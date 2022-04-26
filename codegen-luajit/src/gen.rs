use std::{collections::BTreeSet, io::Result, ops::Range};

use parity_wasm::elements::{
	External, ImportCountType, Instruction, Internal, Module, NameSection, ResizableLimits,
};

use wasm_ast::{
	builder::{Builder, TypeInfo},
	node::{
		AnyBinOp, AnyCmpOp, AnyLoad, AnyStore, AnyUnOp, Backward, Br, BrIf, BrTable, Call,
		CallIndirect, Else, Expression, Forward, Function, GetGlobal, GetLocal, If, Memorize,
		MemoryGrow, MemorySize, Recall, Return, Select, SetGlobal, SetLocal, Statement, Value,
	},
	writer::{Transpiler, Writer},
};

use crate::analyzer::{localize, memory};

fn aux_internal_index(internal: Internal) -> u32 {
	match internal {
		Internal::Function(v) | Internal::Table(v) | Internal::Memory(v) | Internal::Global(v) => v,
	}
}

fn new_limit_max(limits: &ResizableLimits) -> String {
	match limits.maximum() {
		Some(v) => v.to_string(),
		None => "0xFFFF".to_string(),
	}
}

fn write_separated<I, T, M>(mut iter: I, mut func: M, w: Writer) -> Result<()>
where
	M: FnMut(T, Writer) -> Result<()>,
	I: Iterator<Item = T>,
{
	match iter.next() {
		Some(first) => func(first, w)?,
		None => return Ok(()),
	}

	iter.try_for_each(|v| {
		write!(w, ", ")?;
		func(v, w)
	})
}

fn write_table_init(limit: &ResizableLimits, w: Writer) -> Result<()> {
	let a = limit.initial();
	let b = new_limit_max(limit);

	write!(w, "{{ min = {a}, max = {b}, data = {{}} }}")
}

fn write_memory_init(limit: &ResizableLimits, w: Writer) -> Result<()> {
	let a = limit.initial();
	let b = new_limit_max(limit);

	write!(w, "rt.allocator.new({a}, {b})")
}

fn write_func_start(wasm: &Module, index: u32, offset: u32, w: Writer) -> Result<()> {
	let opt = wasm
		.names_section()
		.and_then(NameSection::functions)
		.and_then(|v| v.names().get(index));

	write!(w, "FUNC_LIST")?;

	if let Some(name) = opt {
		write!(w, "--[[{name}]]")?;
	}

	write!(w, "[{}] =", index + offset)
}

fn write_ascending(prefix: &str, range: Range<usize>, w: Writer) -> Result<()> {
	write_separated(range, |i, w| write!(w, "{prefix}_{i}"), w)
}

fn write_f32(number: f32, w: Writer) -> Result<()> {
	let sign = if number.is_sign_negative() { "-" } else { "" };

	if number.is_infinite() {
		write!(w, "{sign}math.huge ")
	} else if number.is_nan() {
		write!(w, "{sign}0/0 ")
	} else {
		write!(w, "{number:e} ")
	}
}

fn write_f64(number: f64, w: Writer) -> Result<()> {
	let sign = if number.is_sign_negative() { "-" } else { "" };

	if number.is_infinite() {
		write!(w, "{sign}math.huge ")
	} else if number.is_nan() {
		write!(w, "{sign}0/0 ")
	} else {
		write!(w, "{number:e} ")
	}
}

fn write_named_array(name: &str, len: usize, w: Writer) -> Result<()> {
	let hash = len.min(1);
	let len = len.saturating_sub(1);

	write!(w, "local {name} = table_new({len}, {hash})")
}

fn write_parameter_list(func: &Function, w: Writer) -> Result<()> {
	write!(w, "function(")?;
	write_ascending("param", 0..func.num_param, w)?;
	write!(w, ")")
}

fn write_call_store(result: Range<usize>, w: Writer) -> Result<()> {
	if result.is_empty() {
		return Ok(());
	}

	write_ascending("reg", result, w)?;
	write!(w, " = ")
}

fn write_variable_list(func: &Function, w: Writer) -> Result<()> {
	let mut total = 0;

	for data in &func.local_data {
		let range = total..total + usize::try_from(data.count()).unwrap();
		let typed = data.value_type();

		total = range.end;

		write!(w, "local ")?;
		write_ascending("loc", range.clone(), w)?;
		write!(w, " = ")?;
		write_separated(range, |_, w| write!(w, "ZERO_{typed} "), w)?;
	}

	if func.num_stack != 0 {
		write!(w, "local ")?;
		write_ascending("reg", 0..func.num_stack, w)?;
		write!(w, " ")?;
	}

	Ok(())
}

fn write_constant(code: &[Instruction], w: Writer) -> Result<()> {
	// FIXME: Badly generated WASM will produce the wrong constant.
	for inst in code {
		let result = match *inst {
			Instruction::I32Const(v) => write!(w, "{v} "),
			Instruction::I64Const(v) => write!(w, "{v}LL "),
			Instruction::F32Const(v) => write_f32(f32::from_bits(v), w),
			Instruction::F64Const(v) => write_f64(f64::from_bits(v), w),
			Instruction::GetGlobal(i) => write!(w, "GLOBAL_LIST[{i}].value "),
			_ => {
				continue;
			}
		};

		return result;
	}

	write!(w, "error(\"mundane expression\")")
}

fn condense_jump_table(list: &[u32]) -> Vec<(usize, usize, u32)> {
	let mut result = Vec::new();
	let mut index = 0;

	while index < list.len() {
		let start = index;

		loop {
			index += 1;

			// if end of list or next value is not equal, break
			if index == list.len() || list[index - 1] != list[index] {
				break;
			}
		}

		result.push((start, index - 1, list[start]));
	}

	result
}

#[derive(Default)]
struct Visitor {
	label_list: Vec<usize>,
	num_label: usize,
	num_param: usize,
}

impl Visitor {
	fn push_label(&mut self) -> usize {
		self.label_list.push(self.num_label);
		self.num_label += 1;

		self.num_label - 1
	}

	fn pop_label(&mut self) {
		self.label_list.pop().unwrap();
	}
}

trait Driver {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()>;
}

impl Driver for Recall {
	fn visit(&self, _: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "reg_{} ", self.var)
	}
}

impl Driver for Select {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "(")?;
		write_as_condition(&self.cond, v, w)?;
		write!(w, "and ")?;
		self.a.visit(v, w)?;
		write!(w, "or ")?;
		self.b.visit(v, w)?;
		write!(w, ")")
	}
}

fn write_variable(var: usize, v: &Visitor, w: Writer) -> Result<()> {
	if let Some(rem) = var.checked_sub(v.num_param) {
		write!(w, "loc_{rem} ")
	} else {
		write!(w, "param_{var} ")
	}
}

impl Driver for GetLocal {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write_variable(self.var, v, w)
	}
}

impl Driver for GetGlobal {
	fn visit(&self, _: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "GLOBAL_LIST[{}].value ", self.var)
	}
}

impl Driver for AnyLoad {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "load_{}(memory_at_0, ", self.op.as_name())?;
		self.pointer.visit(v, w)?;
		write!(w, "+ {})", self.offset)
	}
}

impl Driver for MemorySize {
	fn visit(&self, _: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "memory_at_{}.min ", self.memory)
	}
}

impl Driver for MemoryGrow {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "rt.allocator.grow(memory_at_{}, ", self.memory)?;
		self.value.visit(v, w)?;
		write!(w, ")")
	}
}

impl Driver for Value {
	fn visit(&self, _: &mut Visitor, w: Writer) -> Result<()> {
		match self {
			Self::I32(i) => write!(w, "{i} "),
			Self::I64(i) => write!(w, "{i}LL "),
			Self::F32(f) => write_f32(*f, w),
			Self::F64(f) => write_f64(*f, w),
		}
	}
}

impl Driver for AnyUnOp {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		let (a, b) = self.op.as_name();

		write!(w, "{a}_{b}(")?;
		self.rhs.visit(v, w)?;
		write!(w, ")")
	}
}

fn write_bin_call(
	op: (&str, &str),
	lhs: &Expression,
	rhs: &Expression,
	v: &mut Visitor,
	w: Writer,
) -> Result<()> {
	write!(w, "{}_{}(", op.0, op.1)?;
	lhs.visit(v, w)?;
	write!(w, ", ")?;
	rhs.visit(v, w)?;
	write!(w, ")")
}

impl Driver for AnyBinOp {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		if let Some(op) = self.op.as_operator() {
			write!(w, "(")?;
			self.lhs.visit(v, w)?;
			write!(w, "{op} ")?;
			self.rhs.visit(v, w)?;
			write!(w, ")")
		} else {
			write_bin_call(self.op.as_name(), &self.lhs, &self.rhs, v, w)
		}
	}
}

fn write_any_cmp(cmp: &AnyCmpOp, v: &mut Visitor, w: Writer) -> Result<()> {
	if let Some(op) = cmp.op.as_operator() {
		cmp.lhs.visit(v, w)?;
		write!(w, "{op} ")?;
		cmp.rhs.visit(v, w)
	} else {
		write_bin_call(cmp.op.as_name(), &cmp.lhs, &cmp.rhs, v, w)
	}
}

impl Driver for AnyCmpOp {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "(")?;
		write_any_cmp(self, v, w)?;
		write!(w, "and 1 or 0)")
	}
}

// Removes the boolean to integer conversion
fn write_as_condition(data: &Expression, v: &mut Visitor, w: Writer) -> Result<()> {
	if let Expression::AnyCmpOp(o) = data {
		write_any_cmp(o, v, w)
	} else {
		data.visit(v, w)?;
		write!(w, "~= 0 ")
	}
}

fn write_expr_list(list: &[Expression], v: &mut Visitor, w: Writer) -> Result<()> {
	write_separated(list.iter(), |e, w| e.visit(v, w), w)
}

impl Driver for Expression {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		match self {
			Self::Recall(e) => e.visit(v, w),
			Self::Select(e) => e.visit(v, w),
			Self::GetLocal(e) => e.visit(v, w),
			Self::GetGlobal(e) => e.visit(v, w),
			Self::AnyLoad(e) => e.visit(v, w),
			Self::MemorySize(e) => e.visit(v, w),
			Self::MemoryGrow(e) => e.visit(v, w),
			Self::Value(e) => e.visit(v, w),
			Self::AnyUnOp(e) => e.visit(v, w),
			Self::AnyBinOp(e) => e.visit(v, w),
			Self::AnyCmpOp(e) => e.visit(v, w),
		}
	}
}

impl Driver for Memorize {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "reg_{} = ", self.var)?;
		self.value.visit(v, w)
	}
}

impl Driver for Forward {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		let label = v.push_label();

		self.body.iter().try_for_each(|s| s.visit(v, w))?;

		write!(w, "::continue_at_{label}::")?;

		v.pop_label();

		Ok(())
	}
}

impl Driver for Backward {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		let label = v.push_label();

		write!(w, "::continue_at_{label}::")?;
		write!(w, "while true do ")?;

		self.body.iter().try_for_each(|s| s.visit(v, w))?;

		write!(w, "break ")?;
		write!(w, "end ")?;

		v.pop_label();

		Ok(())
	}
}

impl Driver for Else {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "else ")?;

		self.body.iter().try_for_each(|s| s.visit(v, w))
	}
}

impl Driver for If {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		let label = v.push_label();

		write!(w, "if ")?;
		write_as_condition(&self.cond, v, w)?;
		write!(w, "then ")?;

		self.truthy.iter().try_for_each(|s| s.visit(v, w))?;

		if let Some(s) = &self.falsey {
			s.visit(v, w)?;
		}

		write!(w, "::continue_at_{label}::")?;
		write!(w, "end ")?;

		v.pop_label();

		Ok(())
	}
}

fn write_br_at(up: usize, v: &Visitor, w: Writer) -> Result<()> {
	let level = v.label_list.iter().nth_back(up).unwrap();

	write!(w, "goto continue_at_{level} ")
}

impl Driver for Br {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write_br_at(self.target, v, w)
	}
}

impl Driver for BrIf {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "if ")?;
		write_as_condition(&self.cond, v, w)?;
		write!(w, "then ")?;

		write_br_at(self.target, v, w)?;

		write!(w, "end ")
	}
}

impl Driver for BrTable {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "temp = ")?;
		self.cond.visit(v, w)?;
		write!(w, " ")?;

		for (start, end, dest) in condense_jump_table(&self.data.table) {
			if start == end {
				write!(w, "if temp == {start} then ")?;
			} else {
				write!(w, "if temp >= {start} and temp <= {end} then ")?;
			}

			write_br_at(dest.try_into().unwrap(), v, w)?;
			write!(w, "else")?;
		}

		write!(w, " ")?;
		write_br_at(self.data.default.try_into().unwrap(), v, w)?;
		write!(w, "end ")
	}
}

impl Driver for Return {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "do return ")?;

		write_expr_list(&self.list, v, w)?;

		write!(w, "end ")
	}
}

impl Driver for Call {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write_call_store(self.result.clone(), w)?;

		write!(w, "FUNC_LIST[{}](", self.func)?;

		write_expr_list(&self.param_list, v, w)?;

		write!(w, ")")
	}
}

impl Driver for CallIndirect {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write_call_store(self.result.clone(), w)?;

		write!(w, "TABLE_LIST[{}].data[", self.table)?;

		self.index.visit(v, w)?;

		write!(w, "](")?;

		write_expr_list(&self.param_list, v, w)?;

		write!(w, ")")
	}
}

impl Driver for SetLocal {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write_variable(self.var, v, w)?;

		write!(w, "= ")?;
		self.value.visit(v, w)
	}
}

impl Driver for SetGlobal {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "GLOBAL_LIST[{}].value = ", self.var)?;
		self.value.visit(v, w)
	}
}

impl Driver for AnyStore {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write!(w, "store_{}(memory_at_0, ", self.op.as_name())?;
		self.pointer.visit(v, w)?;
		write!(w, "+ {}, ", self.offset)?;
		self.value.visit(v, w)?;
		write!(w, ")")
	}
}

impl Driver for Statement {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		match self {
			Self::Unreachable => write!(w, "error(\"out of code bounds\")"),
			Self::Memorize(s) => s.visit(v, w),
			Self::Forward(s) => s.visit(v, w),
			Self::Backward(s) => s.visit(v, w),
			Self::If(s) => s.visit(v, w),
			Self::Br(s) => s.visit(v, w),
			Self::BrIf(s) => s.visit(v, w),
			Self::BrTable(s) => s.visit(v, w),
			Self::Return(s) => s.visit(v, w),
			Self::Call(s) => s.visit(v, w),
			Self::CallIndirect(s) => s.visit(v, w),
			Self::SetLocal(s) => s.visit(v, w),
			Self::SetGlobal(s) => s.visit(v, w),
			Self::AnyStore(s) => s.visit(v, w),
		}
	}
}

impl Driver for Function {
	fn visit(&self, v: &mut Visitor, w: Writer) -> Result<()> {
		write_parameter_list(self, w)?;

		for v in memory::visit(self) {
			write!(w, "local memory_at_{v} = MEMORY_LIST[{v}]")?;
		}

		write_variable_list(self, w)?;
		write!(w, "local temp ")?;

		v.num_param = self.num_param;
		self.code.visit(v, w)?;

		write!(w, "end ")
	}
}

pub struct Generator<'a> {
	wasm: &'a Module,
	type_info: TypeInfo<'a>,
}

static RUNTIME: &str = include_str!("../runtime/runtime.lua");

impl<'a> Transpiler<'a> for Generator<'a> {
	fn new(wasm: &'a Module) -> Self {
		let type_info = TypeInfo::from_module(wasm);

		Self { wasm, type_info }
	}

	fn runtime(w: Writer) -> Result<()> {
		write!(w, "{RUNTIME}")
	}

	fn transpile(&self, w: Writer) -> Result<()> {
		write!(w, "local rt = require(\"luajit\")")?;

		let func_list = self.build_func_list();

		Self::gen_localize(&func_list, w)?;

		write!(w, "local ZERO_i32 = 0 ")?;
		write!(w, "local ZERO_i64 = 0LL ")?;
		write!(w, "local ZERO_f32 = 0.0 ")?;
		write!(w, "local ZERO_f64 = 0.0 ")?;

		write!(w, "local table_new = require(\"table.new\")")?;
		write_named_array("FUNC_LIST", self.wasm.functions_space(), w)?;
		write_named_array("TABLE_LIST", self.wasm.table_space(), w)?;
		write_named_array("MEMORY_LIST", self.wasm.memory_space(), w)?;
		write_named_array("GLOBAL_LIST", self.wasm.globals_space(), w)?;

		self.gen_func_list(&func_list, w)?;
		self.gen_start_point(w)
	}
}

impl<'a> Generator<'a> {
	fn gen_import_of<T>(&self, w: Writer, lower: &str, cond: T) -> Result<()>
	where
		T: Fn(&External) -> bool,
	{
		let import = match self.wasm.import_section() {
			Some(v) => v.entries(),
			None => return Ok(()),
		};
		let upper = lower.to_uppercase();

		for (i, v) in import.iter().filter(|v| cond(v.external())).enumerate() {
			let field = v.field();
			let module = v.module();

			write!(w, "{upper}[{i}] = wasm.{module}.{lower}.{field} ")?;
		}

		Ok(())
	}

	fn gen_export_of<T>(&self, w: Writer, lower: &str, cond: T) -> Result<()>
	where
		T: Fn(&Internal) -> bool,
	{
		let export = match self.wasm.export_section() {
			Some(v) => v.entries(),
			None => return Ok(()),
		};
		let upper = lower.to_uppercase();

		write!(w, "{lower} = {{")?;

		for v in export.iter().filter(|v| cond(v.internal())) {
			let field = v.field();
			let index = aux_internal_index(*v.internal());

			write!(w, "{field} = {upper}[{index}],")?;
		}

		write!(w, "}},")
	}

	fn gen_import_list(&self, w: Writer) -> Result<()> {
		self.gen_import_of(w, "func_list", |v| matches!(v, External::Function(_)))?;
		self.gen_import_of(w, "table_list", |v| matches!(v, External::Table(_)))?;
		self.gen_import_of(w, "memory_list", |v| matches!(v, External::Memory(_)))?;
		self.gen_import_of(w, "global_list", |v| matches!(v, External::Global(_)))
	}

	fn gen_export_list(&self, w: Writer) -> Result<()> {
		self.gen_export_of(w, "func_list", |v| matches!(v, Internal::Function(_)))?;
		self.gen_export_of(w, "table_list", |v| matches!(v, Internal::Table(_)))?;
		self.gen_export_of(w, "memory_list", |v| matches!(v, Internal::Memory(_)))?;
		self.gen_export_of(w, "global_list", |v| matches!(v, Internal::Global(_)))
	}

	fn gen_table_list(&self, w: Writer) -> Result<()> {
		let table = match self.wasm.table_section() {
			Some(v) => v.entries(),
			None => return Ok(()),
		};
		let offset = self.wasm.import_count(ImportCountType::Table);

		for (i, v) in table.iter().enumerate() {
			write!(w, "TABLE_LIST[{}] =", i + offset)?;
			write_table_init(v.limits(), w)?;
		}

		Ok(())
	}

	fn gen_memory_list(&self, w: Writer) -> Result<()> {
		let memory = match self.wasm.memory_section() {
			Some(v) => v.entries(),
			None => return Ok(()),
		};
		let offset = self.wasm.import_count(ImportCountType::Memory);

		for (i, v) in memory.iter().enumerate() {
			write!(w, "MEMORY_LIST[{}] =", i + offset)?;
			write_memory_init(v.limits(), w)?;
		}

		Ok(())
	}

	fn gen_global_list(&self, w: Writer) -> Result<()> {
		let global = match self.wasm.global_section() {
			Some(v) => v,
			None => return Ok(()),
		};
		let offset = self.wasm.import_count(ImportCountType::Global);

		for (i, v) in global.entries().iter().enumerate() {
			write!(w, "GLOBAL_LIST[{}] = {{ value =", i + offset)?;
			write_constant(v.init_expr().code(), w)?;
			write!(w, "}}")?;
		}

		Ok(())
	}

	fn gen_element_list(&self, w: Writer) -> Result<()> {
		let element = match self.wasm.elements_section() {
			Some(v) => v.entries(),
			None => return Ok(()),
		};

		for v in element {
			write!(w, "do ")?;
			write!(w, "local target = TABLE_LIST[{}].data ", v.index())?;
			write!(w, "local offset =")?;

			write_constant(v.offset().as_ref().unwrap().code(), w)?;

			write!(w, "local data = {{")?;

			v.members()
				.iter()
				.try_for_each(|v| write!(w, "FUNC_LIST[{v}],"))?;

			write!(w, "}}")?;

			write!(w, "table.move(data, 1, #data, offset, target)")?;

			write!(w, "end ")?;
		}

		Ok(())
	}

	fn gen_data_list(&self, w: Writer) -> Result<()> {
		let data = match self.wasm.data_section() {
			Some(v) => v.entries(),
			None => return Ok(()),
		};

		for v in data {
			write!(w, "do ")?;
			write!(w, "local target = MEMORY_LIST[{}]", v.index())?;
			write!(w, "local offset =")?;

			write_constant(v.offset().as_ref().unwrap().code(), w)?;

			write!(w, "local data = \"")?;

			v.value().iter().try_for_each(|v| write!(w, "\\x{v:02X}"))?;

			write!(w, "\"")?;

			write!(w, "rt.allocator.init(target, offset, data)")?;

			write!(w, "end ")?;
		}

		Ok(())
	}

	fn gen_start_point(&self, w: Writer) -> Result<()> {
		write!(w, "local function run_init_code()")?;
		self.gen_table_list(w)?;
		self.gen_memory_list(w)?;
		self.gen_global_list(w)?;
		self.gen_element_list(w)?;
		self.gen_data_list(w)?;
		write!(w, "end ")?;

		write!(w, "return function(wasm)")?;
		self.gen_import_list(w)?;
		write!(w, "run_init_code()")?;

		if let Some(start) = self.wasm.start_section() {
			write!(w, "FUNC_LIST[{start}]()")?;
		}

		write!(w, "return {{")?;
		self.gen_export_list(w)?;
		write!(w, "}} end ")
	}

	fn gen_localize(func_list: &[Function], w: Writer) -> Result<()> {
		let mut loc_set = BTreeSet::new();

		for func in func_list {
			loc_set.extend(localize::visit(func));
		}

		loc_set
			.into_iter()
			.try_for_each(|(a, b)| write!(w, "local {a}_{b} = rt.{a}.{b} "))
	}

	// FIXME: Make `pub` only for fuzzing.
	#[must_use]
	pub fn build_func_list(&self) -> Vec<Function> {
		let list = self.wasm.code_section().unwrap().bodies();
		let iter = list.iter().enumerate();

		iter.map(|f| Builder::new(&self.type_info).consume(f.0, f.1))
			.collect()
	}

	/// # Errors
	/// Returns `Err` if writing to `Writer` failed.
	///
	/// # Panics
	/// If the number of functions overflows 32 bits.
	pub fn gen_func_list(&self, func_list: &[Function], w: Writer) -> Result<()> {
		let offset = self.type_info.len_ex().try_into().unwrap();

		func_list.iter().enumerate().try_for_each(|(i, v)| {
			write_func_start(self.wasm, i.try_into().unwrap(), offset, w)?;

			v.visit(&mut Visitor::default(), w)
		})
	}
}
