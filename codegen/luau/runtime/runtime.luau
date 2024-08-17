local function no_op(num)
	return num
end

local bit_lshift = bit32.lshift
local bit_rshift = bit32.rshift
local bit_arshift = bit32.arshift

local bit_and = bit32.band
local bit_or = bit32.bor
local bit_xor = bit32.bxor
local bit_not = bit32.bnot

local bit_extract = bit32.extract
local bit_replace = bit32.replace

-- X: a[0 __21]
-- Y: a[22__31]
--  | b[0 __11]
-- Z: b[12__31]
local constructor = Vector3.new

local rt_i64_ZERO = constructor(0, 0, 0)

local function rt_i64_from_u32(data_1, data_2)
	local x = bit_and(data_1, 0x3FFFFF)
	local y = bit_and(data_2, 0x3FFFFF)
	local z = bit_replace(bit_rshift(data_1, 22), bit_rshift(data_2, 22), 10, 10)

	return constructor(x, y, z)
end

local function rt_i64_is_zero(value)
	return value == rt_i64_ZERO
end

local function load_d1(value)
	return bit_replace(bit_and(value.X, 0x3FFFFF), value.Z, 22, 10)
end

local function load_d2(value)
	return bit_replace(bit_and(value.Y, 0x3FFFFF), bit_rshift(value.Z, 10), 22, 10)
end

local function rt_i64_into_u32(value)
	local x, y, z = value.X, value.Y, value.Z
	return bit_replace(bit_and(x, 0x3FFFFF), z, 22, 10), bit_replace(bit_and(y, 0x3FFFFF), bit_rshift(z, 10), 22, 10)
end

local function rt_i64_from_u64(value)
	return rt_i64_from_u32(bit_and(value % 0x100000000), bit_and(value / 0x100000000))
end

local function rt_convert_f64_u64(value)
	local value_1, value_2 = rt_i64_into_u32(value)
	return value_1 + value_2 * 0x100000000
end

local rt_i64_ONE = rt_i64_from_u64(1)
local NUM_SIX_FOUR = rt_i64_from_u64(64)
local NUM_BIT_26 = rt_i64_from_u64(0x4000000)
local NUM_BIT_52 = rt_i64_from_u64(0x10000000000000)

local function rt_add_i64(lhs, rhs)
	local lhs_1, lhs_2 = rt_i64_into_u32(lhs)
	local rhs_1, rhs_2 = rt_i64_into_u32(rhs)
	local data_1 = lhs_1 + rhs_1
	local data_2 = lhs_2 + rhs_2

	if data_1 >= 0x100000000 then
		data_1 = data_1 - 0x100000000
		data_2 = data_2 + 1
	end

	if data_2 >= 0x100000000 then
		data_2 = data_2 - 0x100000000
	end

	return rt_i64_from_u32(data_1, data_2)
end

local function rt_sub_i64(lhs, rhs)
	local lhs_1, lhs_2 = rt_i64_into_u32(lhs)
	local rhs_1, rhs_2 = rt_i64_into_u32(rhs)
	local data_1 = lhs_1 - rhs_1
	local data_2 = lhs_2 - rhs_2

	if data_1 < 0 then
		data_1 = data_1 + 0x100000000
		data_2 = data_2 - 1
	end

	if data_2 < 0 then
		data_2 = data_2 + 0x100000000
	end

	return rt_i64_from_u32(data_1, data_2)
end

local function rt_lt_u64(lhs, rhs)
	local data_l_2 = load_d2(lhs)
	local data_r_2 = load_d2(rhs)

	return data_l_2 < data_r_2 or (data_l_2 == data_r_2 and load_d1(lhs) < load_d1(rhs))
end

local function rt_mul_i64(lhs, rhs)
	if rt_i64_is_zero(lhs) or rt_i64_is_zero(rhs) then
		return rt_i64_ZERO
	elseif rt_lt_u64(lhs, NUM_BIT_26) and rt_lt_u64(rhs, NUM_BIT_26) then
		return rt_i64_from_u64(load_d1(lhs) * load_d1(rhs))
	end

	-- Divide each long into 4 chunks of 16 bits, and then add up 4x4 products_
	-- We can skip products that would overflow_
	local lhs_1, lhs_2 = rt_i64_into_u32(lhs)
	local rhs_1, rhs_2 = rt_i64_into_u32(rhs)

	local a48 = bit_rshift(lhs_2, 16)
	local a32 = bit_and(lhs_2, 0xFFFF)
	local a16 = bit_rshift(lhs_1, 16)
	local a00 = bit_and(lhs_1, 0xFFFF)

	local b48 = bit_rshift(rhs_2, 16)
	local b32 = bit_and(rhs_2, 0xFFFF)
	local b16 = bit_rshift(rhs_1, 16)
	local b00 = bit_and(rhs_1, 0xFFFF)

	local c00 = a00 * b00
	local c16 = bit_rshift(c00, 16)

	c00 = bit_and(c00, 0xFFFF)
	c16 = c16 + a16 * b00

	local c32 = bit_rshift(c16, 16)

	c16 = bit_and(c16, 0xFFFF)
	c16 = c16 + a00 * b16
	c32 = c32 + bit_rshift(c16, 16)
	c16 = bit_and(c16, 0xFFFF)
	c32 = c32 + a32 * b00

	local c48 = bit_rshift(c32, 16)

	c32 = bit_and(c32, 0xFFFF)
	c32 = c32 + a16 * b16
	c48 = c48 + bit_rshift(c32, 16)
	c32 = bit_and(c32, 0xFFFF)
	c32 = c32 + a00 * b32
	c48 = c48 + bit_rshift(c32, 16)
	c32 = bit_and(c32, 0xFFFF)
	c48 = c48 + a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48
	c48 = bit_and(c48, 0xFFFF)

	local data_1 = bit_replace(c00, c16, 16, 16)
	local data_2 = bit_replace(c32, c48, 16, 16)

	return rt_i64_from_u32(data_1, data_2)
end

local function rt_bit_or_i64(lhs, rhs)
	local x = bit_or(lhs.X, rhs.X)
	local y = bit_or(lhs.Y, rhs.Y)
	local z = bit_or(lhs.Z, rhs.Z)

	return constructor(x, y, z)
end

local function rt_shl_i64(lhs, rhs)
	local count = rhs.X % 64

	if count == 0 then
		return lhs
	elseif count < 32 then
		local pad = 32 - count
		local lhs_1, lhs_2 = rt_i64_into_u32(lhs)

		local data_1 = bit_lshift(lhs_1, count)
		local data_2 = bit_replace(bit_rshift(lhs_1, pad), lhs_2, count, pad)

		return rt_i64_from_u32(data_1, data_2)
	else
		local lhs_1 = load_d1(lhs)

		return rt_i64_from_u32(0, bit_lshift(lhs_1, count - 32))
	end
end

local function rt_div_u64(lhs, rhs)
	if rt_i64_is_zero(rhs) then
		error("division by zero")
	elseif rt_i64_is_zero(lhs) then
		return rt_i64_ZERO, rt_i64_ZERO
	elseif rt_lt_u64(lhs, NUM_BIT_52) and rt_lt_u64(rhs, NUM_BIT_52) then
		local lhs_u = rt_convert_f64_u64(lhs)
		local rhs_u = rt_convert_f64_u64(rhs)

		return rt_i64_from_u64(lhs_u / rhs_u), rt_i64_from_u64(lhs_u % rhs_u)
	end

	local quotient = rt_i64_ZERO
	local remainder = rt_i64_ZERO

	local num_1, num_2 = rt_i64_into_u32(lhs)

	for i = 63, 0, -1 do
		local rem_1, rem_2 = rt_i64_into_u32(rt_shl_i64(remainder, rt_i64_ONE))

		if i > 31 then
			rem_1 = bit_or(rem_1, bit_extract(num_2, i - 32, 1))
		else
			rem_1 = bit_or(rem_1, bit_extract(num_1, i, 1))
		end

		remainder = rt_i64_from_u32(rem_1, rem_2)

		if not rt_lt_u64(remainder, rhs) then
			remainder = rt_sub_i64(remainder, rhs)
			quotient = rt_bit_or_i64(quotient, rt_shl_i64(rt_i64_ONE, rt_i64_from_u32(i, 0)))
		end
	end

	return quotient, remainder
end

local function rt_i64_is_negative(value)
	return value.Z >= 0x80000
end

local function rt_i64_negate(value)
	local value_1, value_2 = rt_i64_into_u32(value)
	local data_1 = bit_not(value_1) + 1
	local data_2 = bit_not(value_2)

	if data_1 >= 0x100000000 then
		data_1 = data_1 - 0x100000000
		data_2 = data_2 + 1
	end

	if data_2 >= 0x100000000 then
		data_2 = data_2 - 0x100000000
	end

	return rt_i64_from_u32(data_1, data_2)
end

local function rt_div_i64(lhs, rhs)
	local left_negative = rt_i64_is_negative(lhs)
	local right_negative = rt_i64_is_negative(rhs)

	if left_negative then
		lhs = rt_i64_negate(lhs)
	end

	if right_negative then
		rhs = rt_i64_negate(rhs)
	end

	local quotient, remainder = rt_div_u64(lhs, rhs)

	if left_negative ~= right_negative then
		quotient = rt_i64_negate(quotient)
	end

	if left_negative then
		remainder = rt_i64_negate(remainder)
	end

	return quotient, remainder
end

local function rt_bit_and_i64(lhs, rhs)
	local x = bit_and(lhs.X, rhs.X)
	local y = bit_and(lhs.Y, rhs.Y)
	local z = bit_and(lhs.Z, rhs.Z)

	return constructor(x, y, z)
end

local function rt_bit_not_i64(value)
	local x = bit_and(bit_not(value.X), 0xFFFFFF)
	local y = bit_and(bit_not(value.Y), 0xFFFFFF)
	local z = bit_and(bit_not(value.Z), 0xFFFFFF)

	return constructor(x, y, z)
end

local function rt_bit_xor_i64(lhs, rhs)
	local x = bit_xor(lhs.X, rhs.X)
	local y = bit_xor(lhs.Y, rhs.Y)
	local z = bit_xor(lhs.Z, rhs.Z)

	return constructor(x, y, z)
end

local function rt_shr_u64(lhs, rhs)
	local count = rhs.X % 64

	if count == 0 then
		return lhs
	elseif count < 32 then
		local lhs_1, lhs_2 = rt_i64_into_u32(lhs)

		local data_1 = bit_replace(bit_rshift(lhs_1, count), lhs_2, 32 - count, count)
		local data_2 = bit_rshift(lhs_2, count)

		return rt_i64_from_u32(data_1, data_2)
	else
		local lhs_2 = load_d2(lhs)

		return rt_i64_from_u32(bit_rshift(lhs_2, count - 32), 0)
	end
end

local function rt_shr_i64(lhs, rhs)
	local count = rhs.X % 64

	if count == 0 then
		return lhs
	elseif count < 32 then
		local lhs_1, lhs_2 = rt_i64_into_u32(lhs)

		local data_1 = bit_replace(bit_rshift(lhs_1, count), lhs_2, 32 - count, count)
		local data_2 = bit_arshift(lhs_2, count)

		return rt_i64_from_u32(data_1, data_2)
	else
		local lhs_2 = load_d2(lhs)

		local data_1 = bit_arshift(lhs_2, count - 32)
		local data_2 = lhs_2 >= 0x80000000 and 0xFFFFFFFF or 0

		return rt_i64_from_u32(data_1, data_2)
	end
end

local function rt_rotl_i64(lhs, rhs)
	if rt_i64_is_zero(rhs) then
		return lhs
	else
		local data_1 = rt_shl_i64(lhs, rhs)
		local data_2 = rt_shr_u64(lhs, rt_sub_i64(NUM_SIX_FOUR, rhs))

		return rt_bit_or_i64(data_1, data_2)
	end
end

local function rt_rotr_i64(lhs, rhs)
	if rt_i64_is_zero(rhs) then
		return lhs
	else
		local data_1 = rt_shr_u64(lhs, rhs)
		local data_2 = rt_shl_i64(lhs, rt_sub_i64(NUM_SIX_FOUR, rhs))

		return rt_bit_or_i64(data_1, data_2)
	end
end

local function rt_eq_i64(lhs, rhs)
	return lhs == rhs
end

local function rt_gt_u64(lhs, rhs)
	local data_l_2 = load_d2(lhs)
	local data_r_2 = load_d2(rhs)

	return data_l_2 > data_r_2 or (data_l_2 == data_r_2 and load_d1(lhs) > load_d1(rhs))
end

local function rt_lt_i64(lhs, rhs)
	local neg_a = rt_i64_is_negative(lhs)
	local neg_b = rt_i64_is_negative(rhs)

	if neg_a and not neg_b then
		return true
	elseif not neg_a and neg_b then
		return false
	else
		return rt_i64_is_negative(rt_sub_i64(lhs, rhs))
	end
end

local function rt_gt_i64(lhs, rhs)
	local neg_a = rt_i64_is_negative(lhs)
	local neg_b = rt_i64_is_negative(rhs)

	if neg_a and not neg_b then
		return false
	elseif not neg_a and neg_b then
		return true
	else
		return rt_i64_is_negative(rt_sub_i64(rhs, lhs))
	end
end

local function rt_convert_f64_i32(num)
	return bit_xor(num, 0x80000000) - 0x80000000
end

local assert = assert

local math_abs = math.abs
local math_fmod = math.fmod
local math_modf = math.modf
local math_round = math.round
local math_sign = math.sign
local math_min = math.min
local math_max = math.max

local function rt_add_i32(lhs, rhs)
	return bit_or(lhs + rhs, 0)
end

local function rt_sub_i32(lhs, rhs)
	return bit_or(lhs - rhs, 0)
end

local function rt_mul_i32(lhs, rhs)
	if (lhs + rhs) < 0x8000000 then
		return bit_or(lhs * rhs, 0)
	else
		local a16 = bit_rshift(lhs, 16)
		local a00 = bit_and(lhs, 0xFFFF)
		local b16 = bit_rshift(rhs, 16)
		local b00 = bit_and(rhs, 0xFFFF)

		local c00 = a00 * b00
		local c16 = a16 * b00 + a00 * b16

		return bit_or(c00 + bit_lshift(c16, 16), 0)
	end
end

local function rt_div_i32(lhs, rhs)
	assert(rhs ~= 0, "division by zero")

	lhs = rt_convert_f64_i32(lhs)
	rhs = rt_convert_f64_i32(rhs)

	return bit_or(math_modf(lhs / rhs), 0)
end

local function rt_div_u32(lhs, rhs)
	assert(rhs ~= 0, "division by zero")

	return bit_or(math_modf(lhs / rhs), 0)
end

local function rt_rem_i32(lhs, rhs)
	assert(rhs ~= 0, "division by zero")

	lhs = rt_convert_f64_i32(lhs)
	rhs = rt_convert_f64_i32(rhs)

	return bit_or(math_fmod(lhs, rhs), 0)
end

local function rt_rem_i64(lhs, rhs)
	local _, remainder = rt_div_i64(lhs, rhs)

	return remainder
end

local function rt_rem_u64(lhs, rhs)
	local _, remainder = rt_div_u64(lhs, rhs)

	return remainder
end

local function rt_neg_f64(num)
	return -num
end

local function rt_min_f64(lhs, rhs)
	if rhs == rhs then
		return math_min(lhs, rhs)
	else
		return rhs
	end
end

local function rt_max_f64(lhs, rhs)
	if rhs == rhs then
		return math_max(lhs, rhs)
	else
		return rhs
	end
end

local buffer_create = buffer.create

local CP_INSTANCE = buffer_create(8)

local buffer_write_f64 = buffer.writef64
local buffer_read_i8 = buffer.readi8

local function rt_copysign_f64(lhs, rhs)
	buffer_write_f64(CP_INSTANCE, 0, rhs)

	if buffer_read_i8(CP_INSTANCE, 7) >= 0 then
		return (math_abs(lhs))
	else
		return -math_abs(lhs)
	end
end

local function rt_nearest_f32(num)
	local result = math_round(num)

	if (math_abs(num) + 0.5) % 2 == 1 then
		return result - math_sign(result)
	else
		return result
	end
end

local bit_countlz = bit32.countlz
local bit_countrz = bit32.countrz

local function rt_popcnt_i32(num)
	num = num - bit_and(bit_rshift(num, 1), 0x55555555)
	num = bit_and(num, 0x33333333) + bit_and(bit_rshift(num, 2), 0x33333333)
	num = bit_and((num + bit_rshift(num, 4)), 0x0F0F0F0F)
	num = num + bit_rshift(num, 8)
	num = num + bit_rshift(num, 16)
	return bit_and(num, 0x0000003F)
end

local function rt_clz_i64(num)
	local data_1, data_2 = rt_i64_into_u32(num)
	local temp

	if data_2 == 0 then
		temp = bit_countlz(data_1) + 32
	else
		temp = bit_countlz(data_2)
	end

	return rt_i64_from_u32(temp, 0)
end

local function rt_ctz_i64(num)
	local data_1, data_2 = rt_i64_into_u32(num)
	local temp

	if data_1 == 0 then
		temp = bit_countrz(data_2) + 32
	else
		temp = bit_countrz(data_1)
	end

	return rt_i64_from_u32(temp, 0)
end

local function rt_popcnt_i64(num)
	local data_1, data_2 = rt_i64_into_u32(num)
	local temp = rt_popcnt_i32(data_1) + rt_popcnt_i32(data_2)

	return rt_i64_from_u32(temp, 0)
end

local function rt_le_i32(lhs, rhs)
	return rt_convert_f64_i32(lhs) <= rt_convert_f64_i32(rhs)
end

local function rt_lt_i32(lhs, rhs)
	return rt_convert_f64_i32(lhs) < rt_convert_f64_i32(rhs)
end

local function rt_ge_i32(lhs, rhs)
	return rt_convert_f64_i32(lhs) >= rt_convert_f64_i32(rhs)
end

local function rt_gt_i32(lhs, rhs)
	return rt_convert_f64_i32(lhs) > rt_convert_f64_i32(rhs)
end

local function rt_ne_i64(lhs, rhs)
	return not rt_eq_i64(lhs, rhs)
end

local function rt_le_i64(lhs, rhs)
	return rt_lt_i64(lhs, rhs) or rt_eq_i64(lhs, rhs)
end

local function rt_le_u64(lhs, rhs)
	return rt_lt_u64(lhs, rhs) or rt_eq_i64(lhs, rhs)
end

local function rt_ge_i64(lhs, rhs)
	return rt_gt_i64(lhs, rhs) or rt_eq_i64(lhs, rhs)
end

local function rt_ge_u64(lhs, rhs)
	return rt_gt_u64(lhs, rhs) or rt_eq_i64(lhs, rhs)
end

local bit_lrotate = bit32.lrotate
local bit_rrotate = bit32.rrotate

local function rt_shl_i32(lhs, rhs)
	return bit_lshift(lhs, rhs % 32)
end

local function rt_shr_u32(lhs, rhs)
	return bit_rshift(lhs, rhs % 32)
end

local function rt_shr_i32(lhs, rhs)
	return bit_arshift(lhs, rhs % 32)
end

local function rt_rotl_i32(lhs, rhs)
	return bit_lrotate(lhs, rhs % 32)
end

local function rt_rotr_i32(lhs, rhs)
	return bit_rrotate(lhs, rhs % 32)
end

local math_ceil = math.ceil
local math_floor = math.floor
local math_clamp = math.clamp

local NUM_MIN_I64 = rt_i64_from_u32(0, 0x80000000)
local NUM_MAX_I64 = rt_i64_from_u32(0xFFFFFFFF, 0x7FFFFFFF)
local NUM_MAX_U64 = rt_i64_from_u32(0xFFFFFFFF, 0xFFFFFFFF)

local function rt_truncate_f64(num)
	if num >= 0 then
		return math_floor(num)
	else
		return math_ceil(num)
	end
end

local function rt_wrap_i32_i64(num)
	local data_1, _ = rt_i64_into_u32(num)

	return data_1
end

local function rt_truncate_i32_f64(num)
	return bit_or(rt_truncate_f64(num), 0)
end

local function rt_truncate_i64_f64(num)
	if num < 0 then
		local temp = rt_i64_from_u64(-num)

		return rt_i64_negate(temp)
	else
		return rt_i64_from_u64(num)
	end
end

local function rt_truncate_u64_f64(num)
	if num <= 0 then
		return rt_i64_ZERO
	else
		return rt_i64_from_u64(math_floor(num))
	end
end

local function rt_saturate_i32_f64(num)
	local temp = math_clamp(rt_truncate_f64(num), -0x80000000, 0x7FFFFFFF)

	return bit_or(temp, 0)
end

local function rt_saturate_u32_f64(num)
	return math_clamp(rt_truncate_f64(num), 0, 0xFFFFFFFF)
end

local function rt_saturate_i64_f64(num)
	if num >= 2 ^ 63 - 1 then
		return NUM_MAX_I64
	elseif num <= -2 ^ 63 then
		return NUM_MIN_I64
	else
		return rt_truncate_i64_f64(num)
	end
end

local function rt_saturate_u64_f64(num)
	if num >= 2 ^ 64 then
		return NUM_MAX_U64
	elseif num <= 0 then
		return rt_i64_ZERO
	else
		return rt_truncate_i64_f64(num)
	end
end

local function rt_extend_i32_n8(num)
	num = bit_and(num, 0xFF)

	if num >= 0x80 then
		return bit_or(num - 0x100, 0)
	else
		return num
	end
end

local function rt_extend_i32_n16(num)
	num = bit_and(num, 0xFFFF)

	if num >= 0x8000 then
		return bit_or(num - 0x10000, 0)
	else
		return num
	end
end

local function rt_extend_i64_n8(num)
	local data_1, _ = rt_i64_into_u32(num)

	data_1 = bit_and(data_1, 0xFF)

	if data_1 >= 0x80 then
		local temp = rt_i64_from_u32(-data_1 + 0x100, 0)

		return rt_i64_negate(temp)
	else
		return rt_i64_from_u32(data_1, 0)
	end
end

local function rt_extend_i64_n16(num)
	local data_1, _ = rt_i64_into_u32(num)

	data_1 = bit_and(data_1, 0xFFFF)

	if data_1 >= 0x8000 then
		local temp = rt_i64_from_u32(-data_1 + 0x10000, 0)

		return rt_i64_negate(temp)
	else
		return rt_i64_from_u32(data_1, 0)
	end
end

local function rt_extend_i64_n32(num)
	local data_1, _ = rt_i64_into_u32(num)

	if data_1 >= 0x80000000 then
		local temp = rt_i64_from_u32(-data_1 + 0x100000000, 0)

		return rt_i64_negate(temp)
	else
		return rt_i64_from_u32(data_1, 0)
	end
end

local function rt_extend_i64_i32(num)
	if num >= 0x80000000 then
		local temp = rt_i64_from_u32(-num + 0x100000000, 0)

		return rt_i64_negate(temp)
	else
		return rt_i64_from_u32(num, 0)
	end
end

local function rt_extend_i64_u32(num)
	return rt_i64_from_u32(num, 0)
end

local function rt_convert_f64_i64(num)
	if rt_i64_is_negative(num) then
		local temp = rt_i64_negate(num)

		return -rt_convert_f64_u64(temp)
	else
		return rt_convert_f64_u64(num)
	end
end

local RE_INSTANCE = buffer_create(8)

local buffer_read_f32 = buffer.readf32
local buffer_read_f64 = buffer.readf64
local buffer_read_u32 = buffer.readu32

local buffer_write_f32 = buffer.writef32
local buffer_write_u32 = buffer.writeu32

local function rt_reinterpret_i32_f32(num)
	buffer_write_f32(RE_INSTANCE, 0, num)

	return buffer_read_u32(RE_INSTANCE, 0)
end

local function rt_reinterpret_i64_f64(num)
	buffer_write_f64(RE_INSTANCE, 0, num)

	local data_1 = buffer_read_u32(RE_INSTANCE, 0)
	local data_2 = buffer_read_u32(RE_INSTANCE, 4)

	return rt_i64_from_u32(data_1, data_2)
end

local function rt_reinterpret_f32_i32(num)
	buffer_write_u32(RE_INSTANCE, 0, num)

	return buffer_read_f32(RE_INSTANCE, 0)
end

local function rt_reinterpret_f64_i64(num)
	local data_1, data_2 = rt_i64_into_u32(num)

	buffer_write_u32(RE_INSTANCE, 0, data_1)
	buffer_write_u32(RE_INSTANCE, 4, data_2)

	return buffer_read_f64(RE_INSTANCE, 0)
end

local string_sub = string.sub

local buffer_to_string = buffer.tostring
local buffer_from_string = buffer.fromstring

local buffer_len = buffer.len
local buffer_copy = buffer.copy
local buffer_fill = buffer.fill

local buffer_read_u8 = buffer.readu8
local buffer_read_i16 = buffer.readi16
local buffer_read_u16 = buffer.readu16
local buffer_read_i32 = buffer.readi32

local buffer_write_u8 = buffer.writeu8
local buffer_write_u16 = buffer.writeu16

local function rt_load_i32_i8(memory, addr)
	return bit_or(buffer_read_i8(memory.data, addr), 0)
end

local function rt_load_i32_u8(memory, addr)
	return buffer_read_u8(memory.data, addr)
end

local function rt_load_i32_i16(memory, addr)
	return bit_or(buffer_read_i16(memory.data, addr), 0)
end

local function rt_load_i32_u16(memory, addr)
	return buffer_read_u16(memory.data, addr)
end

local function rt_load_i32(memory, addr)
	return buffer_read_u32(memory.data, addr)
end

local function rt_load_i64_i8(memory, addr)
	local value = buffer_read_i8(memory.data, addr)

	if value >= 0 then
		return rt_i64_from_u32(value, 0)
	else
		return rt_i64_from_u32(value + 0x100000000, 0xFFFFFFFF)
	end
end

local function rt_load_i64_u8(memory, addr)
	return rt_i64_from_u32(buffer_read_u8(memory.data, addr), 0)
end

local function rt_load_i64_i16(memory, addr)
	local value = buffer_read_i16(memory.data, addr)

	if value >= 0 then
		return rt_i64_from_u32(value, 0)
	else
		return rt_i64_from_u32(value + 0x100000000, 0xFFFFFFFF)
	end
end

local function rt_load_i64_u16(memory, addr)
	return rt_i64_from_u32(buffer_read_u16(memory.data, addr), 0)
end

local function rt_load_i64_i32(memory, addr)
	local value = buffer_read_i32(memory.data, addr)

	if value >= 0 then
		return rt_i64_from_u32(value, 0)
	else
		return rt_i64_from_u32(value + 0x100000000, 0xFFFFFFFF)
	end
end

local function rt_load_i64_u32(memory, addr)
	return rt_i64_from_u32(buffer_read_u32(memory.data, addr), 0)
end

local function rt_load_i64(memory, addr)
	local data = memory.data
	local value_1 = buffer_read_u32(data, addr)
	local value_2 = buffer_read_u32(data, addr + 4)

	return rt_i64_from_u32(value_1, value_2)
end

local function rt_load_f32(memory, addr)
	return buffer_read_f32(memory.data, addr)
end

local function rt_load_f64(memory, addr)
	return buffer_read_f64(memory.data, addr)
end

local function rt_load_string(memory, addr, len)
	local temp = buffer_create(len)

	buffer_copy(temp, 0, memory.data, addr, len)

	return buffer_to_string(temp)
end

local function rt_store_i32_n8(memory, addr, value)
	buffer_write_u8(memory.data, addr, value)
end

local function rt_store_i32_n16(memory, addr, value)
	buffer_write_u16(memory.data, addr, value)
end

local function rt_store_i32(memory, addr, value)
	buffer_write_u32(memory.data, addr, value)
end

local function rt_store_i64_n8(memory, addr, value)
	local value_1, _ = rt_i64_into_u32(value)

	buffer_write_u8(memory.data, addr, value_1)
end

local function rt_store_i64_n16(memory, addr, value)
	local value_1, _ = rt_i64_into_u32(value)

	buffer_write_u16(memory.data, addr, value_1)
end

local function rt_store_i64_n32(memory, addr, value)
	local value_1, _ = rt_i64_into_u32(value)

	buffer_write_u32(memory.data, addr, value_1)
end

local function rt_store_i64(memory, addr, value)
	local data = memory.data
	local value_1, value_2 = rt_i64_into_u32(value)

	buffer_write_u32(data, addr, value_1)
	buffer_write_u32(data, addr + 4, value_2)
end

local function rt_store_f32(memory, addr, value)
	buffer_write_f32(memory.data, addr, value)
end

local function rt_store_f64(memory, addr, value)
	buffer_write_f64(memory.data, addr, value)
end

local function rt_store_string(memory, addr, data, len)
	local content = if not len or len == #data then data else string_sub(data, 1, len)
	local temp = buffer_from_string(content)

	buffer_copy(memory.data, addr, temp)
end

local function rt_store_copy(memory_1, addr_1, memory_2, addr_2, len)
	buffer_copy(memory_1.data, addr_1, memory_2.data, addr_2, len)
end

local function rt_store_fill(memory, addr, len, value)
	buffer_fill(memory.data, addr, value, len)
end

local WASM_PAGE_SIZE = 65536

local function rt_allocator_new(min, max)
	return { max = max, data = buffer_create(min * WASM_PAGE_SIZE) }
end

local function rt_allocator_size(memory)
	return buffer_len(memory.data) / WASM_PAGE_SIZE
end

local function rt_allocator_grow(memory, num)
	local old = rt_allocator_size(memory)
	local new = old + num

	if new <= memory.max then
		local reallocated = buffer_create(new * WASM_PAGE_SIZE)

		buffer_copy(reallocated, 0, memory.data)

		memory.data = reallocated

		return old
	else
		return 0xFFFFFFFF
	end
end
