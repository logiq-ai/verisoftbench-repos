import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Utils.Field
import Clean.Gadgets.Boolean

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.Addition32.Theorems

lemma lift_val1 {x y b : (F p)} (x_byte : x.val < 256) (y_byte : y.val < 256) (b_bool : IsBool b) :
    (x + y + b).val = (x.val + y.val + b.val) := by
  have b_lt_2 := IsBool.val_lt_two b_bool
  field_to_nat

lemma lift_val2 {x b : (F p)} (x_byte : x.val < 256) (b_bool : IsBool b) :
    (b * 256 + x).val = (b.val * 256 + x.val) := by
  have b_lt_2 := IsBool.val_lt_two b_bool
  field_to_nat

omit p_large_enough in
lemma zify_bool {b : (F p)} (b_bool : IsBool b) : (↑(b.val) : ℤ) = 0 ∨ (↑(b.val) : ℤ) = 1  := by
  rcases b_bool with b_zero | b_one
  · rw [b_zero]
    simp only [ZMod.val_zero, CharP.cast_eq_zero, zero_ne_one, or_false]
  · rw [b_one, ZMod.val_one]
    simp only [Nat.cast_one, one_ne_zero, or_true]

theorem add32_mod_div_from_eq (z c sum : ℤ)
    (hz_lo : 0 ≤ z)
    (hz_hi : z < 2 ^ 32)
    (hsum : z + c * 2 ^ 32 = sum) :
    z = sum % 2 ^ 32 ∧ c = sum / 2 ^ 32 := by
  have hpow : (0 : ℤ) < 2 ^ 32 := by
    norm_num
  have hpair : sum / 2 ^ 32 = c ∧ sum % 2 ^ 32 = z := by
    apply (Int.ediv_emod_unique (a := sum) (b := 2 ^ 32) (r := z) (q := c) hpow).2
    constructor
    · simpa [mul_comm] using hsum
    · exact ⟨hz_lo, hz_hi⟩
  exact ⟨hpair.2.symm, hpair.1.symm⟩

def pack32_int (a0 a1 a2 a3 : ℤ) : ℤ := a0 + a1 * 256 + a2 * 256 ^ 2 + a3 * 256 ^ 3

theorem add32_pack_eq (x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : ℤ)
    (h0 : x0 + y0 + carry_in = c0 * 256 + z0)
    (h1 : x1 + y1 + c0 = c1 * 256 + z1)
    (h2 : x2 + y2 + c1 = c2 * 256 + z2)
    (h3 : x3 + y3 + c2 = c3 * 256 + z3) :
    pack32_int z0 z1 z2 z3 + c3 * 2 ^ 32 =
      pack32_int x0 x1 x2 x3 + pack32_int y0 y1 y2 y3 + carry_in := by
  unfold pack32_int
  nlinarith [h0, h1, h2, h3]

theorem add32_pack_range (z0 z1 z2 z3 : ℤ)
    (hz0_lo : 0 ≤ z0) (hz0_hi : z0 < 256)
    (hz1_lo : 0 ≤ z1) (hz1_hi : z1 < 256)
    (hz2_lo : 0 ≤ z2) (hz2_hi : z2 < 256)
    (hz3_lo : 0 ≤ z3) (hz3_hi : z3 < 256) :
    0 ≤ pack32_int z0 z1 z2 z3 ∧ pack32_int z0 z1 z2 z3 < 2 ^ 32 := by
  unfold pack32_int
  constructor
  · nlinarith [show (0 : ℤ) ≤ 256 ^ 2 by norm_num, show (0 : ℤ) ≤ 256 ^ 3 by norm_num]
  · nlinarith [show (256 : ℤ) ^ 2 = 65536 by norm_num, show (256 : ℤ) ^ 3 = 16777216 by norm_num, show (2 : ℤ) ^ 32 = 4294967296 by norm_num]

theorem add32_soundness {x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : F p}
    (x0_byte : x0.val < 256) (x1_byte : x1.val < 256) (x2_byte : x2.val < 256) (x3_byte : x3.val < 256)
    (y0_byte : y0.val < 256) (y1_byte : y1.val < 256) (y2_byte : y2.val < 256) (y3_byte : y3.val < 256)
    (z0_byte : z0.val < 256) (z1_byte : z1.val < 256) (z2_byte : z2.val < 256) (z3_byte : z3.val < 256)
    (carry_in_bool : IsBool carry_in) (c0_bool : IsBool c0)
    (c1_bool : IsBool c1) (c2_bool : IsBool c2) (c3_bool : IsBool c3)
    (h0 : x0 + y0 + carry_in = c0 * 256 + z0)
    (h1 : x1 + y1 + c0 = c1 * 256 + z1)
    (h2 : x2 + y2 + c1 = c2 * 256 + z2)
    (h3 : x3 + y3 + c2 = c3 * 256 + z3) :
    ZMod.val z0 + ZMod.val z1 * 256 + ZMod.val z2 * 256 ^ 2 + ZMod.val z3 * 256 ^ 3 =
      (ZMod.val x0 + ZMod.val x1 * 256 + ZMod.val x2 * 256 ^ 2 + ZMod.val x3 * 256 ^ 3 +
            (ZMod.val y0 + ZMod.val y1 * 256 + ZMod.val y2 * 256 ^ 2 + ZMod.val y3 * 256 ^ 3) +
          ZMod.val carry_in) %
        2 ^ 32 ∧
    ZMod.val c3 =
      (ZMod.val x0 + ZMod.val x1 * 256 + ZMod.val x2 * 256 ^ 2 + ZMod.val x3 * 256 ^ 3 +
            (ZMod.val y0 + ZMod.val y1 * 256 + ZMod.val y2 * 256 ^ 2 + ZMod.val y3 * 256 ^ 3) +
          ZMod.val carry_in) /
        2 ^ 32 := by
  have h0' := congrArg ZMod.val h0
  have h1' := congrArg ZMod.val h1
  have h2' := congrArg ZMod.val h2
  have h3' := congrArg ZMod.val h3
  rw [lift_val1 x0_byte y0_byte carry_in_bool, lift_val2 z0_byte c0_bool] at h0'
  rw [lift_val1 x1_byte y1_byte c0_bool, lift_val2 z1_byte c1_bool] at h1'
  rw [lift_val1 x2_byte y2_byte c1_bool, lift_val2 z2_byte c2_bool] at h2'
  rw [lift_val1 x3_byte y3_byte c2_bool, lift_val2 z3_byte c3_bool] at h3'
  have hx0_nonneg : 0 ≤ ZMod.val x0 := Nat.zero_le _
  have hx1_nonneg : 0 ≤ ZMod.val x1 := Nat.zero_le _
  have hx2_nonneg : 0 ≤ ZMod.val x2 := Nat.zero_le _
  have hx3_nonneg : 0 ≤ ZMod.val x3 := Nat.zero_le _
  have hy0_nonneg : 0 ≤ ZMod.val y0 := Nat.zero_le _
  have hy1_nonneg : 0 ≤ ZMod.val y1 := Nat.zero_le _
  have hy2_nonneg : 0 ≤ ZMod.val y2 := Nat.zero_le _
  have hy3_nonneg : 0 ≤ ZMod.val y3 := Nat.zero_le _
  have hz0_nonneg : 0 ≤ ZMod.val z0 := Nat.zero_le _
  have hz1_nonneg : 0 ≤ ZMod.val z1 := Nat.zero_le _
  have hz2_nonneg : 0 ≤ ZMod.val z2 := Nat.zero_le _
  have hz3_nonneg : 0 ≤ ZMod.val z3 := Nat.zero_le _
  have hcarry_nonneg : 0 ≤ ZMod.val carry_in := Nat.zero_le _
  have hc0_nonneg : 0 ≤ ZMod.val c0 := Nat.zero_le _
  have hc1_nonneg : 0 ≤ ZMod.val c1 := Nat.zero_le _
  have hc2_nonneg : 0 ≤ ZMod.val c2 := Nat.zero_le _
  have hc3_nonneg : 0 ≤ ZMod.val c3 := Nat.zero_le _
  zify at *
  set x : ℤ := pack32_int (↑(ZMod.val x0)) (↑(ZMod.val x1)) (↑(ZMod.val x2)) (↑(ZMod.val x3))
  set y : ℤ := pack32_int (↑(ZMod.val y0)) (↑(ZMod.val y1)) (↑(ZMod.val y2)) (↑(ZMod.val y3))
  set z : ℤ := pack32_int (↑(ZMod.val z0)) (↑(ZMod.val z1)) (↑(ZMod.val z2)) (↑(ZMod.val z3))
  set carryi : ℤ := ↑(ZMod.val carry_in)
  set c3i : ℤ := ↑(ZMod.val c3)
  have hpack : z + c3i * 2 ^ 32 = x + y + carryi := by
    simpa [x, y, z, carryi, c3i, pack32_int] using
      (add32_pack_eq (↑(ZMod.val x0)) (↑(ZMod.val x1)) (↑(ZMod.val x2)) (↑(ZMod.val x3))
        (↑(ZMod.val y0)) (↑(ZMod.val y1)) (↑(ZMod.val y2)) (↑(ZMod.val y3))
        (↑(ZMod.val carry_in)) (↑(ZMod.val c0)) (↑(ZMod.val c1)) (↑(ZMod.val c2)) (↑(ZMod.val c3))
        (↑(ZMod.val z0)) (↑(ZMod.val z1)) (↑(ZMod.val z2)) (↑(ZMod.val z3))
        h0' h1' h2' h3')
  have hzrange : 0 ≤ z ∧ z < 2 ^ 32 := by
    simpa [z, pack32_int] using
      (add32_pack_range (↑(ZMod.val z0)) (↑(ZMod.val z1)) (↑(ZMod.val z2)) (↑(ZMod.val z3))
        hz0_nonneg z0_byte hz1_nonneg z1_byte hz2_nonneg z2_byte hz3_nonneg z3_byte)
  have hmoddiv := add32_mod_div_from_eq z c3i (x + y + carryi) hzrange.1 hzrange.2 hpack
  simpa [x, y, z, carryi, c3i, pack32_int] using hmoddiv

