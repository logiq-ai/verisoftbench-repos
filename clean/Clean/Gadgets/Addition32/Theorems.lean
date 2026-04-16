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

theorem add32_nat_unrolled (x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : ℕ) (h0 : x0 + y0 + carry_in = c0 * 256 + z0) (h1 : x1 + y1 + c0 = c1 * 256 + z1) (h2 : x2 + y2 + c1 = c2 * 256 + z2) (h3 : x3 + y3 + c2 = c3 * 256 + z3) : x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + (y0 + y1 * 256 + y2 * 256 ^ 2 + y3 * 256 ^ 3) + carry_in = z0 + z1 * 256 + z2 * 256 ^ 2 + z3 * 256 ^ 3 + c3 * 256 ^ 4 := by
  omega

theorem add32_output_lt (z0 z1 z2 z3 : ℕ) (z0_byte : z0 < 256) (z1_byte : z1 < 256) (z2_byte : z2 < 256) (z3_byte : z3 < 256) : z0 + z1 * 256 + z2 * 256 ^ 2 + z3 * 256 ^ 3 < 256 ^ 4 := by
  omega

theorem nat_mod_div_of_eq_add_mul (total low high base : ℕ) (hlow : low < base) (h : total = low + high * base) : low = total % base ∧ high = total / base := by
  have hbase : 0 < base := lt_of_le_of_lt (Nat.zero_le low) hlow
  constructor
  · rw [h, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow]
  · rw [h, Nat.add_mul_div_right _ _ hbase, Nat.div_eq_of_lt hlow, Nat.zero_add]

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
  have h0_nat := congrArg ZMod.val h0
  rw [lift_val1 x0_byte y0_byte carry_in_bool, lift_val2 z0_byte c0_bool] at h0_nat
  have h1_nat := congrArg ZMod.val h1
  rw [lift_val1 x1_byte y1_byte c0_bool, lift_val2 z1_byte c1_bool] at h1_nat
  have h2_nat := congrArg ZMod.val h2
  rw [lift_val1 x2_byte y2_byte c1_bool, lift_val2 z2_byte c2_bool] at h2_nat
  have h3_nat := congrArg ZMod.val h3
  rw [lift_val1 x3_byte y3_byte c2_bool, lift_val2 z3_byte c3_bool] at h3_nat
  let total := x0.val + x1.val * 256 + x2.val * 256 ^ 2 + x3.val * 256 ^ 3 +
    (y0.val + y1.val * 256 + y2.val * 256 ^ 2 + y3.val * 256 ^ 3) + carry_in.val
  let low := z0.val + z1.val * 256 + z2.val * 256 ^ 2 + z3.val * 256 ^ 3
  have hsplit : total = low + c3.val * 256 ^ 4 := by
    dsimp [total, low]
    exact add32_nat_unrolled x0.val x1.val x2.val x3.val y0.val y1.val y2.val y3.val carry_in.val c0.val c1.val c2.val c3.val z0.val z1.val z2.val z3.val h0_nat h1_nat h2_nat h3_nat
  have hlow : low < 256 ^ 4 := by
    dsimp [low]
    exact add32_output_lt z0.val z1.val z2.val z3.val z0_byte z1_byte z2_byte z3_byte
  have hmoddiv := nat_mod_div_of_eq_add_mul total low c3.val (256 ^ 4) hlow hsplit
  have hpow : 256 ^ 4 = 2 ^ 32 := by
    norm_num
  simpa [total, low, hpow] using hmoddiv

