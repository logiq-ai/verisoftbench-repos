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
        2 ^ 32
  := by sorry
