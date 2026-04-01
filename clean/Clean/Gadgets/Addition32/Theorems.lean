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

theorem add32_weighted_sum_eq {x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : F p}
    (x0_byte : x0.val < 256) (x1_byte : x1.val < 256) (x2_byte : x2.val < 256) (x3_byte : x3.val < 256)
    (y0_byte : y0.val < 256) (y1_byte : y1.val < 256) (y2_byte : y2.val < 256) (y3_byte : y3.val < 256)
    (z0_byte : z0.val < 256) (z1_byte : z1.val < 256) (z2_byte : z2.val < 256) (z3_byte : z3.val < 256)
    (carry_in_bool : IsBool carry_in) (c0_bool : IsBool c0)
    (c1_bool : IsBool c1) (c2_bool : IsBool c2) (c3_bool : IsBool c3)
    (h0 : x0 + y0 + carry_in = c0 * 256 + z0)
    (h1 : x1 + y1 + c0 = c1 * 256 + z1)
    (h2 : x2 + y2 + c1 = c2 * 256 + z2)
    (h3 : x3 + y3 + c2 = c3 * 256 + z3) :
    U32.value (U32.mk x0 x1 x2 x3) + U32.value (U32.mk y0 y1 y2 y3) + ZMod.val carry_in =
      U32.value (U32.mk z0 z1 z2 z3) + ZMod.val c3 * 2 ^ 32 := by
  have s0 := congrArg ZMod.val h0
  have s1 := congrArg ZMod.val h1
  have s2 := congrArg ZMod.val h2
  have s3 := congrArg ZMod.val h3
  rw [lift_val1 x0_byte y0_byte carry_in_bool, lift_val2 z0_byte c0_bool] at s0
  rw [lift_val1 x1_byte y1_byte c0_bool, lift_val2 z1_byte c1_bool] at s1
  rw [lift_val1 x2_byte y2_byte c1_bool, lift_val2 z2_byte c2_bool] at s2
  rw [lift_val1 x3_byte y3_byte c2_bool, lift_val2 z3_byte c3_bool] at s3
  simp only [U32.value]
  omega

theorem nat_mod_div_of_eq_add_mul (a r q n : ℕ) (hn : 0 < n) (hEq : a = r + q * n) (hr : r < n) : r = a % n ∧ q = a / n := by
  constructor
  · have hrmod : r % n = r := Nat.mod_eq_of_lt hr
    have hmod : a % n = r := by
      rw [hEq, Nat.add_mul_mod_self_right, hrmod]
    exact hmod.symm
  · have lo : q * n ≤ a := by
      rw [hEq]
      exact Nat.le_add_left _ _
    have hi : a < (q + 1) * n := by
      calc
        a = r + q * n := hEq
        _ < n + q * n := by
          exact Nat.add_lt_add_right hr (q * n)
        _ = (q + 1) * n := by
          rw [Nat.succ_mul, Nat.add_comm]
    have hq : a / n = q := Nat.div_eq_of_lt_le lo hi
    exact hq.symm

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
  let total := U32.value (U32.mk x0 x1 x2 x3) + U32.value (U32.mk y0 y1 y2 y3) + ZMod.val carry_in
  let out := U32.value (U32.mk z0 z1 z2 z3)
  have hsum : total = out + ZMod.val c3 * 2 ^ 32 := by
    dsimp [total, out]
    exact add32_weighted_sum_eq x0_byte x1_byte x2_byte x3_byte y0_byte y1_byte y2_byte y3_byte z0_byte z1_byte z2_byte z3_byte carry_in_bool c0_bool c1_bool c2_bool c3_bool h0 h1 h2 h3
  have hout_lt : out < 2 ^ 32 := by
    dsimp [out]
    exact U32.value_lt_of_normalized (by
      simp only [U32.Normalized]
      exact ⟨z0_byte, z1_byte, z2_byte, z3_byte⟩)
  have hmoddiv := nat_mod_div_of_eq_add_mul total out (ZMod.val c3) (2 ^ 32) (by norm_num) hsum hout_lt
  rcases hmoddiv with ⟨hout_mod, hc3_div⟩
  constructor
  · simpa [total, out, U32.value]
      using hout_mod
  · simpa [total, out, U32.value]
      using hc3_div

