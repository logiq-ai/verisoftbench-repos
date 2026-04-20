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

theorem add32_output_lt {z0 z1 z2 z3 : F p}
    (z0_byte : z0.val < 256) (z1_byte : z1.val < 256) (z2_byte : z2.val < 256) (z3_byte : z3.val < 256) :
    (U32.mk z0 z1 z2 z3).value < 2 ^ 32 := by
  have hnorm : (U32.mk z0 z1 z2 z3).Normalized := by
    change z0.val < 256 ∧ z1.val < 256 ∧ z2.val < 256 ∧ z3.val < 256
    exact ⟨z0_byte, z1_byte, z2_byte, z3_byte⟩
  exact U32.value_lt_of_normalized (x := U32.mk z0 z1 z2 z3) hnorm

theorem add32_weighted_nat_sum {x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : ℕ}
    (h0 : x0 + y0 + carry_in = z0 + c0 * 256)
    (h1 : x1 + y1 + c0 = z1 + c1 * 256)
    (h2 : x2 + y2 + c1 = z2 + c2 * 256)
    (h3 : x3 + y3 + c2 = z3 + c3 * 256) :
    z0 + z1 * 256 + z2 * 256 ^ 2 + z3 * 256 ^ 3 + c3 * 256 ^ 4 =
      x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 +
        (y0 + y1 * 256 + y2 * 256 ^ 2 + y3 * 256 ^ 3) + carry_in := by
  have h1w := congrArg (fun n : ℕ => n * 256) h1
  have h2w := congrArg (fun n : ℕ => n * 256 ^ 2) h2
  have h3w := congrArg (fun n : ℕ => n * 256 ^ 3) h3
  ring_nf at h1w h2w h3w ⊢
  omega

theorem add32_carry_decomposition {x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : F p}
    (x0_byte : x0.val < 256) (x1_byte : x1.val < 256) (x2_byte : x2.val < 256) (x3_byte : x3.val < 256)
    (y0_byte : y0.val < 256) (y1_byte : y1.val < 256) (y2_byte : y2.val < 256) (y3_byte : y3.val < 256)
    (z0_byte : z0.val < 256) (z1_byte : z1.val < 256) (z2_byte : z2.val < 256) (z3_byte : z3.val < 256)
    (carry_in_bool : IsBool carry_in) (c0_bool : IsBool c0)
    (c1_bool : IsBool c1) (c2_bool : IsBool c2) (c3_bool : IsBool c3)
    (h0 : x0 + y0 + carry_in = c0 * 256 + z0)
    (h1 : x1 + y1 + c0 = c1 * 256 + z1)
    (h2 : x2 + y2 + c1 = c2 * 256 + z2)
    (h3 : x3 + y3 + c2 = c3 * 256 + z3) :
    (U32.mk z0 z1 z2 z3).value + 2 ^ 32 * ZMod.val c3 =
      (U32.mk x0 x1 x2 x3).value + (U32.mk y0 y1 y2 y3).value + ZMod.val carry_in := by
  have h0' := congrArg ZMod.val h0
  have h1' := congrArg ZMod.val h1
  have h2' := congrArg ZMod.val h2
  have h3' := congrArg ZMod.val h3
  rw [lift_val1 x0_byte y0_byte carry_in_bool, lift_val2 z0_byte c0_bool] at h0'
  rw [lift_val1 x1_byte y1_byte c0_bool, lift_val2 z1_byte c1_bool] at h1'
  rw [lift_val1 x2_byte y2_byte c1_bool, lift_val2 z2_byte c2_bool] at h2'
  rw [lift_val1 x3_byte y3_byte c2_bool, lift_val2 z3_byte c3_bool] at h3'
  have h1w := congrArg (fun n : ℕ => n * 256) h1'
  have h2w := congrArg (fun n : ℕ => n * 65536) h2'
  have h3w := congrArg (fun n : ℕ => n * 16777216) h3'
  clear h0 h1 h2 h3
  clear x0_byte x1_byte x2_byte x3_byte y0_byte y1_byte y2_byte y3_byte z0_byte z1_byte z2_byte z3_byte
  clear carry_in_bool c0_bool c1_bool c2_bool c3_bool
  simp [U32.value]
  ring_nf at h1w h2w h3w ⊢
  omega

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
  have hz : (U32.mk z0 z1 z2 z3).value =
      ZMod.val z0 + ZMod.val z1 * 256 + ZMod.val z2 * 256 ^ 2 + ZMod.val z3 * 256 ^ 3 := by
    rfl
  have hx : (U32.mk x0 x1 x2 x3).value =
      ZMod.val x0 + ZMod.val x1 * 256 + ZMod.val x2 * 256 ^ 2 + ZMod.val x3 * 256 ^ 3 := by
    rfl
  have hy : (U32.mk y0 y1 y2 y3).value =
      ZMod.val y0 + ZMod.val y1 * 256 + ZMod.val y2 * 256 ^ 2 + ZMod.val y3 * 256 ^ 3 := by
    rfl
  have hqr :
      (((U32.mk x0 x1 x2 x3).value + (U32.mk y0 y1 y2 y3).value + ZMod.val carry_in) / 2 ^ 32 =
          ZMod.val c3) ∧
        (((U32.mk x0 x1 x2 x3).value + (U32.mk y0 y1 y2 y3).value + ZMod.val carry_in) % 2 ^ 32 =
          (U32.mk z0 z1 z2 z3).value) :=
    (Nat.div_mod_unique
      (a := (U32.mk x0 x1 x2 x3).value + (U32.mk y0 y1 y2 y3).value + ZMod.val carry_in)
      (b := 2 ^ 32) (c := (U32.mk z0 z1 z2 z3).value) (d := ZMod.val c3)
      (by norm_num)).2
      ⟨add32_carry_decomposition x0_byte x1_byte x2_byte x3_byte y0_byte y1_byte y2_byte y3_byte
          z0_byte z1_byte z2_byte z3_byte carry_in_bool c0_bool c1_bool c2_bool c3_bool h0 h1 h2 h3,
        add32_output_lt z0_byte z1_byte z2_byte z3_byte⟩
  constructor
  · rw [← hz, ← hx, ← hy]
    exact hqr.2.symm
  · rw [← hx, ← hy]
    exact hqr.1.symm

