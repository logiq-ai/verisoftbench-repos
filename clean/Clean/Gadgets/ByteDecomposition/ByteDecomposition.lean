import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Gadgets.ByteDecomposition.Theorems
import Init.Data.Nat.Div.Basic

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

namespace Gadgets.ByteDecomposition
open FieldUtils (mod floorDiv two_lt two_pow_lt two_val two_pow_val)

structure Outputs (F : Type) where
  low : F
  high : F

instance : ProvableStruct Outputs where
  components := [field, field]
  toComponents := fun { low, high } => .cons low (.cons high .nil)
  fromComponents := fun (.cons low (.cons high .nil)) => { low, high }

/--
  Decompose a byte into a low and a high part.
  The low part is the least significant `offset` bits,
  and the high part is the most significant `8 - offset` bits.
-/
def main (offset : Fin 8) (x : Expression (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let low ← witness fun env => mod (env x) (2^offset.val) (by simp [two_pow_lt])
  let high ← witness fun env => floorDiv (env x) (2^offset.val)

  lookup ByteTable ((2^(8-offset.val) : F p) * low)
  lookup ByteTable high

  x === low + high * (2^offset.val : F p)

  return { low, high }

def Assumptions (x : F p) := x.val < 256

def Spec (offset : Fin 8) (x : F p) (out : Outputs (F p)) :=
  let ⟨low, high⟩ := out
  (low.val = x.val % (2^offset.val) ∧ high.val = x.val / (2^offset.val))
  ∧ (low.val < 2^offset.val ∧ high.val < 2^(8-offset.val))

def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) field Outputs where
  main := main offset
  localLength _ := 2
  output _ i0 := varFromOffset Outputs i0

theorem byteDecomposition_arith_soundness (offset : Fin 8) (x low high : F p) (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8) (h_eq : x = low + high * 2^offset.val) : low.val = x.val % 2^offset.val ∧ high.val = x.val / 2^offset.val := by
  have hoff : offset.val ≤ 8 := by
    omega
  have low_lt_8 : low.val < 2 ^ 8 := by
    exact lt_of_lt_of_le low_lt (Nat.pow_le_pow_of_le (a := 2) Nat.one_lt_ofNat hoff)
  have hpow : (2 ^ offset.val : F p).val ≤ 2 ^ 8 := by
    rw [two_pow_val _ hoff]
    exact Nat.pow_le_pow_of_le (a := 2) Nat.one_lt_ofNat hoff
  have h_lift : (low + high * (2 ^ offset.val : F p)).val = low.val + high.val * (2 ^ offset.val : F p).val := by
    exact Theorems.byteDecomposition_lift low_lt_8 high_lt hpow
  have h_nat : x.val = low.val + high.val * 2 ^ offset.val := by
    rw [h_eq]
    simpa only [two_pow_val _ hoff] using h_lift
  constructor
  · rw [h_nat, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt low_lt]
  · rw [h_nat, Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num)), Nat.div_eq_of_lt low_lt, Nat.zero_add]

theorem byteDecomposition_shift_power_mul_eq_pow8 (offset : Fin 8) : ((2^(8-offset.val) : F p) * (2^offset.val : F p)) = (2^8 : F p) := by
  have hoff : offset.val ≤ 8 := Nat.le_of_lt offset.is_lt
  calc
    ((2^(8-offset.val) : F p) * (2^offset.val : F p))
        = (((2^(8-offset.val) * 2^offset.val : ℕ) : F p)) := by
            simp [Nat.cast_mul]
    _ = (2^8 : ℕ) := by rw [Nat.pow_sub_mul_pow 2 hoff]
    _ = (2^8 : F p) := by norm_num

theorem byteDecomposition_shifted_low_dvd (offset : Fin 8) (x low high : F p) (x_lt : x.val < 2^8) (shifted_low_lt : ((2^(8-offset.val) : F p) * low).val < 2^8) (high_lt : high.val < 2^8) (h_eq : x = low + high * 2^offset.val) : 2^(8-offset.val) ∣ ((2^(8-offset.val) : F p) * low).val := by
  have hp512 : p > 512 := by
    linarith [p_large_enough.elim]
  letI : Fact (p > 512) := .mk hp512
  have hoff : offset.val ≤ 8 := Nat.le_of_lt offset.is_lt
  have hpow8_nat : 2 ^ (8 - offset.val) * 2 ^ offset.val = 2 ^ 8 := by
    simpa using (Nat.pow_sub_mul_pow 2 hoff)
  have hc_pos : 0 < 2 ^ (8 - offset.val) := Nat.two_pow_pos _
  have hc_le : 2 ^ (8 - offset.val) ≤ 2 ^ 8 := by
    exact Nat.pow_le_pow_of_le (by norm_num : 1 < 2) (by omega)
  have h256sq_lt_p : 2 ^ 8 * 2 ^ 8 < p := by
    have h : 2 ^ 8 * 2 ^ 8 < 2 ^ 16 + 2 ^ 8 := by
      norm_num
    linarith [p_large_enough.elim]
  have hcx_lt_nat : 2 ^ (8 - offset.val) * x.val < p := by
    refine lt_trans ?_ h256sq_lt_p
    exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left x_lt hc_pos)
      (Nat.mul_le_mul_right _ hc_le)
  have hcx_lt : ((2 ^ (8 - offset.val) : F p)).val * x.val < p := by
    rw [two_pow_val _ (by omega)]
    exact hcx_lt_nat
  have hxmul : ((2 ^ (8 - offset.val) : F p) * x).val = 2 ^ (8 - offset.val) * x.val := by
    have hxmul' := ZMod.val_mul_of_lt (a := (2 ^ (8 - offset.val) : F p)) (b := x) hcx_lt
    rw [two_pow_val _ (by omega)] at hxmul'
    exact hxmul'
  have hfield : ((2 ^ (8 - offset.val) : F p) * x) =
      ((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p) := by
    calc
      ((2 ^ (8 - offset.val) : F p) * x)
          = (2 ^ (8 - offset.val) : F p) * (low + high * (2 ^ offset.val : F p)) := by
            rw [h_eq]
      _ = ((2 ^ (8 - offset.val) : F p) * low) + ((2 ^ (8 - offset.val) : F p) * (high * (2 ^ offset.val : F p))) := by
            rw [mul_add]
      _ = ((2 ^ (8 - offset.val) : F p) * low) + (((2 ^ (8 - offset.val) : F p) * high) * (2 ^ offset.val : F p)) := by
            rw [mul_assoc]
      _ = ((2 ^ (8 - offset.val) : F p) * low) + high * ((2 ^ (8 - offset.val) : F p) * (2 ^ offset.val : F p)) := by
            rw [mul_comm (2 ^ (8 - offset.val) : F p) high, ← mul_assoc]
      _ = ((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p) := by
            rw [byteDecomposition_shift_power_mul_eq_pow8 offset]
  have hpow_le : ((2 ^ 8 : F p)).val ≤ 2 ^ 8 := by
    rw [two_pow_val 8 (by omega)]
  have hrhs : (((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p)).val =
      ((2 ^ (8 - offset.val) : F p) * low).val + high.val * (2 ^ 8 : F p).val := by
    exact Theorems.byteDecomposition_lift shifted_low_lt high_lt hpow_le
  have hnat0 : 2 ^ (8 - offset.val) * x.val =
      ((2 ^ (8 - offset.val) : F p) * low).val + high.val * (2 ^ 8 : F p).val := by
    calc
      2 ^ (8 - offset.val) * x.val = ((2 ^ (8 - offset.val) : F p) * x).val := by
        symm
        exact hxmul
      _ = (((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p)).val := by
        rw [hfield]
      _ = ((2 ^ (8 - offset.val) : F p) * low).val + high.val * (2 ^ 8 : F p).val := by
        exact hrhs
  have hnat : 2 ^ (8 - offset.val) * x.val =
      ((2 ^ (8 - offset.val) : F p) * low).val + high.val * 2 ^ 8 := by
    rw [two_pow_val 8 (by omega)] at hnat0
    exact hnat0
  have hnat' : 2 ^ (8 - offset.val) * x.val =
      ((2 ^ (8 - offset.val) : F p) * low).val +
        2 ^ (8 - offset.val) * (high.val * 2 ^ offset.val) := by
    rw [← hpow8_nat] at hnat
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnat
  have hsum : 2 ^ (8 - offset.val) ∣ ((2 ^ (8 - offset.val) : F p) * low).val +
      2 ^ (8 - offset.val) * (high.val * 2 ^ offset.val) := by
    refine ⟨x.val, ?_⟩
    simpa [Nat.mul_comm] using hnat'.symm
  have hmul : 2 ^ (8 - offset.val) ∣ 2 ^ (8 - offset.val) * (high.val * 2 ^ offset.val) := by
    exact dvd_mul_right _ _
  exact (Nat.dvd_add_left hmul).1 hsum

theorem byteDecomposition_low_lt_from_shifted_lookup (offset : Fin 8) (x low high : F p) (x_lt : x.val < 2^8) (shifted_low_lt : ((2^(8-offset.val) : F p) * low).val < 2^8) (high_lt : high.val < 2^8) (h_eq : x = low + high * 2^offset.val) : low.val < 2^offset.val := by
  let c : ℕ := 2 ^ (8 - offset.val)
  let d : ℕ := 2 ^ offset.val
  have pow_8_nat : 2 ^ 8 = c * d := by
    dsimp [c, d]
    simp [← pow_add]
  have hc_lt : c < p := by
    dsimp [c]
    exact two_pow_lt _ (by omega)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Nat.two_pow_pos _
  have hdiv : c ∣ (((c : F p) * low).val) := by
    dsimp [c]
    simpa using byteDecomposition_shifted_low_dvd offset x low high x_lt shifted_low_lt high_lt h_eq
  obtain ⟨z, hz⟩ := hdiv
  have hval : (((c : F p) * low).val) = c * low.val := by
    exact FieldUtils.mul_nat_val_of_dvd (x := low) c hc_lt hz
  have hbound : c * low.val < c * d := by
    rw [← hval, ← pow_8_nat]
    simpa [c] using shifted_low_lt
  have hlt : low.val < d := by
    exact (Nat.mul_lt_mul_left hc_pos).mp hbound
  dsimp [d] at hlt
  exact hlt

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  rintro i0 env input_var x h_input hx h_constraints
  simp only [ProvableType.eval_field] at h_input
  simp only [circuit_norm, main, elaborated, h_input, ByteTable] at h_constraints ⊢
  let low : F p := env.get i0
  let high : F p := env.get (i0 + 1)
  have hlow_shifted : ((2 ^ (8 - offset.val) : F p) * low).val < 2 ^ 8 := by
    simpa [low] using h_constraints.1
  have hhigh : high.val < 2 ^ 8 := by
    simpa [high] using h_constraints.2.1
  have heq : x = low + high * 2 ^ offset.val := by
    simpa [low, high] using h_constraints.2.2
  have hlow : low.val < 2 ^ offset.val :=
    byteDecomposition_low_lt_from_shifted_lookup offset x low high hx hlow_shifted hhigh heq
  have harith := byteDecomposition_arith_soundness offset x low high hlow hhigh heq
  rcases harith with ⟨hlow_mod, hhigh_div⟩
  constructor
  · exact ⟨hlow_mod, hhigh_div⟩
  · constructor
    · exact hlow
    · rw [hhigh_div]
      apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))).2
      have hpow : 2 ^ (8 - offset.val) * 2 ^ offset.val = 2 ^ 8 := by
        rw [← Nat.pow_add]
        simpa [Nat.sub_add_cancel (Nat.le_of_lt offset.is_lt)]
      rw [hpow]
      simpa using hx


theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) Assumptions := by
  rintro i0 env x_var henv (x : F p) h_input (x_byte : x.val < 256)
  simp only [ProvableType.eval_field] at h_input
  simp only [circuit_norm, main, elaborated, h_input, ByteTable] at henv ⊢
  simp only [henv]
  have pow_8_nat : 2^8 = 2^(8-offset.val) * 2^offset.val := by simp [←pow_add]

  and_intros

  · show (2^(8-offset.val) * mod x (2^offset.val) _).val < 2^8
    suffices ((2 : F p)^(8-offset.val)).val * (mod x (2^offset.val) _).val < 2^8 by
      rwa [ZMod.val_mul_of_lt (by linarith [p_large_enough.elim])]
    rw [two_pow_val _ (by omega), pow_8_nat]
    exact Nat.mul_lt_mul_of_pos_left FieldUtils.mod_lt (Nat.pow_pos (by norm_num))

  · show (floorDiv x (2^offset.val)).val < 2^8
    apply FieldUtils.floorDiv_lt
    rw [PNat.pow_coe, PNat.val_ofNat]
    suffices 1 * 2^8 ≤ 2^offset.val * 2^8 by linarith
    apply Nat.mul_le_mul_right
    exact Nat.succ_le_of_lt (by norm_num)

  · have : (2^offset.val : F p) = ((2^offset.val : ℕ+) : F p) := by simp
    rw [this, mul_comm, FieldUtils.mod_add_floorDiv]

def circuit (offset : Fin 8) : FormalCircuit (F p) field Outputs := {
  elaborated offset with
  main := main offset
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset
}
end Gadgets.ByteDecomposition
