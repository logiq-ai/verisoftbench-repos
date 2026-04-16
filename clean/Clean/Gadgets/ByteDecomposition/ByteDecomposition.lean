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

theorem low_lt_of_scaled_lookup (offset : Fin 8) (x low high : F p) (x_lt : x.val < 2^8) (scaled_low_lt : (((2^(8-offset.val) : F p) * low).val < 2^8)) (high_lt : high.val < 2^8) (h_eq : x = low + high * (2^offset.val : F p)) : low.val < 2^offset.val := by
  let c : ℕ := 2 ^ (8 - offset.val)
  let y : ℕ := (((c : F p) * low).val)
  have hsub_add : 8 - offset.val + offset.val = 8 := by
    omega
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Nat.pow_pos (by norm_num)
  have hc_le : c ≤ 2 ^ 8 := by
    dsimp [c]
    simpa using
      (Nat.pow_le_pow_of_le (a := 2) (show 2 > 1 by norm_num) (Nat.sub_le 8 offset.val))
  have hc_lt_p : c < p := by
    dsimp [c]
    exact two_pow_lt _ (by omega)
  have hy_lt : y < 2 ^ 8 := by
    simpa [y, c] using scaled_low_lt
  have hc_val : ((c : F p)).val = c := by
    dsimp [c]
    simpa using (two_pow_val (8 - offset.val) (by omega))
  have hpow8_val : ((2 ^ 8 : F p)).val = 2 ^ 8 := by
    simpa using (two_pow_val 8 (by omega))
  have hpow_nat : c * 2 ^ offset.val = 2 ^ 8 := by
    dsimp [c]
    rw [← pow_add, hsub_add]
    norm_num
  have hpow : ((c : F p) * (2 ^ offset.val : F p)) = (2 ^ 8 : F p) := by
    calc
      ((c : F p) * (2 ^ offset.val : F p)) = (256 : F p) := by
        simpa [Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (n : F p)) hpow_nat
      _ = (2 ^ 8 : F p) := by norm_num
  have hmul_eq : ((c : F p) * x) = ((c : F p) * low) + high * (2 ^ 8 : F p) := by
    calc
      ((c : F p) * x) = (c : F p) * (low + high * (2 ^ offset.val : F p)) := by rw [h_eq]
      _ = ((c : F p) * low) + (c : F p) * (high * (2 ^ offset.val : F p)) := by rw [mul_add]
      _ = ((c : F p) * low) + high * ((c : F p) * (2 ^ offset.val : F p)) := by
        congr 1
        simpa [mul_assoc, mul_comm, mul_left_comm]
      _ = ((c : F p) * low) + high * (2 ^ 8 : F p) := by rw [hpow]
  have h256sq_lt_p : 2 ^ 8 * 2 ^ 8 < p := by
    have h16_lt_p : 2 ^ 16 < p := by
      linarith [p_large_enough.elim]
    calc
      2 ^ 8 * 2 ^ 8 = 2 ^ 16 := by rw [← pow_add]
      _ < p := h16_lt_p
  have hcx_lt : c * x.val < p := by
    have hx_mul : c * x.val < c * 2 ^ 8 := by
      exact Nat.mul_lt_mul_of_pos_left x_lt hc_pos
    have hc_mul : c * 2 ^ 8 ≤ 2 ^ 8 * 2 ^ 8 := by
      exact Nat.mul_le_mul_right (2 ^ 8) hc_le
    exact lt_trans (lt_of_lt_of_le hx_mul hc_mul) h256sq_lt_p
  have hmulx_val : (((c : F p) * x).val) = c * x.val := by
    have htmp : (((c : F p) * x).val) = ((c : F p)).val * x.val := by
      exact ZMod.val_mul_of_lt (by rw [hc_val]; exact hcx_lt)
    simpa [hc_val] using htmp
  have hsum_val : ((((c : F p) * low) + high * (2 ^ 8 : F p)).val) = y + high.val * 2 ^ 8 := by
    have hpow8_le : ((2 ^ 8 : F p)).val ≤ 2 ^ 8 := by
      rw [hpow8_val]
    have htmp :=
      Gadgets.ByteDecomposition.Theorems.byteDecomposition_lift
        (low := ((c : F p) * low)) (high := high) (two_power := (2 ^ 8 : F p))
        (by simpa [c] using scaled_low_lt) high_lt hpow8_le
    simpa [y, hpow8_val] using htmp
  have hnat : c * x.val = y + high.val * 2 ^ 8 := by
    calc
      c * x.val = (((c : F p) * x).val) := by symm; exact hmulx_val
      _ = ((((c : F p) * low) + high * (2 ^ 8 : F p)).val) := by rw [hmul_eq]
      _ = y + high.val * 2 ^ 8 := hsum_val
  have pow_8_nat : 2 ^ 8 = c * 2 ^ offset.val := by
    rw [← hpow_nat]
  have htail_dvd : c ∣ high.val * 2 ^ 8 := by
    rw [pow_8_nat]
    refine ⟨high.val * 2 ^ offset.val, ?_⟩
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hsum_dvd : c ∣ y + high.val * 2 ^ 8 := by
    exact ⟨x.val, hnat.symm⟩
  have hy_dvd : c ∣ y := by
    exact (Nat.dvd_add_iff_left (m := y) (n := high.val * 2 ^ 8) htail_dvd).mpr hsum_dvd
  have hz_lt : y / c < 2 ^ offset.val := by
    rw [Nat.div_lt_iff_lt_mul hc_pos]
    simpa [pow_8_nat, Nat.mul_comm] using hy_lt
  have hy_eq : y = c * (y / c) := by
    simpa [Nat.mul_comm] using (Nat.eq_mul_of_div_eq_left hy_dvd rfl)
  have hy_low : y = c * low.val := by
    dsimp [y]
    exact FieldUtils.mul_nat_val_of_dvd c hc_lt_p hy_eq
  have hlow_eq : low.val = y / c := by
    apply Nat.eq_of_mul_eq_mul_left hc_pos
    calc
      c * low.val = y := by simpa using hy_low.symm
      _ = c * (y / c) := hy_eq
  rw [hlow_eq]
  exact hz_lt

theorem soundness_core (offset : Fin 8) (x low high : F p) (x_lt : x.val < 2^8) (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8) (h_eq : x = low + high * (2^offset.val : F p)) : low.val = x.val % 2^offset.val ∧ high.val = x.val / 2^offset.val := by
  have h_off : offset.val ≤ 8 := by
    omega
  have h_low : low.val < 2 ^ 8 := by
    exact lt_of_lt_of_le low_lt (Nat.pow_le_pow_of_le (by norm_num) h_off)
  have h_two_power : (2 ^ offset.val : F p).val ≤ 2 ^ 8 := by
    rw [two_pow_val offset.val h_off]
    exact Nat.pow_le_pow_of_le (by norm_num) h_off
  have h_nat : x.val = low.val + high.val * 2 ^ offset.val := by
    calc
      x.val = (low + high * (2 ^ offset.val : F p)).val := by
        rw [h_eq]
      _ = low.val + high.val * (2 ^ offset.val : F p).val := by
        simpa using Theorems.byteDecomposition_lift (low := low) (high := high)
          (two_power := (2 ^ offset.val : F p)) h_low high_lt h_two_power
      _ = low.val + high.val * 2 ^ offset.val := by
        rw [two_pow_val offset.val h_off]
  have h_base_pos : 0 < 2 ^ offset.val := by
    exact Nat.pow_pos (by norm_num : 0 < 2)
  have h_div_mod : x.val / (2 ^ offset.val) = high.val ∧ x.val % (2 ^ offset.val) = low.val := by
    apply (Nat.div_mod_unique (a := x.val) (b := 2 ^ offset.val) (c := low.val) (d := high.val) h_base_pos).2
    constructor
    · simpa [Nat.mul_comm, Nat.add_comm] using h_nat.symm
    · exact low_lt
  exact ⟨h_div_mod.2.symm, h_div_mod.1.symm⟩

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  intro i0 env input_var input h_input h_assumptions h_holds
  simp only [ProvableType.eval_field] at h_input
  simp only [circuit_norm, main, elaborated, h_input, ByteTable] at h_holds ⊢
  simp only [Spec]
  change input.val < 2 ^ 8 at h_assumptions
  rcases h_holds with ⟨h_scaled_low_lt, h_high_lt_byte, h_eq⟩
  have low_lt : (env.get i0).val < 2 ^ offset.val := by
    exact low_lt_of_scaled_lookup offset input (env.get i0) (env.get (i0 + 1))
      h_assumptions h_scaled_low_lt h_high_lt_byte h_eq
  have h_core := soundness_core offset input (env.get i0) (env.get (i0 + 1))
    h_assumptions low_lt h_high_lt_byte h_eq
  rcases h_core with ⟨low_eq, high_eq⟩
  constructor
  · exact ⟨low_eq, high_eq⟩
  · constructor
    · exact low_lt
    · rw [high_eq]
      have pow_8_nat : 2 ^ 8 = 2 ^ (8 - offset.val) * 2 ^ offset.val := by
        simp [←pow_add]
      have h_input_lt : input.val < 2 ^ offset.val * 2 ^ (8 - offset.val) := by
        rw [pow_8_nat] at h_assumptions
        rw [Nat.mul_comm] at h_assumptions
        exact h_assumptions
      exact Nat.div_lt_of_lt_mul h_input_lt


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
