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

theorem scaled_lookup_decode_nat (offset : Fin 8) (x scaledLow high : ℕ)
  (h_eq : (2^(8-offset.val)) * x = scaledLow + high * 2^8)
  (h_scaledLow_lt : scaledLow < 2^8) :
  high = x / 2^offset.val ∧ scaledLow = (2^(8-offset.val)) * (x % 2^offset.val) := by
  let d := 2 ^ (8 - offset.val)
  let c := 2 ^ offset.val
  have hdc : d * c = 2 ^ 8 := by
    dsimp [d, c]
    calc
      2 ^ (8 - offset.val) * 2 ^ offset.val = 2 ^ ((8 - offset.val) + offset.val) := by
        rw [← Nat.pow_add]
      _ = 2 ^ 8 := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt offset.is_lt)]
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hmod_lt : d * (x % c) < 2 ^ 8 := by
    have hxmodlt : x % c < c := Nat.mod_lt _ hcpos
    calc
      d * (x % c) < d * c := by
        exact Nat.mul_lt_mul_of_pos_left hxmodlt hdpos
      _ = 2 ^ 8 := hdc
  have hxdecomp : d * x = d * (x % c) + (x / c) * 2 ^ 8 := by
    calc
      d * x = d * (x % c + c * (x / c)) := by
        rw [Nat.mod_add_div x c]
      _ = d * (x % c) + d * (c * (x / c)) := by
        rw [Nat.mul_add]
      _ = d * (x % c) + (d * c) * (x / c) := by
        rw [← Nat.mul_assoc]
      _ = d * (x % c) + (2 ^ 8) * (x / c) := by
        rw [hdc]
      _ = d * (x % c) + (x / c) * 2 ^ 8 := by
        rw [Nat.mul_comm (2 ^ 8) (x / c)]
  let r := d * (x % c)
  let q := x / c
  have h1 : scaledLow + high * 2 ^ 8 = r + q * 2 ^ 8 := by
    calc
      scaledLow + high * 2 ^ 8 = d * x := by
        exact h_eq.symm
      _ = d * (x % c) + (x / c) * 2 ^ 8 := hxdecomp
      _ = r + q * 2 ^ 8 := by
        rfl
  have hrlt : r < 2 ^ 8 := by
    dsimp [r]
    exact hmod_lt
  have hmain : scaledLow = r ∧ high = q := by
    omega
  rcases hmain with ⟨hsl, hh⟩
  constructor
  · simpa [q, c] using hh
  · simpa [r, d] using hsl

theorem scaled_lookup_nat_eq (offset : Fin 8) (x low high : F p)
  (x_lt : x.val < 2^8)
  (scaled_low_lt : (((2^(8-offset.val) : F p) * low).val < 2^8))
  (high_lt : high.val < 2^8)
  (h_eq : x = low + high * 2^offset.val) :
  (2^(8-offset.val)) * x.val = (((2^(8-offset.val) : F p) * low).val) + high.val * 2^8 := by
  have hsub_le : 8 - offset.val ≤ 8 := by
    omega
  have hpowval : ((2 ^ (8 - offset.val) : F p)).val = 2 ^ (8 - offset.val) := by
    exact two_pow_val _ hsub_le
  have hpow8val : ((2 ^ 8 : F p)).val = 2 ^ 8 := by
    exact two_pow_val 8 (by omega)
  have hscaled := congrArg (fun z => (((2 ^ (8 - offset.val) : F p) * z)).val) h_eq
  have h_mul_lt : 2 ^ (8 - offset.val) * x.val < p := by
    have hd_le : 2 ^ (8 - offset.val) ≤ 2 ^ 8 := by
      exact Nat.pow_le_pow_of_le (show 2 > 1 by norm_num) (by omega)
    have h1 : 2 ^ (8 - offset.val) * x.val < 2 ^ (8 - offset.val) * 2 ^ 8 := by
      exact Nat.mul_lt_mul_of_pos_left x_lt (Nat.pow_pos (by norm_num))
    have h2 : 2 ^ (8 - offset.val) * 2 ^ 8 ≤ 2 ^ 8 * 2 ^ 8 := by
      exact Nat.mul_le_mul_right (2 ^ 8) hd_le
    have h3 : 2 ^ (8 - offset.val) * x.val < 2 ^ 8 * 2 ^ 8 :=
      lt_of_lt_of_le h1 h2
    have hp16 : 2 ^ 16 < p := by
      linarith [p_large_enough.elim]
    have hp : 2 ^ 8 * 2 ^ 8 < p := by
      simpa [pow_add] using hp16
    exact lt_trans h3 hp
  have hleft : (((2 ^ (8 - offset.val) : F p) * x)).val = 2 ^ (8 - offset.val) * x.val := by
    have hmul' : ((2 ^ (8 - offset.val) : F p)).val * x.val < p := by
      rwa [hpowval]
    rw [ZMod.val_mul_of_lt hmul', hpowval]
  have hpow :
      ((2 ^ (8 - offset.val) : F p) * (2 ^ offset.val : F p)) = (2 ^ 8 : F p) := by
    rw [← pow_add]
    congr
    omega
  have hright :
      (((2 ^ (8 - offset.val) : F p) * (low + high * 2 ^ offset.val)).val) =
        (((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p)).val := by
    rw [mul_add]
    congr 1
    congr 1
    calc
      (2 ^ (8 - offset.val) : F p) * (high * 2 ^ offset.val)
          = high * ((2 ^ (8 - offset.val) : F p) * (2 ^ offset.val : F p)) := by
              ring
      _ = high * (2 ^ 8 : F p) := by
            rw [hpow]
  have hbyte :
      ((((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p)).val) =
        (((2 ^ (8 - offset.val) : F p) * low).val) + high.val * 2 ^ 8 := by
    have hbyte' :=
      Gadgets.ByteDecomposition.Theorems.byteDecomposition_lift
        (low := ((2 ^ (8 - offset.val) : F p) * low))
        (high := high)
        (two_power := (2 ^ 8 : F p))
        scaled_low_lt
        high_lt
        (by
          rw [hpow8val])
    rw [hpow8val] at hbyte'
    exact hbyte'
  calc
    2 ^ (8 - offset.val) * x.val = (((2 ^ (8 - offset.val) : F p) * x)).val := hleft.symm
    _ = (((2 ^ (8 - offset.val) : F p) * (low + high * 2 ^ offset.val)).val) := hscaled
    _ = ((((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p)).val) := hright
    _ = (((2 ^ (8 - offset.val) : F p) * low).val) + high.val * 2 ^ 8 := hbyte

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  rintro i0 env x_var x h_input x_lt h_constraints
  simp only [ProvableType.eval_field] at h_input
  simp only [circuit_norm, main, elaborated, h_input, ByteTable] at h_constraints ⊢
  set low : F p := env.get i0
  set high : F p := env.get (i0 + 1)
  have h_scaledLow : (((2 ^ (8 - offset.val) : F p) * low).val < 2 ^ 8) := by
    simpa [low] using h_constraints.1
  have h_highByte : high.val < 2 ^ 8 := by
    simpa [high] using h_constraints.2.1
  have h_eq : x = low + high * 2 ^ offset.val := by
    simpa [low, high] using h_constraints.2.2
  have h_nat_eq :=
    scaled_lookup_nat_eq offset x low high x_lt h_scaledLow h_highByte h_eq
  rcases
      scaled_lookup_decode_nat offset x.val (((2 ^ (8 - offset.val) : F p) * low).val) high.val
        h_nat_eq h_scaledLow with
    ⟨h_high_div, h_scaledLow_eq⟩
  have h_cpos : 0 < 2 ^ (8 - offset.val) := by positivity
  have h_dpos : 0 < 2 ^ offset.val := by positivity
  have h_scaledLow_eq' : ((((2 ^ (8 - offset.val) : ℕ) : F p) * low).val) =
      (2 ^ (8 - offset.val)) * (x.val % 2 ^ offset.val) := by
    simpa using h_scaledLow_eq
  have h_low_mul :=
    (FieldUtils.mul_nat_val_eq_iff (x := low) (c := 2 ^ (8 - offset.val)) h_cpos
        (two_pow_lt _ (by omega))).1 h_scaledLow_eq'
  have h_low_mod : low.val = x.val % 2 ^ offset.val := h_low_mul.1
  have h_low_lt : low.val < 2 ^ offset.val := by
    rw [h_low_mod]
    exact Nat.mod_lt _ h_dpos
  have h_high_lt : high.val < 2 ^ (8 - offset.val) := by
    rw [h_high_div]
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm, ← Nat.pow_add]
    simpa [Assumptions] using x_lt
  simp only [Spec]
  constructor
  · constructor
    · exact h_low_mod
    · exact h_high_div
  · constructor
    · exact h_low_lt
    · exact h_high_lt


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
