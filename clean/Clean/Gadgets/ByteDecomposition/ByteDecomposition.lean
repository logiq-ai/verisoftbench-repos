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

theorem pow_mul_lt_two_pow_16 (n x : ℕ) (hn : n ≤ 8) (hx : x < 2 ^ 8) : 2 ^ n * x < 2 ^ 16 := by
  have hlt : 2 ^ n * x < 2 ^ (n + 8) := by
    have hx' : 2 ^ n * x < 2 ^ n * 2 ^ 8 := by
      exact Nat.mul_lt_mul_of_pos_left hx (Nat.two_pow_pos n)
    simpa only [pow_add] using hx'
  have hpow : 2 ^ (n + 8) ≤ 2 ^ 16 := by
    have hle : n + 8 ≤ 16 := by
      omega
    exact Nat.pow_le_pow_of_le (by norm_num) hle
  exact lt_of_lt_of_le hlt hpow

theorem scaled_rhs_val_eq (offset : Fin 8) (low high : F p) (scaled_low_lt : (((2 ^ (8 - offset.val) : F p) * low)).val < 2 ^ 8) (high_lt : high.val < 2 ^ 8) : ((((2 ^ (8 - offset.val) : F p) * low) + high * (2 ^ 8 : F p))).val = (((2 ^ (8 - offset.val) : F p) * low)).val + high.val * 2 ^ 8 := by
  have hpow : ((2 ^ 8 : F p)).val ≤ 2 ^ 8 := by
    rw [two_pow_val 8 (by norm_num)]
  simpa only [two_pow_val 8 (by norm_num), Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Theorems.byteDecomposition_lift
      (low := ((2 ^ (8 - offset.val) : F p) * low))
      (high := high)
      (two_power := (2 ^ 8 : F p))
      scaled_low_lt
      high_lt
      hpow)

theorem scaled_low_lt_implies_low_lt (offset : Fin 8) (x low high : F p) (x_lt : x.val < 2 ^ 8) (scaled_low_lt : (((2 ^ (8 - offset.val) : F p) * low)).val < 2 ^ 8) (high_lt : high.val < 2 ^ 8) (h_eq : x = low + high * 2 ^ offset.val) : low.val < 2 ^ offset.val := by
  let n : ℕ := 8 - offset.val
  have hn : n ≤ 8 := by
    dsimp [n]
    omega
  have hp16 : 2 ^ 16 < p := by
    have hp := p_large_enough.elim
    linarith
  have hoff : n + offset.val = 8 := by
    dsimp [n]
    omega
  have pow_8 : ((2 ^ n : ℕ) : F p) * (2 ^ offset.val : F p) = (2 ^ 8 : F p) := by
    simp [show n + offset.val = 8 by exact hoff, ← pow_add]
  have pow_8_nat : 2 ^ n * 2 ^ offset.val = 2 ^ 8 := by
    simp [show n + offset.val = 8 by exact hoff, ← pow_add]
  have h_eq_mul0 : (2 ^ n : F p) * x =
      (2 ^ n : F p) * low + ((2 ^ n : F p) * (2 ^ offset.val : F p)) * high := by
    rw [h_eq, mul_add]
    ring_nf
  have h_eq_mul : (2 ^ n : F p) * x = (2 ^ n : F p) * low + high * (2 ^ 8 : F p) := by
    calc
      (2 ^ n : F p) * x = (2 ^ n : F p) * low + 2 ^ n * 2 ^ offset.val * high := h_eq_mul0
      _ = (2 ^ n : F p) * low + high * ((2 ^ n : F p) * (2 ^ offset.val : F p)) := by
        ac_rfl
      _ = (2 ^ n : F p) * low + high * (2 ^ 8 : F p) := by
        simpa using congrArg (fun t : F p => (2 ^ n : F p) * low + high * t) pow_8
  have h_eq_val := congrArg ZMod.val h_eq_mul
  have h_lt_mul_x : 2 ^ n * x.val < 2 ^ 16 := by
    exact pow_mul_lt_two_pow_16 n x.val hn x_lt
  have hxval : (((2 ^ n : F p) * x)).val = 2 ^ n * x.val := by
    rw [ZMod.val_mul_of_lt (by
      rw [two_pow_val n hn]
      linarith [h_lt_mul_x, hp16]), two_pow_val n hn]
  have h_rhs : (((2 ^ n : F p) * low) + high * (2 ^ 8 : F p)).val =
      (((2 ^ n : F p) * low)).val + high.val * 2 ^ 8 := by
    simpa [n] using scaled_rhs_val_eq offset low high (by simpa [n] using scaled_low_lt) high_lt
  rw [hxval, h_rhs] at h_eq_val
  have h_eq_nat : 2 ^ n * x.val = (((2 ^ n : F p) * low)).val + 2 ^ n * (high.val * 2 ^ offset.val) := by
    calc
      2 ^ n * x.val = (((2 ^ n : F p) * low)).val + high.val * 2 ^ 8 := h_eq_val
      _ = (((2 ^ n : F p) * low)).val + 2 ^ n * (high.val * 2 ^ offset.val) := by
        rw [← pow_8_nat]
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have h_sub : (((2 ^ n : F p) * low)).val = 2 ^ n * (x.val - high.val * 2 ^ offset.val) := by
    have htmp : (((2 ^ n : F p) * low)).val =
        2 ^ n * x.val - 2 ^ n * (high.val * 2 ^ offset.val) := by
      exact Nat.eq_sub_of_add_eq h_eq_nat.symm
    rw [← Nat.mul_sub_left_distrib] at htmp
    exact htmp
  have h_sub' : (((2 ^ n : ℕ) : F p) * low).val = 2 ^ n * (x.val - high.val * 2 ^ offset.val) := by
    simpa using h_sub
  have h_eq_mul_low' : (((2 ^ n : ℕ) : F p) * low).val = 2 ^ n * low.val := by
    exact FieldUtils.mul_nat_val_of_dvd (x := low) (2 ^ n) (two_pow_lt n hn) h_sub'
  have h_eq_mul_low : (((2 ^ n : F p) * low)).val = 2 ^ n * low.val := by
    simpa using h_eq_mul_low'
  have h_scaled : 2 ^ n * low.val < 2 ^ n * 2 ^ offset.val := by
    have hs : (((2 ^ n : F p) * low)).val < 2 ^ 8 := by
      simpa [n] using scaled_low_lt
    rw [h_eq_mul_low, ← pow_8_nat] at hs
    exact hs
  exact (Nat.mul_lt_mul_left (show 0 < 2 ^ n by exact Nat.pow_pos (by norm_num))).mp h_scaled

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  unfold Soundness
  intro i0 env x_var x h_input x_byte h_holds
  have h_input' : env x_var = x := by
    simpa only [id_eq, circuit_norm] using h_input
  have x_byte' : x.val < 2 ^ 8 := by
    simpa [Assumptions] using x_byte
  let low : F p := env.get i0
  let high : F p := env.get (i0 + 1)
  have h_holds' : (((2 ^ (8 - offset.val) : F p) * low)).val < 2 ^ 8 ∧ high.val < 2 ^ 8 ∧ x = low + high * 2 ^ offset.val := by
    simpa only [circuit_norm, elaborated, main, ByteTable, h_input', low, high] using h_holds
  rcases h_holds' with ⟨scaled_low_lt, high_lt, h_eq⟩
  have h_lt_low : low.val < 2 ^ offset.val :=
    scaled_low_lt_implies_low_lt offset x low high x_byte' scaled_low_lt high_lt h_eq
  have h_sound := Theorems.soundness offset x low high x_byte' h_lt_low high_lt h_eq
  rcases h_sound with ⟨low_eq, high_eq⟩
  have h_high_lt : high.val < 2 ^ (8 - offset.val) := by
    rw [high_eq]
    let n : ℕ := 8 - offset.val
    change x.val / 2 ^ offset.val < 2 ^ n
    rw [Nat.div_lt_iff_lt_mul (by simp)]
    have pow_8_nat : 2 ^ n * 2 ^ offset.val = 2 ^ 8 := by
      simp [n, ← pow_add]
    rwa [pow_8_nat]
  simpa only [Spec, circuit_norm, low, high] using
    (show ((low.val = x.val % 2 ^ offset.val ∧ high.val = x.val / 2 ^ offset.val) ∧
      (low.val < 2 ^ offset.val ∧ high.val < 2 ^ (8 - offset.val))) from
      ⟨⟨low_eq, high_eq⟩, ⟨h_lt_low, h_high_lt⟩⟩)


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
