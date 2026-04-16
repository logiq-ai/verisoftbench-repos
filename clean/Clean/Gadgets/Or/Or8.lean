import Clean.Circuit.Basic
import Clean.Gadgets.Xor.ByteXorTable

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Or.Or8
open Xor (ByteXorTable)
open FieldUtils

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableStruct Inputs where
  components := [field, field]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

def Spec (input : Inputs (F p)) (z : F p) :=
  let ⟨x, y⟩ := input
  z.val = x.val ||| y.val ∧ z.val < 256

def main (input : Var Inputs (F p)) : Circuit (F p) (fieldVar (F p)) := do
  let ⟨x, y⟩ := input
  let or ← witness fun eval => (eval x).val ||| (eval y).val
  -- we prove OR correct using an XOR lookup
  let xor := 2*or - x - y
  lookup ByteXorTable (x, y, xor)
  return or

-- OR / XOR identity that justifies the circuit
private theorem or_times_two_sub_xor {x y : ℕ} (hx : x < 256) (hy : y < 256) :
    2 * (x ||| y) = x + y + (x ^^^ y) := by
  -- proof strategy: prove a UInt16 version of the identity using `bv_decide`,
  -- and show that the UInt16 identity is the same as the Nat version since everything is small enough
  let x16 := x.toUInt16
  let y16 := y.toUInt16
  have h_u16 : (2 * (x16 ||| y16)).toNat = (x16 + y16 + (x16 ^^^ y16)).toNat := by
    apply congrArg UInt16.toNat
    bv_decide (timeout := 120)

  have hx16 : x.toUInt16.toNat = x := UInt16.toNat_ofNat_of_lt (by linarith)
  have hy16 : y.toUInt16.toNat = y := UInt16.toNat_ofNat_of_lt (by linarith)
  have h_or_byte : x ||| y < 256 := Nat.or_lt_two_pow (n:=8) hx hy
  have h_xor_byte : x ^^^ y < 256 := Nat.xor_lt_two_pow (n:=8) hx hy

  have h_mod_2_to_16 : (2 * (x ||| y)) % 2^16 = (x + y + (x ^^^ y)) % 2^16 := by
    conv_lhs => rw [←hx16, ←hy16]
    conv_rhs => rw [←hx16, ←hy16]
    simp only [x16, y16] at h_u16
    simp only [← UInt16.toNat_or]
    norm_num at h_u16 ⊢
    repeat rw [Nat.mod_eq_of_lt] <;> try omega
    · repeat rw [Nat.mod_eq_of_lt] at h_u16 <;> try omega
      · simpa
      · repeat rw [Nat.mod_eq_of_lt] <;> try omega
        simp only [UInt16.toNat, UInt16.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
    · repeat rw [Nat.mod_eq_of_lt] <;> try omega

  have h_lhs : 2 * (x ||| y) < 2^16 := by linarith
  have h_rhs : x + y + (x ^^^ y) < 2^16 := by linarith
  rw [Nat.mod_eq_of_lt h_lhs, Nat.mod_eq_of_lt h_rhs] at h_mod_2_to_16
  exact h_mod_2_to_16

private theorem or_times_two_sub_xor' {x y : ℕ} (hx : x < 256) (hy : y < 256) :
    2 * (x ||| y) - x - y = (x ^^^ y) := by
  have := or_times_two_sub_xor hx hy
  omega

-- corollaries that we also need

private theorem two_or_ge_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x ||| y) ≥ x + y := by
  have h := or_times_two_sub_xor hx hy
  linarith

-- some helper lemmas about 2
lemma val_two : (2 : F p).val = 2 := val_lt_p 2 (by linarith [p_large_enough.elim])

lemma two_non_zero : (2 : F p) ≠ 0 := by
  apply_fun ZMod.val
  rw [val_two, ZMod.val_zero]
  trivial

instance elaborated : ElaboratedCircuit (F p) Inputs field where
  main
  localLength _ := 1

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i env ⟨ x_var, y_var ⟩ ⟨ x, y ⟩ h_input h_assumptions h_constraint
  simp_all only [circuit_norm, main, Assumptions, Spec, ByteXorTable, Inputs.mk.injEq]
  have ⟨ hx_byte, hy_byte ⟩ := h_assumptions
  set w := env.get i
  -- The constraint from lookup is about xor = 2*or - x - y
  -- which in field arithmetic is 2*w + -x + -y
  set xor := 2*w + -x + -y
  have h_xor : xor.val = x.val ^^^ y.val := h_constraint
  have value_goal : w.val = x.val ||| y.val := by
    have two_or_field : 2*w = x + y + xor := by ring
    have x_y_val : (x + y).val = x.val + y.val := by field_to_nat
    have x_y_xor_val : (x + y + xor).val = x.val + y.val + (x.val ^^^ y.val) := by
      -- The key insight: from 2*(x ||| y) = x + y + (x ^^^ y), we get
      -- x + y + (x ^^^ y) = 2*(x ||| y) ≤ 2*255 = 510 < 512 < p
      have sum_bound : (x + y).val + xor.val < p := by
        rw [x_y_val, h_xor]
        have : x.val + y.val + (x.val ^^^ y.val) ≤ 2 * 255 := by
          have h := or_times_two_sub_xor hx_byte hy_byte
          have or_le : x.val ||| y.val ≤ 255 := by
            have : x.val ||| y.val < 256 := Nat.or_lt_two_pow (n:=8) hx_byte hy_byte
            omega
          linarith
        have := p_large_enough.elim
        omega

      rw [ZMod.val_add_of_lt sum_bound, x_y_val, h_xor]

    have two_or : (2*w).val = 2*(x.val ||| y.val) := by
      rw [two_or_field, x_y_xor_val, or_times_two_sub_xor hx_byte hy_byte]
    have two_mul_val : (2*w).val = 2*w.val := FieldUtils.mul_nat_val_of_dvd 2
      (by linarith [p_large_enough.elim]) two_or
    rw [two_mul_val] at two_or
    omega
  constructor
  · assumption
  simp only [value_goal]
  show Nat.bitwise _ _ _ < 2 ^ 8
  exact Nat.bitwise_lt_two_pow hx_byte hy_byte

theorem or_witness_xor_val {x y : F p} (hx : x.val < 256) (hy : y.val < 256) : ((2 * (((x.val ||| y.val : ℕ) : F p)) - x - y : F p)).val = x.val ^^^ y.val := by
  let o : ℕ := x.val ||| y.val
  have ho_byte : o < 256 := by
    simpa only [o] using (Nat.or_lt_two_pow (n := 8) hx hy)
  have hp : 512 < p := p_large_enough.elim
  have ho_p : o < p := by
    omega
  have h_two_o_lt : 2 * o < p := by
    omega
  have h_mul : (2 * (((o : ℕ) : F p))).val = 2 * o := by
    rw [ZMod.val_mul_of_lt]
    · rw [val_two, ZMod.val_cast_of_lt ho_p]
    · rw [val_two, ZMod.val_cast_of_lt ho_p]
      exact h_two_o_lt
  have h_sub1 : ((2 * (((o : ℕ) : F p)) - x : F p)).val = 2 * o - x.val := by
    rw [ZMod.val_sub]
    · rw [h_mul]
    · rw [h_mul]
      have h_ge : 2 * o ≥ x.val + y.val := by
        simpa only [o] using (two_or_ge_add hx hy)
      omega
  have h_sub2 : ((2 * (((o : ℕ) : F p)) - x - y : F p)).val = 2 * o - x.val - y.val := by
    rw [ZMod.val_sub]
    · rw [h_sub1]
    · rw [h_sub1]
      have h_ge : 2 * o ≥ x.val + y.val := by
        simpa only [o] using (two_or_ge_add hx hy)
      omega
  rw [h_sub2]
  simpa only [o] using (or_times_two_sub_xor' hx hy)

theorem completeness : Completeness (F p) elaborated Assumptions := by
  unfold Completeness
  intro i₀ env input_var h_env input h_input h_assumptions
  rcases input_var with ⟨x_var, y_var⟩
  rcases input with ⟨x, y⟩
  simp only [Assumptions] at h_assumptions
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h_input ⊢
  simp only [circuit_norm, main, ByteXorTable, h_input] at h_env ⊢
  rcases h_assumptions with ⟨hx, hy⟩
  have h_w : env.get i₀ = (((x).val ||| (y).val : ℕ) : F p) := by
    simpa using h_env
  exact ⟨hx, hy, by simpa [h_w, sub_eq_add_neg, add_assoc] using or_witness_xor_val (x := x) (y := y) hx hy⟩


def circuit : FormalCircuit (F p) Inputs field :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.Or.Or8
