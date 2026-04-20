import Clean.Circuit.Basic
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Utils.Primes

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.And.And8
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
  z.val = x.val &&& y.val

def main (input : Var Inputs (F p)) : Circuit (F p) (fieldVar (F p)) := do
  let ⟨x, y⟩ := input
  let and ← witness fun eval => (eval x).val &&& (eval y).val
  -- we prove AND correct using an XOR lookup and the following identity:
  let xor := x + y - 2*and
  lookup ByteXorTable (x, y, xor)
  return and

-- AND / XOR identity that justifies the circuit

theorem and_times_two_add_xor {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x &&& y) + (x ^^^ y) = x + y := by
  -- proof strategy: prove a UInt16 version of the identity using `bv_decide`,
  -- and show that the UInt16 identity is the same as the Nat version since everything is small enough
  let x16 := x.toUInt16
  let y16 := y.toUInt16
  have h_u16 : (2 * (x16 &&& y16) + (x16 ^^^ y16)).toNat = (x16 + y16).toNat := by
    apply congrArg UInt16.toNat
    bv_decide (timeout := 120)

  have hx16 : x.toUInt16.toNat = x := UInt16.toNat_ofNat_of_lt (by linarith)
  have hy16 : y.toUInt16.toNat = y := UInt16.toNat_ofNat_of_lt (by linarith)

  have h_mod_2_to_16 : (2 * (x &&& y) + (x ^^^ y)) % 2^16 = (x + y) % 2^16 := by
    rw [←hx16, ←hy16]
    simp only [x16, y16] at h_u16
    simpa using h_u16

  have h_and_byte : x &&& y < 256 := Nat.and_lt_two_pow (n:=8) x hy
  have h_xor_byte : x ^^^ y < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  have h_lhs : 2 * (x &&& y) + (x ^^^ y) < 2^16 := by linarith
  have h_rhs : x + y < 2^16 := by linarith
  rw [Nat.mod_eq_of_lt h_lhs, Nat.mod_eq_of_lt h_rhs] at h_mod_2_to_16
  exact h_mod_2_to_16

-- corollaries that we also need

theorem xor_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : x ^^^ y ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith

theorem two_and_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x &&& y) ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith

-- some helper lemmas about 2
lemma val_two : (2 : F p).val = 2 := val_lt_p 2 (by linarith [p_large_enough.elim])

lemma two_non_zero : (2 : F p) ≠ 0 := by
  apply_fun ZMod.val
  rw [val_two, ZMod.val_zero]
  trivial

instance elaborated : ElaboratedCircuit (F p) Inputs field where
  main
  localLength _ := 1
  output _ i := var ⟨i⟩

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry

theorem and_nat_cast_val (x y : F p) : x.val < 256 → y.val < 256 → (((x.val &&& y.val : ℕ) : F p).val = x.val &&& y.val) := by
  intro hx hy
  have h_and_byte : x.val &&& y.val < 256 := Nat.and_lt_two_pow (n := 8) x.val hy
  apply val_lt_p
  linarith [h_and_byte, p_large_enough.elim]

theorem xor_lookup_val (x y : F p) : x.val < 256 → y.val < 256 → (x + y - 2 * ((x.val &&& y.val : ℕ) : F p)).val = x.val ^^^ y.val := by
  intro hx hy
  have hp : p > 512 := p_large_enough.out
  have hxy : (x + y).val = x.val + y.val := by
    apply ZMod.val_add_of_lt
    omega
  have hand : (((x.val &&& y.val : ℕ) : F p)).val = x.val &&& y.val := by
    exact and_nat_cast_val x y hx hy
  have hlt_and : x.val &&& y.val < 256 := by
    have hy8 : y.val < 2 ^ 8 := by
      simpa using hy
    have h : x.val &&& y.val < 2 ^ 8 :=
      Nat.and_lt_two_pow x.val (y := y.val) (n := 8) hy8
    simpa using h
  have h2and' :
      (2 * ((x.val &&& y.val : ℕ) : F p)).val
        = (2 : F p).val * (((x.val &&& y.val : ℕ) : F p)).val := by
    apply ZMod.val_mul_of_lt
    rw [val_two, hand]
    omega
  have h2and : (2 * ((x.val &&& y.val : ℕ) : F p)).val = 2 * (x.val &&& y.val) := by
    rw [h2and', val_two, hand]
  have hsub :
      (x + y - 2 * ((x.val &&& y.val : ℕ) : F p)).val
        = (x + y).val - (2 * ((x.val &&& y.val : ℕ) : F p)).val := by
    apply ZMod.val_sub
    rw [hxy, h2and]
    exact two_and_le_add hx hy
  rw [hsub, hxy, h2and]
  rw [← and_times_two_add_xor hx hy]
  omega

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i env input_var h_env input h_input h_assumptions
  rcases input_var with ⟨x_var, y_var⟩
  rcases input with ⟨x, y⟩
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h_input
  rcases h_input with ⟨hx, hy⟩
  simp only [circuit_norm, explicit_provable_type, main, Assumptions, ByteXorTable, hx, hy] at h_env ⊢
  exact ⟨h_assumptions.1, h_assumptions.2, by
    simpa [sub_eq_add_neg, h_env] using xor_lookup_val x y h_assumptions.1 h_assumptions.2⟩


def circuit : FormalCircuit (F p) Inputs field :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.And.And8
