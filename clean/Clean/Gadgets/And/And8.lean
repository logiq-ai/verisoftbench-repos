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

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i env ⟨x_var, y_var⟩ ⟨x, y⟩ h_input h_assumptions h_constraint
  simp_all only [circuit_norm, main, Assumptions, Spec, ByteXorTable, Inputs.mk.injEq]
  have ⟨hx_byte, hy_byte⟩ := h_assumptions
  set w := env.get i
  set xor := x + y + -(2 * w)
  have h_xor : xor.val = x.val ^^^ y.val := by
    simpa [xor] using h_constraint
  have value_goal : w.val = x.val &&& y.val := by
    have hxy : (x + y).val = x.val + y.val := by
      field_to_nat
    have h_xor_le : xor.val ≤ (x + y).val := by
      rw [h_xor, hxy]
      exact xor_le_add hx_byte hy_byte
    have h_sub : (x + y - xor).val = (x + y).val - xor.val := ZMod.val_sub h_xor_le
    have h_field : x + y - xor = 2 * w := by
      ring
    rw [h_field, hxy, h_xor] at h_sub
    have h_two_w : (2 * w).val = 2 * (x.val &&& y.val) := by
      have h_id := and_times_two_add_xor hx_byte hy_byte
      omega
    have h_mul : (2 * w).val = 2 * w.val :=
      FieldUtils.mul_nat_val_of_dvd 2 (by linarith [p_large_enough.elim]) h_two_w
    rw [h_mul] at h_two_w
    omega
  simpa using value_goal


theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs field :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.And.And8
