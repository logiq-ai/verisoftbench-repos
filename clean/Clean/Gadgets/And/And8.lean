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

theorem xor_val_of_and_witness (x y w : F p) : x.val < 256 → y.val < 256 → w.val = x.val &&& y.val → (x + y - 2 * w).val = x.val ^^^ y.val := by
  intro hx hy hw
  have hxy : (x + y).val = x.val + y.val := by
    field_to_nat
  have handlt : x.val &&& y.val < 256 := by
    exact Nat.and_lt_two_pow (n := 8) x.val hy
  have h2wlt : (2 : F p).val * w.val < p := by
    rw [val_two, hw]
    have hp : p > 512 := p_large_enough.elim
    omega
  have h2w : (2 * w).val = 2 * (x.val &&& y.val) := by
    have hmul : (2 * w).val = (2 : F p).val * w.val := by
      exact ZMod.val_mul_of_lt h2wlt
    rw [hmul, val_two, hw]
  have hle : (2 * w).val ≤ (x + y).val := by
    rw [hxy, h2w]
    exact two_and_le_add hx hy
  rw [ZMod.val_sub hle, hxy, h2w]
  have hmain := and_times_two_add_xor hx hy
  omega

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env input_var h_env input h_input h_assumptions
  cases input with
  | mk x y =>
      simp only [circuit_norm, explicit_provable_type, main, Assumptions] at h_env h_input h_assumptions ⊢
      simp only [Inputs.mk.injEq] at h_input
      rcases h_input with ⟨hx_eq, hy_eq⟩
      subst x
      subst y
      simp only [ByteXorTable, circuit_norm]
      refine ⟨h_assumptions.1, h_assumptions.2, ?_⟩
      have hx : (Expression.eval env input_var.x).val < 256 := h_assumptions.1
      have hy : (Expression.eval env input_var.y).val < 256 := h_assumptions.2
      have hwval : (env.get offset).val = (Expression.eval env input_var.x).val &&& (Expression.eval env input_var.y).val := by
        have hwcast := h_env
        apply congrArg ZMod.val at hwcast
        have handlt : (Expression.eval env input_var.x).val &&& (Expression.eval env input_var.y).val < 256 := by
          exact Nat.and_lt_two_pow (n := 8) (Expression.eval env input_var.x).val hy
        have hp256 : 256 < p := by
          linarith [p_large_enough.elim]
        rw [FieldUtils.val_lt_p ((Expression.eval env input_var.x).val &&& (Expression.eval env input_var.y).val) (lt_trans handlt hp256)] at hwcast
        exact hwcast
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        xor_val_of_and_witness (Expression.eval env input_var.x) (Expression.eval env input_var.y) (env.get offset) hx hy hwval


def circuit : FormalCircuit (F p) Inputs field :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.And.And8
