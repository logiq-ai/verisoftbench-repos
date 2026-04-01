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

theorem and_xor_field_identity (x y : F p) (hx : x.val < 256) (hy : y.val < 256) : x + y - 2 * (((x.val &&& y.val : ℕ) : F p)) = (((x.val ^^^ y.val : ℕ) : F p)) := by
  have hx' : (ZMod.cast x : F p) = x := by
    simpa [F] using (ZMod.cast_id p x)
  have hy' : (ZMod.cast y : F p) = y := by
    simpa [F] using (ZMod.cast_id p y)
  have hnat := and_times_two_add_xor hx hy
  have hcast' : (2 : F p) * (((x.val &&& y.val : ℕ) : F p)) + (((x.val ^^^ y.val : ℕ) : F p)) = (ZMod.cast x + ZMod.cast y : F p) := by
    simpa [Nat.cast_add, Nat.cast_mul] using
      (congrArg (fun n : ℕ => (n : F p)) hnat)
  rw [hx', hy'] at hcast'
  exact (sub_eq_iff_eq_add).2 (by simpa [add_comm, add_left_comm, add_assoc] using hcast'.symm)

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env input_var hUses input hEval hAssumptions
  rcases input_var with ⟨x_var, y_var⟩
  rcases input with ⟨x, y⟩
  simp only [circuit_norm, explicit_provable_type, main, Assumptions, ByteXorTable, Inputs.mk.injEq] at hUses hEval hAssumptions ⊢
  rcases hEval with ⟨hx_eval, hy_eval⟩
  simp only [hx_eval, hy_eval] at hUses ⊢
  rcases hAssumptions with ⟨hx, hy⟩
  refine ⟨hx, hy, ?_⟩
  rw [hUses]
  have h_id := and_xor_field_identity (x := x) (y := y) hx hy
  have h_val := congrArg ZMod.val h_id
  have hxor_lt : ZMod.val x ^^^ ZMod.val y < p := by
    have hxor_byte : ZMod.val x ^^^ ZMod.val y < 256 := Nat.xor_lt_two_pow (n := 8) hx hy
    linarith [p_large_enough.elim]
  rw [FieldUtils.val_lt_p _ hxor_lt] at h_val
  simpa [sub_eq_add_neg] using h_val


def circuit : FormalCircuit (F p) Inputs field :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.And.And8
