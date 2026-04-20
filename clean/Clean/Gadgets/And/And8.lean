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

theorem double_output_val_from_lookup {x y a : F p} (hx : x.val < 256) (hy : y.val < 256)
  (hlookup : (x + y - 2 * a).val = x.val ^^^ y.val) :
  (2 * a).val = 2 * (x.val &&& y.val) := by
  let xorNat := x.val ^^^ y.val
  have xor_lt_p : xorNat < p := by
    have hxor_byte : xorNat < 256 := Nat.xor_lt_two_pow (n := 8) hx hy
    linarith [p_large_enough.elim]
  let xorF : F p := natToField xorNat xor_lt_p
  have xorF_val : xorF.val = xorNat := by
    simpa [xorF] using (FieldUtils.val_of_natToField_eq (p := p) xor_lt_p)
  have hfield : x + y - 2 * a = xorF := by
    apply FieldUtils.ext
    rw [hlookup, xorF_val]
  have htwo : 2 * a = x + y - xorF := by
    calc
      2 * a = x + y - (x + y - 2 * a) := by ring
      _ = x + y - xorF := by rw [hfield]
  have hsum_val : (x + y).val = x.val + y.val := by
    exact ByteUtils.byte_sum_do_not_wrap x y hx hy
  have hxor_le_sum : xorF.val ≤ (x + y).val := by
    rw [hsum_val, xorF_val]
    exact xor_le_add hx hy
  calc
    (2 * a).val = (x + y - xorF).val := by
      exact congrArg ZMod.val htwo
    _ = (x + y).val - xorF.val := by
      exact ZMod.val_sub hxor_le_sum
    _ = x.val + y.val - (x.val ^^^ y.val) := by
      rw [hsum_val, xorF_val]
    _ = 2 * (x.val &&& y.val) := by
      rw [←and_times_two_add_xor hx hy, Nat.add_sub_cancel]

theorem output_val_from_lookup {x y a : F p} (hx : x.val < 256) (hy : y.val < 256)
  (hlookup : (x + y - 2 * a).val = x.val ^^^ y.val) :
  a.val = x.val &&& y.val := by
  have hdouble : (2 * a).val = 2 * (x.val &&& y.val) :=
    double_output_val_from_lookup hx hy hlookup
  have hmul : (2 * a).val = 2 * a.val :=
    mul_nat_val_of_dvd 2 (by linarith [p_large_enough.elim]) hdouble
  have hEq : 2 * a.val = 2 * (x.val &&& y.val) := by
    rw [←hmul]
    exact hdouble
  exact Nat.mul_left_cancel (show 0 < 2 by decide) hEq

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i env input_var input h_input h_as h_holds
  let ⟨x_var, y_var⟩ := input_var
  let ⟨x, y⟩ := input
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h_input
  simp only [circuit_norm, Assumptions] at h_as
  simp only [h_input, circuit_norm, main, ByteXorTable, Vector.mapRange] at h_holds
  have hlookup : (x + y - 2 * env.get i).val = x.val ^^^ y.val := by
    simpa [sub_eq_add_neg] using h_holds.2.2
  simp only [circuit_norm, Spec]
  exact output_val_from_lookup h_as.1 h_as.2 hlookup


theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs field :=
  { Assumptions, Spec, soundness, completeness }

end Gadgets.And.And8
