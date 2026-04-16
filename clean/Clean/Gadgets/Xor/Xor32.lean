import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U32
import Clean.Gadgets.Xor.ByteXorTable

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Xor32
open Gadgets.Xor

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableStruct Inputs where
  components := [U32, U32]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p))  := do
  let ⟨x, y⟩ := input
  let z ← witness fun env =>
    let z0 := (env x.x0).val ^^^ (env y.x0).val
    let z1 := (env x.x1).val ^^^ (env y.x1).val
    let z2 := (env x.x2).val ^^^ (env y.x2).val
    let z3 := (env x.x3).val ^^^ (env y.x3).val
    U32.mk z0 z1 z2 z3

  lookup ByteXorTable (x.x0, y.x0, z.x0)
  lookup ByteXorTable (x.x1, y.x1, z.x1)
  lookup ByteXorTable (x.x2, y.x2, z.x2)
  lookup ByteXorTable (x.x3, y.x3, z.x3)
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ^^^ y.value ∧ z.Normalized

instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main := main
  localLength _ := 4
  output _ i0 := varFromOffset U32 i0

omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u32 {x y z : U32 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val ^^^ y.x0.val ∧
    z.x1.val = x.x1.val ^^^ y.x1.val ∧
    z.x2.val = x.x2.val ^^^ y.x2.val ∧
    z.x3.val = x.x3.val ^^^ y.x3.val) : Spec { x, y } z := by
  simp only [Spec]
  have ⟨ hx0, hx1, hx2, hx3 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3 ⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U32.Normalized, h_eq]
    exact ⟨ Nat.xor_lt_two_pow (n:=8) hx0 hy0, Nat.xor_lt_two_pow (n:=8) hx1 hy1,
      Nat.xor_lt_two_pow (n:=8) hx2 hy2, Nat.xor_lt_two_pow (n:=8) hx3 hy3 ⟩

  suffices z.value = x.value ^^^ y.value from ⟨ this, z_norm ⟩
  simp only [U32.value_xor_horner, x_norm, y_norm, z_norm, h_eq, xor_mul_two_pow]
  ac_rfl

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env input_var input h_input h_as h_holds

  let ⟨⟨ x0_var, x1_var, x2_var, x3_var ⟩,
       ⟨ y0_var, y1_var, y2_var, y3_var ⟩⟩ := input_var
  let ⟨⟨ x0, x1, x2, x3 ⟩,
       ⟨ y0, y1, y2, y3 ⟩⟩ := input

  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq, U32.mk.injEq] at h_input

  simp only [circuit_norm, Assumptions] at h_as
  obtain ⟨ x_norm, y_norm ⟩ := h_as

  simp only [h_input, circuit_norm, main, ByteXorTable,
    varFromOffset, Vector.mapRange] at h_holds

  apply soundness_to_u32 (by simp [circuit_norm, x_norm]) (by simp [circuit_norm, y_norm])
  simp only [circuit_norm, explicit_provable_type]
  simp [h_holds]

lemma xor_val {x y : F p} (hx : x.val < 256) (hy : y.val < 256) :
  (x.val ^^^ y.val : F p).val = x.val ^^^ y.val := by
  apply FieldUtils.val_lt_p
  have h_byte : x.val ^^^ y.val < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  linarith [p_large_enough.elim]

theorem byte_xor_lookup_complete {x y : F p} : x.val < 256 → y.val < 256 → ByteXorTable.Completeness (x, y, (((x.val ^^^ y.val : ℕ)) : F p)) := by
  intro hx hy
  simp only [ByteXorTable, Table.fromStatic, StaticTable.toTable]
  exact ⟨hx, hy, xor_val hx hy⟩

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env input_var h_env input h_input h_assumptions
  rcases input with ⟨x, y⟩
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq, U32.mk.injEq] at h_input
  simp only [circuit_norm, Assumptions, U32.Normalized] at h_assumptions
  simp only [h_input, circuit_norm, elaborated, main, ByteXorTable, varFromOffset, Vector.mapRange] at h_env ⊢
  rcases h_assumptions with ⟨hx, hy0, hy1, hy2, hy3⟩
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  have h0 := h_env (i := ⟨0, by decide⟩)
  have h1 := h_env (i := ⟨1, by decide⟩)
  have h2 := h_env (i := ⟨2, by decide⟩)
  have h3 := h_env (i := ⟨3, by decide⟩)
  have h0' : env.get i0 = (((x0.val ^^^ y0.val : ℕ)) : F p) := by
    simpa using h0
  have h1' : env.get (i0 + 1) = (((x1.val ^^^ y1.val : ℕ)) : F p) := by
    simpa using h1
  have h2' : env.get (i0 + 2) = (((x2.val ^^^ y2.val : ℕ)) : F p) := by
    simpa using h2
  have h3' : env.get (i0 + 3) = (((x3.val ^^^ y3.val : ℕ)) : F p) := by
    simpa using h3
  have hz0 : ZMod.val (env.get i0) = ZMod.val x0 ^^^ ZMod.val y0 := by
    rw [h0']
    exact xor_val hx0 hy0
  have hz1 : ZMod.val (env.get (i0 + 1)) = ZMod.val x1 ^^^ ZMod.val y1 := by
    rw [h1']
    exact xor_val hx1 hy1
  have hz2 : ZMod.val (env.get (i0 + 2)) = ZMod.val x2 ^^^ ZMod.val y2 := by
    rw [h2']
    exact xor_val hx2 hy2
  have hz3 : ZMod.val (env.get (i0 + 3)) = ZMod.val x3 ^^^ ZMod.val y3 := by
    rw [h3']
    exact xor_val hx3 hy3
  exact ⟨⟨hx0, hy0, hz0⟩, ⟨hx1, hy1, hz1⟩, ⟨hx2, hy2, hz2⟩, hx3, hy3, hz3⟩


def circuit : FormalCircuit (F p) Inputs U32 where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Xor32
