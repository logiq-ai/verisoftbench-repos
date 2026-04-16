import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable

import Clean.Utils.Tactics
section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Xor64
open Gadgets.Xor

structure Inputs (F : Type) where
  x: U64 F
  y: U64 F

instance : ProvableStruct Inputs where
  components := [U64, U64]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U64 (F p))  := do
  let ⟨x, y⟩ := input
  let z ← witness fun env =>
    let z0 := (env x.x0).val ^^^ (env y.x0).val
    let z1 := (env x.x1).val ^^^ (env y.x1).val
    let z2 := (env x.x2).val ^^^ (env y.x2).val
    let z3 := (env x.x3).val ^^^ (env y.x3).val
    let z4 := (env x.x4).val ^^^ (env y.x4).val
    let z5 := (env x.x5).val ^^^ (env y.x5).val
    let z6 := (env x.x6).val ^^^ (env y.x6).val
    let z7 := (env x.x7).val ^^^ (env y.x7).val
    U64.mk z0 z1 z2 z3 z4 z5 z6 z7

  lookup ByteXorTable (x.x0, y.x0, z.x0)
  lookup ByteXorTable (x.x1, y.x1, z.x1)
  lookup ByteXorTable (x.x2, y.x2, z.x2)
  lookup ByteXorTable (x.x3, y.x3, z.x3)
  lookup ByteXorTable (x.x4, y.x4, z.x4)
  lookup ByteXorTable (x.x5, y.x5, z.x5)
  lookup ByteXorTable (x.x6, y.x6, z.x6)
  lookup ByteXorTable (x.x7, y.x7, z.x7)
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U64 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ^^^ y.value ∧ z.Normalized

instance elaborated : ElaboratedCircuit (F p) Inputs U64 where
  main := main
  localLength _ := 8
  output _ i0 := varFromOffset U64 i0

omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u64 {x y z : U64 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val ^^^ y.x0.val ∧
    z.x1.val = x.x1.val ^^^ y.x1.val ∧
    z.x2.val = x.x2.val ^^^ y.x2.val ∧
    z.x3.val = x.x3.val ^^^ y.x3.val ∧
    z.x4.val = x.x4.val ^^^ y.x4.val ∧
    z.x5.val = x.x5.val ^^^ y.x5.val ∧
    z.x6.val = x.x6.val ^^^ y.x6.val ∧
    z.x7.val = x.x7.val ^^^ y.x7.val) : Spec { x, y } z := by
  simp only [Spec]
  have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7 ⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U64.Normalized, h_eq]
    exact ⟨ Nat.xor_lt_two_pow (n:=8) hx0 hy0, Nat.xor_lt_two_pow (n:=8) hx1 hy1,
      Nat.xor_lt_two_pow (n:=8) hx2 hy2, Nat.xor_lt_two_pow (n:=8) hx3 hy3,
      Nat.xor_lt_two_pow (n:=8) hx4 hy4, Nat.xor_lt_two_pow (n:=8) hx5 hy5,
      Nat.xor_lt_two_pow (n:=8) hx6 hy6, Nat.xor_lt_two_pow (n:=8) hx7 hy7 ⟩

  suffices z.value = x.value ^^^ y.value from ⟨ this, z_norm ⟩
  simp only [U64.value_xor_horner, x_norm, y_norm, z_norm, h_eq, xor_mul_two_pow]
  ac_rfl

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry

lemma xor_val {x y : F p} (hx : x.val < 256) (hy : y.val < 256) :
    (x.val ^^^ y.val : F p).val = x.val ^^^ y.val := by
  apply FieldUtils.val_lt_p
  have h_byte : x.val ^^^ y.val < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  linarith [p_large_enough.elim]

theorem byte_xor_lookup_complete: ∀ {x y z : F p}, x.val < 256 → y.val < 256 → z = (x.val ^^^ y.val : F p) → ByteXorTable.Completeness (x, y, z) := by
  intro x y z hx hy hz
  simp only [circuit_norm, ByteXorTable, hz, hx, hy, xor_val hx hy]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  rcases input_x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  rcases input_y with ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩
  rcases h_input with ⟨hxin, hyin⟩
  rcases h_assumptions with ⟨hxnorm, hynorm⟩
  simp only [U64.Normalized] at hxnorm hynorm
  rcases hxnorm with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  rcases hynorm with ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩
  have hxin0 : Expression.eval env input_var_x.x0 = x0 := by
    simpa [circuit_norm] using congrArg U64.x0 hxin
  have hxin1 : Expression.eval env input_var_x.x1 = x1 := by
    simpa [circuit_norm] using congrArg U64.x1 hxin
  have hxin2 : Expression.eval env input_var_x.x2 = x2 := by
    simpa [circuit_norm] using congrArg U64.x2 hxin
  have hxin3 : Expression.eval env input_var_x.x3 = x3 := by
    simpa [circuit_norm] using congrArg U64.x3 hxin
  have hxin4 : Expression.eval env input_var_x.x4 = x4 := by
    simpa [circuit_norm] using congrArg U64.x4 hxin
  have hxin5 : Expression.eval env input_var_x.x5 = x5 := by
    simpa [circuit_norm] using congrArg U64.x5 hxin
  have hxin6 : Expression.eval env input_var_x.x6 = x6 := by
    simpa [circuit_norm] using congrArg U64.x6 hxin
  have hxin7 : Expression.eval env input_var_x.x7 = x7 := by
    simpa [circuit_norm] using congrArg U64.x7 hxin
  have hyin0 : Expression.eval env input_var_y.x0 = y0 := by
    simpa [circuit_norm] using congrArg U64.x0 hyin
  have hyin1 : Expression.eval env input_var_y.x1 = y1 := by
    simpa [circuit_norm] using congrArg U64.x1 hyin
  have hyin2 : Expression.eval env input_var_y.x2 = y2 := by
    simpa [circuit_norm] using congrArg U64.x2 hyin
  have hyin3 : Expression.eval env input_var_y.x3 = y3 := by
    simpa [circuit_norm] using congrArg U64.x3 hyin
  have hyin4 : Expression.eval env input_var_y.x4 = y4 := by
    simpa [circuit_norm] using congrArg U64.x4 hyin
  have hyin5 : Expression.eval env input_var_y.x5 = y5 := by
    simpa [circuit_norm] using congrArg U64.x5 hyin
  have hyin6 : Expression.eval env input_var_y.x6 = y6 := by
    simpa [circuit_norm] using congrArg U64.x6 hyin
  have hyin7 : Expression.eval env input_var_y.x7 = y7 := by
    simpa [circuit_norm] using congrArg U64.x7 hyin
  simp only [circuit_norm, explicit_provable_type, hxin0, hxin1, hxin2, hxin3, hxin4, hxin5, hxin6, hxin7,
    hyin0, hyin1, hyin2, hyin3, hyin4, hyin5, hyin6, hyin7] at ⊢
  have hz0 : env.get i₀ = (x0.val ^^^ y0.val : F p) := by
    simpa [hxin0, hyin0, explicit_provable_type] using (h_env ⟨0, by decide⟩)
  have hz1 : env.get (i₀ + 1) = (x1.val ^^^ y1.val : F p) := by
    simpa [hxin1, hyin1, explicit_provable_type] using (h_env ⟨1, by decide⟩)
  have hz2 : env.get (i₀ + 2) = (x2.val ^^^ y2.val : F p) := by
    simpa [hxin2, hyin2, explicit_provable_type] using (h_env ⟨2, by decide⟩)
  have hz3 : env.get (i₀ + 3) = (x3.val ^^^ y3.val : F p) := by
    simpa [hxin3, hyin3, explicit_provable_type] using (h_env ⟨3, by decide⟩)
  have hz4 : env.get (i₀ + 4) = (x4.val ^^^ y4.val : F p) := by
    simpa [hxin4, hyin4, explicit_provable_type] using (h_env ⟨4, by decide⟩)
  have hz5 : env.get (i₀ + 5) = (x5.val ^^^ y5.val : F p) := by
    simpa [hxin5, hyin5, explicit_provable_type] using (h_env ⟨5, by decide⟩)
  have hz6 : env.get (i₀ + 6) = (x6.val ^^^ y6.val : F p) := by
    simpa [hxin6, hyin6, explicit_provable_type] using (h_env ⟨6, by decide⟩)
  have hz7 : env.get (i₀ + 7) = (x7.val ^^^ y7.val : F p) := by
    simpa [hxin7, hyin7, explicit_provable_type] using (h_env ⟨7, by decide⟩)
  exact ⟨
    by simpa [hxin0, hyin0] using (byte_xor_lookup_complete (x := x0) (y := y0) (z := env.get i₀) hx0 hy0 hz0),
    by simpa [hxin1, hyin1] using (byte_xor_lookup_complete (x := x1) (y := y1) (z := env.get (i₀ + 1)) hx1 hy1 hz1),
    by simpa [hxin2, hyin2] using (byte_xor_lookup_complete (x := x2) (y := y2) (z := env.get (i₀ + 2)) hx2 hy2 hz2),
    by simpa [hxin3, hyin3] using (byte_xor_lookup_complete (x := x3) (y := y3) (z := env.get (i₀ + 3)) hx3 hy3 hz3),
    by simpa [hxin4, hyin4] using (byte_xor_lookup_complete (x := x4) (y := y4) (z := env.get (i₀ + 4)) hx4 hy4 hz4),
    by simpa [hxin5, hyin5] using (byte_xor_lookup_complete (x := x5) (y := y5) (z := env.get (i₀ + 5)) hx5 hy5 hz5),
    by simpa [hxin6, hyin6] using (byte_xor_lookup_complete (x := x6) (y := y6) (z := env.get (i₀ + 6)) hx6 hy6 hz6),
    by simpa [hxin7, hyin7] using (byte_xor_lookup_complete (x := x7) (y := y7) (z := env.get (i₀ + 7)) hx7 hy7 hz7)
  ⟩


def circuit : FormalCircuit (F p) Inputs U64 where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Xor64
