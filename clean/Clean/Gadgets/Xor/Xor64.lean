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

theorem byte_xor_lookup_complete (x y : F p) : x.val < 256 → y.val < 256 → ByteXorTable.Completeness (x, y, (((x.val ^^^ y.val : ℕ) : F p))) := by
  intro hx hy
  change x.val < 256 ∧ y.val < 256 ∧ ((((x.val ^^^ y.val : ℕ) : F p)).val = x.val ^^^ y.val)
  exact ⟨hx, hy, xor_val hx hy⟩

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env input_var h_env input h_input h_assumptions
  rcases input with ⟨x, y⟩
  cases x
  cases y
  rename_i x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7
  simp only [circuit_norm, explicit_provable_type, main, Assumptions, U64.Normalized] at h_env h_input h_assumptions ⊢
  simp only [Inputs.mk.injEq, U64.mk.injEq] at h_input
  have ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := h_assumptions.left
  have ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩ := h_assumptions.right
  have ⟨hx0_in, hx1_in, hx2_in, hx3_in, hx4_in, hx5_in, hx6_in, hx7_in⟩ := h_input.left
  have ⟨hy0_in, hy1_in, hy2_in, hy3_in, hy4_in, hy5_in, hy6_in, hy7_in⟩ := h_input.right
  have hz0 : env.get offset = (((x0.val ^^^ y0.val : ℕ) : F p)) := by
    simpa only [hx0_in, hy0_in, circuit_norm] using h_env ⟨0, by decide⟩
  have hz1 : env.get (offset + 1) = (((x1.val ^^^ y1.val : ℕ) : F p)) := by
    simpa only [hx1_in, hy1_in, circuit_norm] using h_env ⟨1, by decide⟩
  have hz2 : env.get (offset + 2) = (((x2.val ^^^ y2.val : ℕ) : F p)) := by
    simpa only [hx2_in, hy2_in, circuit_norm] using h_env ⟨2, by decide⟩
  have hz3 : env.get (offset + 3) = (((x3.val ^^^ y3.val : ℕ) : F p)) := by
    simpa only [hx3_in, hy3_in, circuit_norm] using h_env ⟨3, by decide⟩
  have hz4 : env.get (offset + 4) = (((x4.val ^^^ y4.val : ℕ) : F p)) := by
    simpa only [hx4_in, hy4_in, circuit_norm] using h_env ⟨4, by decide⟩
  have hz5 : env.get (offset + 5) = (((x5.val ^^^ y5.val : ℕ) : F p)) := by
    simpa only [hx5_in, hy5_in, circuit_norm] using h_env ⟨5, by decide⟩
  have hz6 : env.get (offset + 6) = (((x6.val ^^^ y6.val : ℕ) : F p)) := by
    simpa only [hx6_in, hy6_in, circuit_norm] using h_env ⟨6, by decide⟩
  have hz7 : env.get (offset + 7) = (((x7.val ^^^ y7.val : ℕ) : F p)) := by
    simpa only [hx7_in, hy7_in, circuit_norm] using h_env ⟨7, by decide⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hx0_in, hy0_in, hz0] using byte_xor_lookup_complete x0 y0 hx0 hy0
  · simpa only [hx1_in, hy1_in, hz1] using byte_xor_lookup_complete x1 y1 hx1 hy1
  · simpa only [hx2_in, hy2_in, hz2] using byte_xor_lookup_complete x2 y2 hx2 hy2
  · simpa only [hx3_in, hy3_in, hz3] using byte_xor_lookup_complete x3 y3 hx3 hy3
  · simpa only [hx4_in, hy4_in, hz4] using byte_xor_lookup_complete x4 y4 hx4 hy4
  · simpa only [hx5_in, hy5_in, hz5] using byte_xor_lookup_complete x5 y5 hx5 hy5
  · simpa only [hx6_in, hy6_in, hz6] using byte_xor_lookup_complete x6 y6 hx6 hy6
  · simpa only [hx7_in, hy7_in, hz7] using byte_xor_lookup_complete x7 y7 hx7 hy7


def circuit : FormalCircuit (F p) Inputs U64 where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Xor64
