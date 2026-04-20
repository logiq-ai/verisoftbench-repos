import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Theorems
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Equality
import Clean.Types.U32

namespace Tables.Fibonacci32
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def fib32 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib32 n + fib32 (n + 1)) % 2^32

/--
  The row type for fib32 are two U32 values
-/
structure RowType (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableStruct RowType where
  components := [U32, U32]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }
  combinedSize := 8 -- explicit size to enable casting indices to `Fin size`

@[reducible]
def nextRowOff : RowType (CellOffset 2 RowType) := {
  x := ⟨.next 0, .next 1, .next 2, .next 3⟩,
  y := ⟨.next 4, .next 5, .next 6, .next 7⟩
}

def assignU32 (offs : U32 (CellOffset 2 RowType)) (x : Var U32 (F p)) : TwoRowsConstraint RowType (F p) := do
  assign offs.x0 x.x0
  assign offs.x1 x.x1
  assign offs.x2 x.x2
  assign offs.x3 x.x3

/--
  inductive contraints that are applied every two rows of the trace.
-/
def recursiveRelation : TwoRowsConstraint RowType (F p) := do
  let curr ← TableConstraint.getCurrRow
  let next ← TableConstraint.getNextRow

  let z ← Gadgets.Addition32.circuit { x := curr.x, y := curr.y }

  assignU32 nextRowOff.y z
  curr.y === next.x

/--
  Boundary constraints that are applied at the beginning of the trace.
-/
def boundary : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.getCurrRow
  row.x === (const (U32.fromByte 0))
  row.y === (const (U32.fromByte 1))

/--
  The fib32 table is composed of the boundary and recursive relation constraints.
-/
def fib32Table : List (TableOperation RowType (F p)) := [
  .boundary (.fromStart 0) boundary,
  .everyRowExceptLast recursiveRelation,
]

/--
  Specification for fibonacci32: for each row with index i
  - the first U32 value is the i-th fibonacci number
  - the second U32 value is the (i+1)-th fibonacci number
  - both U32 values are normalized
-/
def Spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.ForAllRowsOfTraceWithIndex fun row index =>
    (row.x.value = fib32 index) ∧
    (row.y.value = fib32 (index + 1)) ∧
    row.x.Normalized ∧ row.y.Normalized

/-
  First of all, we prove some lemmas about the mapping variables -> cell offsets
  for both boundary and recursive relation
  Those are too expensive to prove in-line, so we prove them here and use them later
-/

variable {α : Type}

-- assignment copied from eval:
-- #eval! (recursive_relation (p:=p_babybear)).finalAssignment.vars
lemma fib_assignment : (recursiveRelation (p:=p)).finalAssignment.vars =
   #v[.input ⟨0, 0⟩, .input ⟨0, 1⟩, .input ⟨0, 2⟩, .input ⟨0, 3⟩, .input ⟨0, 4⟩, .input ⟨0, 5⟩, .input ⟨0, 6⟩,
      .input ⟨0, 7⟩, .input ⟨1, 0⟩, .input ⟨1, 1⟩, .input ⟨1, 2⟩, .input ⟨1, 3⟩, .input ⟨1, 4⟩, .input ⟨1, 5⟩,
      .input ⟨1, 6⟩, .input ⟨1, 7⟩, .input ⟨1, 4⟩, .aux 1, .input ⟨1, 5⟩, .aux 3, .input ⟨1, 6⟩, .aux 5,
      .input ⟨1, 7⟩, .aux 7] := by
  dsimp only [table_assignment_norm, circuit_norm, recursiveRelation, Gadgets.Addition32.circuit, assignU32]
  simp only [circuit_norm, Vector.mapFinRange_succ, Vector.mapFinRange_zero,
    Vector.mapRange_zero, Vector.mapRange_succ]
  simp

lemma fib_vars (curr next : Row (F p) RowType) (aux_env : Environment (F p)) :
    let env := recursiveRelation.windowEnv ⟨<+> +> curr +> next, rfl⟩ aux_env;
    eval env (varFromOffset U32 0) = curr.x ∧
    eval env (varFromOffset U32 4) = curr.y ∧
    eval env (varFromOffset U32 8) = next.x ∧
    eval env (U32.mk (var ⟨16⟩) (var ⟨18⟩) (var ⟨20⟩) (var ⟨22⟩)) = next.y
  := by
  intro env
  dsimp only [env, windowEnv]
  have h_offset : (recursiveRelation (p:=p)).finalAssignment.offset = 24 := rfl
  simp only [h_offset]
  rw [fib_assignment]
  simp only [circuit_norm, explicit_provable_type, reduceDIte, Nat.reduceLT, Nat.reduceAdd]
  -- TODO it's annoying that we explicitly need the GetElem instance here
  simp only [Vector.instGetElemNatLt, Vector.get, Fin.cast_mk, PNat.val_ofNat,
    Fin.isValue, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  and_intros <;> rfl

def fib_add_inputVar : Var Gadgets.Addition32.Inputs (F p) := { x := varFromOffset U32 0, y := varFromOffset U32 4 }

def fib_add_outputVar : Var U32 (F p) := U32.mk (var ⟨16⟩) (var ⟨18⟩) (var ⟨20⟩) (var ⟨22⟩)

def fib_eq_inputVar : Var (ProvablePair U32 U32) (F p) := (varFromOffset U32 4, varFromOffset U32 8)

def fib_windowEnv (curr next : Row (F p) RowType) (aux_env : Environment (F p)) : Environment (F p) := recursiveRelation.windowEnv ⟨<+> +> curr +> next, rfl⟩ aux_env

theorem fib_constraints_addition_sound (curr next : Row (F p) RowType) (aux_env : Environment (F p)) : recursiveRelation.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env → Gadgets.Addition32.Assumptions (eval (fib_windowEnv curr next aux_env) fib_add_inputVar) → Gadgets.Addition32.Spec (eval (fib_windowEnv curr next aux_env) fib_add_inputVar) (eval (fib_windowEnv curr next aux_env) fib_add_outputVar) := by
  intro h hAs
  change Circuit.ConstraintsHold.Soundness (fib_windowEnv curr next aux_env) recursiveRelation.operations at h
  simp only [recursiveRelation, table_norm, circuit_norm] at h
  have h0 := h.1
  change ((Gadgets.Addition32.circuit).toSubcircuit 16 fib_add_inputVar).Soundness
      (fib_windowEnv curr next aux_env) at h0
  have hspec := h0 hAs
  simpa [fib_add_outputVar] using hspec

theorem fib_constraints_addition (curr next : Row (F p) RowType) (aux_env : Environment (F p)) : recursiveRelation.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env → curr.x.Normalized → curr.y.Normalized → next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ next.y.Normalized := by
  intro h hx hy
  have hvars := fib_vars (p := p) curr next aux_env
  dsimp [fib_windowEnv] at hvars
  rcases hvars with ⟨hcurrx, hcurry, _, hnexty⟩
  have hinput : eval (fib_windowEnv curr next aux_env) fib_add_inputVar = Gadgets.Addition32.Inputs.mk curr.x curr.y := by
    rw [ProvableStruct.eval_eq_eval (x := fib_add_inputVar)]
    simp [ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.eval.go,
      ProvableType.eval_field, fib_add_inputVar, fib_windowEnv, hcurrx, hcurry]
  have hAs : Gadgets.Addition32.Assumptions (eval (fib_windowEnv curr next aux_env) fib_add_inputVar) := by
    rw [hinput]
    exact ⟨hx, hy⟩
  have hout : eval (fib_windowEnv curr next aux_env) fib_add_outputVar = next.y := by
    simpa [fib_add_outputVar, fib_windowEnv] using hnexty
  have hspec := fib_constraints_addition_sound (p := p) curr next aux_env h hAs
  rw [hinput, hout] at hspec
  simpa [Gadgets.Addition32.Spec] using hspec

theorem fib_constraints_eq_eval (curr next : Row (F p) RowType) (aux_env : Environment (F p)) : recursiveRelation.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env → eval (fib_windowEnv curr next aux_env) (varFromOffset U32 4) = eval (fib_windowEnv curr next aux_env) (varFromOffset U32 8) := by
  intro h
  simp only [recursiveRelation, table_norm, circuit_norm] at h
  have hEq : ((Gadgets.Equality.circuit U32).toSubcircuit 24 fib_eq_inputVar).Soundness
      (fib_windowEnv curr next aux_env) := by
    set_option maxHeartbeats 4000000 in
    simpa only [fib_eq_inputVar, fib_windowEnv, recursiveRelation, table_norm, circuit_norm] using h.2.1
  simpa only [fib_eq_inputVar, Gadgets.Equality.soundness] using hEq

theorem fib_constraints_eq (curr next : Row (F p) RowType) (aux_env : Environment (F p)) : recursiveRelation.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env → curr.y = next.x := by
  intro h
  have hraw := fib_constraints_eq_eval (p := p) curr next aux_env h
  have hvars := fib_vars (p := p) curr next aux_env
  dsimp [fib_windowEnv] at hraw hvars
  rcases hvars with ⟨_, hy, hnextx, _⟩
  simpa [hy, hnextx] using hraw

lemma fib_constraints (curr next : Row (F p) RowType) (aux_env : Environment (F p))
  : recursiveRelation.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env →
  curr.y = next.x ∧
  (curr.x.Normalized → curr.y.Normalized → next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ next.y.Normalized)
   := by
  intro h
  refine ⟨fib_constraints_eq (p:=p) curr next aux_env h, ?_⟩
  intro hx hy
  exact fib_constraints_addition (p:=p) curr next aux_env h hx hy


lemma boundary_constraints (first_row : Row (F p) RowType) (aux_env : Environment (F p)) :
  Circuit.ConstraintsHold.Soundness (windowEnv boundary ⟨<+> +> first_row, rfl⟩ aux_env) boundary.operations →
  first_row.x.value = fib32 0 ∧ first_row.y.value = fib32 1 ∧ first_row.x.Normalized ∧ first_row.y.Normalized
  := by
  set env := boundary.windowEnv ⟨<+> +> first_row, rfl⟩ aux_env
  simp only [table_norm, boundary, circuit_norm]
  simp only [and_imp]
  have hx : eval env (varFromOffset U32 0) = first_row.x := rfl
  have hy : eval env (varFromOffset U32 4) = first_row.y := rfl
  rw [hx, hy]
  clear hx hy
  intro x_zero y_one
  rw [x_zero, y_one]
  simp only [U32.fromByte_normalized, U32.fromByte_value, fib32]
  trivial

/--
  Definition of the formal table for fibonacci32
-/
def formalFib32Table : FormalTable (F p) RowType := {
  constraints := fib32Table,
  Spec := Spec,

  soundness := by sorry
}

end Tables.Fibonacci32
