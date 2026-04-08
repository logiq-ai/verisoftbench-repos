/-
"Inductive" tables are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

Thus far, only the common `k=2` case is handled.
-/
import Clean.Table.Theorems
import Clean.Gadgets.Equality

def InductiveTable.Soundness (F : Type) [Field F] (State Input : Type → Type) [ProvableType State] [ProvableType Input]
    (Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → Prop)
    (step : Var State F → Var Input F → Circuit F (Var State F)) :=
  ∀ (initialState : State F) (row_index : ℕ) (env : Environment F),
  -- for all rows and inputs
  ∀ (acc_var : Var State F) (x_var : Var Input F)
    (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
      (eval env acc_var = acc) ∧ (eval env x_var = x) →
    -- if the constraints hold
    Circuit.ConstraintsHold.Soundness env (step acc_var x_var |>.operations ((size State) + (size Input))) →
    -- and assuming the spec on the current row and previous inputs
    Spec initialState xs row_index xs_len acc →
    -- we can conclude the spec on the next row and inputs including the current input
    Spec initialState (xs.concat x) (row_index + 1) (xs_len ▸ List.length_concat) (eval env (step acc_var x_var |>.output ((size State) + (size Input))))

def InductiveTable.Completeness (F : Type) [Field F] (State Input : Type → Type) [ProvableType State] [ProvableType Input]
    (InputAssumptions : ℕ → Input F → Prop) (InitialStateAssumptions : State F → Prop)
    (Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → Prop)
    (step : Var State F → Var Input F → Circuit F (Var State F)) :=
  ∀ (initialState : State F) (row_index : ℕ) (env : Environment F),
  -- for all rows and inputs
  ∀ (acc_var : Var State F) (x_var : Var Input F)
    (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
    (eval env acc_var = acc) ∧ (eval env x_var = x) →
  -- when using honest-prover witnesses
  env.UsesLocalWitnessesCompleteness ((size State) + (size Input)) (step acc_var x_var |>.operations ((size State) + (size Input))) →
  -- assuming the spec on the current row, the input_spec on the input, and initial state assumptions
  InitialStateAssumptions initialState ∧
  Spec initialState xs row_index xs_len acc ∧ InputAssumptions row_index x →
  -- the constraints hold
  Circuit.ConstraintsHold.Completeness env (step acc_var x_var |>.operations ((size State) + (size Input)))

/--
In the case of two-row windows, an `InductiveTable` is basically a `FormalCircuit` but
- with the same input and output types
- with extra inputs to the spec: the current row number, and the list of all inputs up to and including the current row
- with assumptions replaced by the spec on the previous row, plus extra assumptions on honest prover inputs for completeness
- with input offset hard-coded to `size Row + size Input`
-/
structure InductiveTable (F : Type) [Field F] (State Input : Type → Type) [ProvableType State] [ProvableType Input] where
  /-- the `step` circuit encodes the transition logic from one state to the next -/
  step : Var State F → Var Input F → Circuit F (Var State F)

  /-- the `Spec` characterizes the `i`th state, possibly in relation to the initial state and the full list of inputs up to that point -/
  Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → Prop

  /--
    assumptions on inputs and initial state for completeness.
    explanation: in general, we expect the `step` circuit to impose some constraints on the `input`.
    similarly, the initial state may need to satisfy certain properties (e.g., normalization) for the table to work correctly.
    in the completeness proof, we therefore need to restrict the possible inputs and initial states a prover can provide.
    by design, completeness for the full table holds for any initial state and list of inputs that satisfy these assumptions.
  -/
  InputAssumptions : ℕ → Input F → Prop := fun _ _ => True
  InitialStateAssumptions : State F → Prop := fun _ => True

  soundness : InductiveTable.Soundness F State Input Spec step

  completeness : InductiveTable.Completeness F State Input InputAssumptions InitialStateAssumptions Spec step

  subcircuitsConsistent : ∀ acc x, ((step acc x).operations ((size State) + (size Input))).SubcircuitsConsistent ((size State) + (size Input))
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

namespace InductiveTable
variable {F : Type} [Field F] {State Input : TypeMap} [ProvableType State] [ProvableType Input]

/-
we show that every `InductiveTable` can be used to define a `FormalTable`,
that encodes the following statement:

`table.Spec 0 input → table.Spec (N-1) output`

for any given public `input` and `ouput`.
-/

def inductiveConstraint (table : InductiveTable F State Input) : TableConstraint 2 (ProvablePair State Input) F Unit := do
  let (acc, x) ← getCurrRow
  let output ← table.step acc x
  let (output', _) ← getNextRow
  -- TODO make this more efficient by assigning variables as long as they don't come from the input
  output' === output

def equalityConstraint (Input : TypeMap) [ProvableType Input] (target : State F) : SingleRowConstraint (ProvablePair State Input) F := do
  let (actual, _) ← getCurrRow
  actual === (const target)

def tableConstraints (table : InductiveTable F State Input) (input_state output_state : State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .everyRowExceptLast table.inductiveConstraint,
    .boundary (.fromStart 0) (equalityConstraint Input input_state),
    .boundary (.fromEnd 0) (equalityConstraint Input output_state),
  ]

theorem equalityConstraint.soundness {row : State F × Input F} {input_state : State F} {env : Environment F} :
  Circuit.ConstraintsHold.Soundness (windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env)
    (equalityConstraint Input input_state .empty).2.circuit
    ↔ row.1 = input_state := by
  set env' := windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env
  simp only [equalityConstraint, circuit_norm, table_norm]

  have h_env_in i (hi : i < size State) : (toElements row.1)[i] = env'.get i := by
    have h_env' : env' = windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, _⟩ env := rfl
    simp only [windowEnv, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
    have hi' : i < size State + size Input := by linarith
    simp [h_env', hi, hi', Vector.getElem_mapFinRange, Trace.getLeFromBottom, _root_.Row.get,
      Vector.mapRange_zero, Vector.append_empty, ProvablePair.instance]

  have h_env : eval env' (varFromOffset State 0) = row.1 := by
    rw [ProvableType.ext_iff]
    intro i hi
    rw [h_env_in i hi, ProvableType.eval_varFromOffset,
      ProvableType.toElements_fromElements, Vector.getElem_mapRange, zero_add]
  rw [h_env]

def traceInputs {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) : List (Input F) :=
  trace.val.toList.map Prod.snd

omit [Field F] in
lemma traceInputs_length {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) :
    (traceInputs trace).length = N := by
  rw [traceInputs, List.length_map, trace.val.toList_length, trace.prop]

def table_inductiveConstraint_nextOffset (table : InductiveTable F State Input) : ℕ :=
  (size State) + (size Input) +
    ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).operations ((size State) + (size Input))).localLength

theorem table_inductiveConstraint_next_assignment_cell (table : InductiveTable F State Input) (j : ℕ) (hj : j < size State + size Input)
  (h_idx : table_inductiveConstraint_nextOffset table + j < table.inductiveConstraint.finalAssignment.offset) :
  table.inductiveConstraint.finalAssignment.vars[table_inductiveConstraint_nextOffset table + j]'h_idx =
    Cell.input ⟨1, ⟨j, hj⟩⟩ := by
  simp [TableConstraint.finalAssignment, table_inductiveConstraint_nextOffset, inductiveConstraint,
    table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_vars,
    CellAssignment.assignmentFromCircuit_offset, Vector.getElem_cast, Vector.getElem_append,
    Vector.getElem_append_right, Vector.getElem_mapFinRange, Vector.mapRange_zero,
    Vector.append_empty, zero_add] <;> omega

theorem table_inductiveConstraint_windowEnv_curr_get (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F)
  (j : ℕ) (hj : j < size State + size Input) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env).get j =
    (ProvablePair.toElements curr)[j] := by
  have hlt :
      j <
        (size State + size Input) +
          Operations.localLength
            (table.step (varFromOffset State 0) (varFromOffset Input (size State))
              (size State + size Input)).2 +
        (size State + size Input) := by
    omega
  simp [hlt, hj, windowEnv, inductiveConstraint, table_assignment_norm, circuit_norm,
    CellAssignment.assignmentFromCircuit_vars, CellAssignment.assignmentFromCircuit_offset,
    Vector.getElem_append, Vector.getElem_mapFinRange, TraceOfLength.get, Trace.getLeFromBottom,
    _root_.Row.get, Vector.mapRange_zero, Vector.append_empty, ProvablePair.instance,
    varFromOffset_pair]
  split_ifs with hcurr
  · cases curr
    rfl
  · omega

theorem table_inductiveConstraint_windowEnv_curr (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset (ProvablePair State Input) 0) = curr := by
  rw [ProvableType.ext_iff]
  intro j hj
  rw [ProvableType.eval_varFromOffset]
  rw [ProvableType.toElements_fromElements]
  rw [Vector.getElem_mapRange]
  simpa using table_inductiveConstraint_windowEnv_curr_get table curr next aux_env j hj

theorem table_soundness_last_boundary (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env →
  trace.lastRow.1 = output := by
  intro h_constraints
  induction N, trace using TraceOfLength.everyRowTwoRowsInduction' with
  | one row =>
      unfold TableConstraintsHold at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints] at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints] at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints] at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints] at h_constraints
      simp [InductiveTable.tableConstraints]
      exact (equalityConstraint.soundness (row := row) (input_state := output) (env := env 2 0)).mp (h_constraints.2 rfl)
  | more N curr next rest ih =>
      unfold TableConstraintsHold at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints] at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints, Trace.len] at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [InductiveTable.tableConstraints, Trace.len, rest.property] at h_constraints
      simp [InductiveTable.tableConstraints, TraceOfLength.lastRow]
      exact (equalityConstraint.soundness (row := next) (input_state := output) (env := env 2 (N + 1))).mp h_constraints.2.1

def table_soundness_prefixConstraints (table : InductiveTable F State Input) (input_state : State F) :
    List (TableOperation (ProvablePair State Input) F) := [
  .everyRowExceptLast table.inductiveConstraint,
  .boundary (.fromStart 0) (equalityConstraint Input input_state)
]

theorem table_soundness_drop_output_boundary (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env →
  TableConstraintsHold (table_soundness_prefixConstraints table input) trace env := by
  intro h
  change TableConstraintsHold.foldl (↑N) ((table.tableConstraints input output).mapIdx fun i cs => (cs, env i)) trace.val
      ((table.tableConstraints input output).mapIdx fun i cs => (cs, env i)) at h
  change TableConstraintsHold.foldl (↑N) ((table_soundness_prefixConstraints table input).mapIdx fun i cs => (cs, env i)) trace.val
      ((table_soundness_prefixConstraints table input).mapIdx fun i cs => (cs, env i))
  revert h
  induction trace.val using Trace.every_row_two_rows_induction with
  | zero =>
      intro h
      simp [table_soundness_prefixConstraints, tableConstraints, TableConstraintsHold.foldl]
  | one row =>
      intro h
      simp [table_soundness_prefixConstraints, tableConstraints, TableConstraintsHold.foldl] at h ⊢
      exact h.1
  | more curr next rest _ ih =>
      intro h
      simp [table_soundness_prefixConstraints, tableConstraints, TableConstraintsHold.foldl] at h ⊢
      refine ⟨h.1, ?_⟩
      refine ⟨?_, ih h.2.2.2⟩
      intro hzero
      simpa [Trace.len] using hzero

theorem two_row_trace_getLeFromBottom_zero (curr next : State F × Input F) (j : ℕ) (hj : j < size State + size Input) :
  (((<+> : Trace F (ProvablePair State Input)) +> curr +> next).getLeFromBottom ⟨0, by simp [Trace.len]⟩ ⟨j, hj⟩) =
    (ProvablePair.toElements next)[j] :=   rfl

theorem table_inductiveConstraint_windowEnv_next_state_get (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F)
  (j : ℕ) (hj : j < size State) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env).get
    (table_inductiveConstraint_nextOffset table + j) =
    (toElements next.1)[j] := by
  have hj' : j < size State + size Input := by
    omega
  have h_off : table.inductiveConstraint.finalAssignment.offset =
      table_inductiveConstraint_nextOffset table + (size State + size Input) := by
    simp [table_inductiveConstraint_nextOffset, InductiveTable.inductiveConstraint,
      TableConstraint.finalAssignment, table_assignment_norm, circuit_norm,
      CellAssignment.assignmentFromCircuit_offset, zero_add]
  have h_idx : table_inductiveConstraint_nextOffset table + j < table.inductiveConstraint.finalAssignment.offset := by
    rw [h_off]
    omega
  have h_cell := table_inductiveConstraint_next_assignment_cell (table := table) (j := j) (hj := hj') (h_idx := h_idx)
  rcases next with ⟨nextState, nextInput⟩
  have h_win :
      TraceOfLength.get
        (⟨<+> +> curr +> ((nextState, nextInput) : ProvablePair State Input F), rfl⟩ :
          TraceOfLength F (ProvablePair State Input) 2)
        1 ⟨j, hj'⟩ =
      (toElements nextState)[j] := by
    simpa [TraceOfLength.get, Trace.getLeFromBottom, _root_.Row.get,
      ProvablePair.toElements, ProvablePair.instance, hj, Vector.getElem_append]
  rw [windowEnv]
  simp [h_idx, h_cell, h_win]

theorem table_inductiveConstraint_windowEnv_next_state (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset State (table_inductiveConstraint_nextOffset table)) = next.1 := by
  rw [ProvableType.ext_iff]
  intro j hj
  rw [ProvableType.eval_varFromOffset]
  simp only [ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  exact table_inductiveConstraint_windowEnv_next_state_get table curr next aux_env j hj

theorem table_inductiveConstraint_soundness (table : InductiveTable F State Input) (initialState : State F)
  (curr next : State F × Input F) (i : ℕ) (xs : List (Input F)) (hxs : xs.length = i)
  (aux_env : Environment F) :
  table.Spec initialState xs i hxs curr.1 →
  TableConstraint.ConstraintsHoldOnWindow table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env →
  table.Spec initialState (xs.concat curr.2) (i + 1) (hxs ▸ List.length_concat) next.1 := by
  intro h_spec h_constraints
  have h_curr :
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset (ProvablePair State Input) 0) = curr := by
    exact table_inductiveConstraint_windowEnv_curr
      (table := table) (curr := curr) (next := next) (aux_env := aux_env)
  have h_next :
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset State (table_inductiveConstraint_nextOffset table)) = next.1 := by
    exact table_inductiveConstraint_windowEnv_next_state
      (table := table) (curr := curr) (next := next) (aux_env := aux_env)
  simp only [InductiveTable.inductiveConstraint, table_inductiveConstraint_nextOffset,
    table_norm, circuit_norm] at h_curr h_next
  simp only [TableConstraint.ConstraintsHoldOnWindow, InductiveTable.inductiveConstraint,
    table_inductiveConstraint_nextOffset, table_norm, circuit_norm] at h_constraints
  have h_curr_state := congrArg Prod.fst h_curr
  have h_curr_input := congrArg Prod.snd h_curr
  have h_step_constraints := h_constraints.1
  have h_step_eq := h_constraints.2
  have h_step_spec :=
    table.soundness initialState i _ (varFromOffset State 0) (varFromOffset Input (0 + size State))
      curr.1 curr.2 xs hxs ⟨h_curr_state, h_curr_input⟩ h_step_constraints h_spec
  have h_output :
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).output
          ((size State) + (size Input))) = next.1 := by
    simpa [InductiveTable.inductiveConstraint, table_inductiveConstraint_nextOffset,
      table_norm, circuit_norm] using h_step_eq.symm.trans (by simpa using h_next)
  have h_output' := h_output
  simp only [InductiveTable.inductiveConstraint, table_inductiveConstraint_nextOffset,
    table_norm, circuit_norm] at h_output'
  have h_step_spec' := h_step_spec
  simp only [table_norm, circuit_norm] at h_step_spec'
  simpa [h_output'] using h_step_spec'

theorem table_soundness_rows (table : InductiveTable F State Input) (input : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table_soundness_prefixConstraints table input) trace env →
  trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) := by
  intro h_input h_constraints
  induction N, trace using TraceOfLength.everyRowTwoRowsInduction' with
  | one row =>
      simp only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, and_true]
      unfold TableConstraintsHold at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [table_soundness_prefixConstraints] at h_constraints
      have h_eq : row.1 = input := by
        exact (equalityConstraint.soundness (Input := Input) (row := row) (input_state := input) (env := env 1 0)).mp (h_constraints.left rfl)
      simpa [h_eq, traceInputs] using h_input
  | more N curr next rest ih =>
      have foldl_indep :
          ∀ (M M' : ℕ) (t : Trace F (ProvablePair State Input)),
            TableConstraintsHold.foldl M
              [(everyRowExceptLast table.inductiveConstraint, env 0),
                (boundary (RowIndex.fromStart 0) (equalityConstraint Input input), env 1)]
              t
              [(everyRowExceptLast table.inductiveConstraint, env 0),
                (boundary (RowIndex.fromStart 0) (equalityConstraint Input input), env 1)]
            ↔
            TableConstraintsHold.foldl M'
              [(everyRowExceptLast table.inductiveConstraint, env 0),
                (boundary (RowIndex.fromStart 0) (equalityConstraint Input input), env 1)]
              t
              [(everyRowExceptLast table.inductiveConstraint, env 0),
                (boundary (RowIndex.fromStart 0) (equalityConstraint Input input), env 1)] := by
        intro M M' t
        induction t using Trace.every_row_two_rows_induction with
        | zero =>
            simp [TableConstraintsHold.foldl]
        | one row =>
            simp [TableConstraintsHold.foldl]
        | more curr next rest _ ih_prev =>
            simp [TableConstraintsHold.foldl, ih_prev]
      unfold TableConstraintsHold at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      unfold TableConstraintsHold.foldl at h_constraints
      simp [table_soundness_prefixConstraints] at h_constraints
      have h_spec_prev := ih (by
        simpa [TableConstraintsHold, table_soundness_prefixConstraints] using
          (foldl_indep (N + 2) (N + 1) (rest.val +> curr)).mp h_constraints.right.right)
      have h_curr : table.Spec input (traceInputs rest) N (traceInputs_length rest) curr.1 := by
        simpa using
          TraceOfLength.lastRow_of_forAllWithPrevious
            ⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ h_spec_prev
      have h_next := table_inductiveConstraint_soundness table input curr next N (traceInputs rest)
          (traceInputs_length rest) (env 0 (rest.val.len + 1)) h_curr h_constraints.left
      simp [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious]
      exact ⟨by simpa [traceInputs, Trace.toList, Trace.len, rest.property] using h_next, h_spec_prev⟩

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ trace.lastRow.1 = output := by
  intro hspec hconstraints
  constructor
  · exact table_soundness_rows table input N trace env hspec
      (table_soundness_drop_output_boundary table input output N trace env hconstraints)
  · exact table_soundness_last_boundary table input output N trace env hconstraints


theorem table_soundness (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input → TableConstraintsHold (table.tableConstraints input output) trace env →
    table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output := by
  intro h_input h_constraints
  have ⟨ h_spec, h_output ⟩ := table_soundness_aux table input output N trace env h_input h_constraints
  rw [←h_output]
  exact TraceOfLength.lastRow_of_forAllWithPrevious trace h_spec

def toFormal (table : InductiveTable F State Input) (input output : State F) : FormalTable F (ProvablePair State Input) where
  constraints := table.tableConstraints input output
  Assumption N := N > 0 ∧ table.Spec input [] 0 rfl input
  Spec {N} trace := table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output

  soundness N trace env assumption constraints :=
    table.table_soundness input output ⟨N, assumption.left⟩ trace env assumption.right constraints

  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_offset]

end InductiveTable
