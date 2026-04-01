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

def inductiveConstraintNextOffset (table : InductiveTable F State Input) : ℕ :=
  (size State + size Input) +
    (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength (size State + size Input)

theorem inductiveConstraint_windowEnv_eval_rows (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
      (varFromOffset (ProvablePair State Input) 0) = curr
  ∧
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
      (varFromOffset (ProvablePair State Input) (inductiveConstraintNextOffset table)) = next := by
  -- Prove both conjuncts by `ProvableType.ext_iff` on the pair type `ProvablePair State Input`.
  -- 
  -- For the first conjunct, the first `size State + size Input` variables in the final assignment still come from the initial `getCurrRow`, so under `windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env` they evaluate exactly to the cells of row `0`, i.e. to `curr`.
  -- 
  -- For the second conjunct, `inductiveConstraintNextOffset table` is exactly the offset at which `getNextRow` is executed: it is the initial current-row block of size `size State + size Input`, followed by the local length of `table.step`. Thus the block of variables starting at that offset is precisely the row returned by `getNextRow`, hence it evaluates to row `1`, i.e. to `next`.
  -- 
  -- Concrete lemmas/reductions to use:
  -- - `ProvableType.ext_iff`
  -- - `ProvableType.eval_varFromOffset`
  -- - `CellAssignment.assignmentFromCircuit_offset`
  -- - `CellAssignment.assignmentFromCircuit_vars`
  -- - `windowEnv`, `inductiveConstraint`, `inductiveConstraintNextOffset`
  -- - `Trace.getLeFromBottom`, `Row.get`
  -- - `Vector.getElem_mapFinRange`, `Vector.getElem_mapRange`
  -- - `ProvablePair.instance`
  -- 
  -- A practical proof style is: for each coordinate `j`, unfold `windowEnv` and the final assignment enough to identify the `j`-th assigned cell as either `.input ⟨0, j⟩` or `.input ⟨1, j⟩`, then conclude by `simp` on `Trace.getLeFromBottom`.
  -- 
  -- Alternative: split first into four component lemmas (current state/current input/next state/next input), but the pair-level statement is cleaner and matches `varFromOffset (ProvablePair State Input)` directly.
  -- 
  -- Sanity check: the theorem is purely about how `windowEnv` interprets the assignments created by `getCurrRow`, `table.step`, and `getNextRow`; no semantic property of `table.Spec` is involved.
  sorry

theorem inductiveConstraint_step_soundness (table : InductiveTable F State Input) (initialState : State F)
  {curr next : State F × Input F} {aux_env : Environment F}
  {i : ℕ} {xs : List (Input F)} (hxs : xs.length = i) :
  TableConstraint.ConstraintsHoldOnWindow (table.inductiveConstraint) ⟨<+> +> curr +> next, rfl⟩ aux_env →
  table.Spec initialState xs i hxs curr.1 →
  table.Spec initialState (xs.concat curr.2) (i + 1) (hxs ▸ List.length_concat) next.1 := by
  -- Use the dedicated `windowEnv` evaluation lemma for the current and next rows, then apply `table.soundness` for a single transition.
  -- 
  -- 1. Introduce `h_win` and `h_spec_curr`.
  -- 2. Obtain the row-evaluation facts from
  --    `inductiveConstraint_windowEnv_eval_rows table curr next aux_env`:
  --    - `h_curr_pair : eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
  --        (varFromOffset (ProvablePair State Input) 0) = curr`,
  --    - `h_next_pair : eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
  --        (varFromOffset (ProvablePair State Input) (inductiveConstraintNextOffset table)) = next`.
  -- 3. Project these pair equalities using `varFromOffset_pair` to get
  --    - `h_acc : eval env' (varFromOffset State 0) = curr.1`,
  --    - `h_x   : eval env' (varFromOffset Input (size State)) = curr.2`,
  --    - `h_next_state : eval env' (varFromOffset State (inductiveConstraintNextOffset table)) = next.1`,
  --    where `env' := windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env`.
  -- 4. Unfold `h_win` with
  --    `simp only [TableConstraint.ConstraintsHoldOnWindow, inductiveConstraint, inductiveConstraintNextOffset, table_norm, table_assignment_norm, circuit_norm, Gadgets.Equality.soundness, varFromOffset_pair] at h_win`.
  --    After simplification, extract:
  --    - `h_step : Circuit.ConstraintsHold.Soundness env' (table.step (varFromOffset State 0) (varFromOffset Input (size State)) |>.operations (size State + size Input))`,
  --    - `h_eq : eval env' (table.step (varFromOffset State 0) (varFromOffset Input (size State)) |>.output (size State + size Input)) = next.1`.
  --      (This is the equality gadget `output' === output`, rewritten using `h_next_state`.)
  -- 5. Apply `table.soundness` with
  --    - `row_index := i`,
  --    - `acc := curr.1`, `x := curr.2`, `xs := xs`, `xs_len := hxs`,
  --    - the current-row evaluation equalities `⟨h_acc, h_x⟩`,
  --    - `h_step`, and `h_spec_curr`.
  --    This yields the spec for the evaluated step output.
  -- 6. Rewrite that output using `h_eq`; the result is exactly the desired spec for `next.1`.
  -- 
  -- Alternative: if the projections are awkward, keep everything at the pair level until the last step and only then take `.1`/`.2` components.
  -- 
  -- Sanity check: once the current row is identified with `acc,x` and the next-row state is identified with the step output, the statement is exactly `table.soundness` applied to one window.
  sorry

def tableConstraintsFromStart (table : InductiveTable F State Input) (input_state output_state : State F)
    (lastIdx : ℕ) : List (TableOperation (ProvablePair State Input) F) := [
  .everyRowExceptLast table.inductiveConstraint,
  .boundary (.fromStart 0) (equalityConstraint Input input_state),
  .boundary (.fromStart lastIdx) (equalityConstraint Input output_state),
]

theorem tableConstraints_iff_fromStart (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env ↔
    TableConstraintsHold (tableConstraintsFromStart table input output (N - 1)) trace env := by
  rcases trace with ⟨trace, htrace⟩
  simp [InductiveTable.tableConstraints, tableConstraintsFromStart, TableConstraintsHold,
    TableConstraintsHold.foldl, Array.toList_push, table_norm] at *
  clear htrace
  induction trace using Trace.every_row_two_rows_induction with
  | zero =>
      simp [TableConstraintsHold.foldl, Trace.len]
  | one row =>
      simp [TableConstraintsHold.foldl, Trace.len]
  | more curr next rest ihRest ihCurr =>
      simp [TableConstraintsHold.foldl, Trace.len, ihCurr]

theorem traceInputs_snoc {N : ℕ} (rest : TraceOfLength F (ProvablePair State Input) N) (row : State F × Input F) :
  traceInputs (N := N + 1) ⟨rest.val +> row, by rw [Trace.len, rest.property]⟩ = (traceInputs rest).concat row.2 := by
  unfold traceInputs
  simp [Trace.toList, List.map_concat]

theorem table_soundness_aux_fromStart (table : InductiveTable F State Input) (input output : State F) (lastIdx : ℕ)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (tableConstraintsFromStart table input output lastIdx) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ (N - 1 = lastIdx → trace.lastRow.1 = output) := by
  -- This is the induction-friendly version of `table_soundness_aux`: the last boundary is expressed as an absolute `.fromStart lastIdx`, so the same constraint list remains stable on prefixes.
  -- 
  -- Proof by positive-length induction on `trace` using `TraceOfLength.everyRowTwoRowsInduction'`.
  -- 
  -- **Base case (`trace = ⟨<+> +> row, rfl⟩`):**
  -- 1. Introduce `h_init` and `h_constraints`.
  -- 2. Simplify with `simp only [tableConstraintsFromStart, TableConstraintsHold, table_norm, TableConstraint.ConstraintsHoldOnWindow] at h_constraints`.
  --    The `.everyRowExceptLast` piece vanishes on a one-row trace.
  -- 3. Rewrite both boundary components using `equalityConstraint.soundness`. This gives
  --    - `h_first : row.1 = input`,
  --    - `h_last : 0 = lastIdx → row.1 = output`.
  -- 4. For the `ForAllRowsWithPrevious` goal, unfold it by
  --    `simp only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, table_norm]`.
  --    Rewrite by `h_first`; then `simpa [traceInputs] using h_init` (the proof argument in `Spec` is proposition-valued, so proof irrelevance lets `simpa` close the remaining mismatch).
  -- 5. Pair this with `h_last`.
  -- 
  -- **Step case (`trace = ⟨rest.val +> curr +> next, _⟩`):**
  -- 1. Introduce `h_init` and `h_constraints`.
  -- 2. Simplify `h_constraints` with the same `simp only`. Because the final boundary is `.fromStart lastIdx`, the recursive tail is definitionally
  --    `TableConstraintsHold (tableConstraintsFromStart table input output lastIdx) ⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ env`.
  --    Extract:
  --    - `h_step` from `.everyRowExceptLast` on the window `curr,next`,
  --    - `h_prefix` for the prefix trace `⟨rest.val +> curr, _⟩`,
  --    - `h_last : rest.val.len + 1 = lastIdx → next.1 = output`, after rewriting the last boundary with `equalityConstraint.soundness`.
  -- 3. Apply the induction hypothesis to the prefix and `h_prefix`. Obtain `h_forall_prefix`.
  -- 4. Extract the current-row spec from the prefix using `TraceOfLength.lastRow_of_forAllWithPrevious` on `⟨rest.val +> curr, _⟩`. After simplifying `[table_norm]`, this is exactly
  --    `table.Spec input (traceInputs rest) rest.val.len (traceInputs_length rest) curr.1`.
  -- 5. Apply `inductiveConstraint_step_soundness` with
  --    - `xs := traceInputs rest`,
  --    - `i := rest.val.len`,
  --    - `hxs := traceInputs_length rest`,
  --    - the window hypothesis `h_step`, and the current-row spec from step 4.
  --    This yields the spec for `next.1` with input list `(traceInputs rest).concat curr.2`.
  -- 6. Rewrite that list using `traceInputs_snoc rest curr`; after `simpa` (again using proof irrelevance for the length proof), this is exactly the head clause needed for `Trace.ForAllRowsWithPrevious` on `⟨rest.val +> curr +> next, _⟩`.
  -- 7. Assemble the new `ForAllRowsWithPrevious` proof with
  --    `simp only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, table_norm]`
  --    and combine the `next` fact from step 6 with `h_forall_prefix`.
  -- 8. For the output implication, intro `hidx : N - 1 = lastIdx`; after simplifying `N - 1` in this case, `hidx` is exactly the hypothesis expected by `h_last`, so conclude `next.1 = output`.
  -- 
  -- Alternative route A: phrase the induction directly over the recursive predicate `TableConstraintsHold.foldl`; the current statement avoids that bookkeeping by converting the end boundary to an absolute start-index.
  -- Alternative route B: strengthen the conclusion so it explicitly carries the last-row spec as a separate conjunct, though `TraceOfLength.lastRow_of_forAllWithPrevious` already supplies that extraction.
  -- 
  -- Sanity check / disproof angle: once the end boundary is absolute, the theorem says exactly: the first boundary initializes the spec, each two-row window propagates it forward, and if the current row index happens to be `lastIdx`, the boundary also forces the state to equal `output`.
  sorry

theorem table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ trace.lastRow.1 = output := by
  intro h_init h_constraints
  have h_constraints' :
      TableConstraintsHold (tableConstraintsFromStart table input output (N - 1)) trace env := by
    exact (tableConstraints_iff_fromStart table input output N trace env).mp h_constraints
  rcases table_soundness_aux_fromStart table input output (N - 1) N trace env h_init h_constraints' with
    ⟨h_forall, h_last⟩
  exact ⟨h_forall, h_last rfl⟩


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
