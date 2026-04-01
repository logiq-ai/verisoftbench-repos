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

theorem inductiveConstraint_finalAssignment_curr_cell (table : InductiveTable F State Input)
  (i : ℕ) (hi : i < size (ProvablePair State Input))
  (hfinal : i < table.inductiveConstraint.finalAssignment.offset) :
  table.inductiveConstraint.finalAssignment.vars[i] =
    Cell.input { row := 0, column := ⟨i, hi⟩ } := by
  let as : CellAssignment 2 (ProvablePair State Input) := (CellAssignment.empty 2).pushRow 0
  let ops :=
    (table.step (varFromOffset (ProvablePair State Input) 0).1
      (varFromOffset (ProvablePair State Input) 0).2
      (size (ProvablePair State Input))).2
  have hprefix_vars := CellAssignment.assignmentFromCircuit_vars (as := as) (ops := ops)
  have hprefix_offset := CellAssignment.assignmentFromCircuit_offset (as := as) (ops := ops)
  simp [as, ops, table_assignment_norm] at hprefix_vars hprefix_offset
  simp [ProvablePair.instance, varFromOffset_pair, zero_add] at hprefix_vars hprefix_offset
  simp [InductiveTable.inductiveConstraint, TableConstraint.finalAssignment,
    table_assignment_norm, circuit_norm, ProvablePair.instance, varFromOffset_pair, zero_add,
    Vector.mapRange_zero, Vector.append_empty, hprefix_vars]
  rw [Vector.getElem_append_left]
  · rw [Vector.getElem_cast]
    rw [Vector.getElem_append_left]
    · simpa [Vector.getElem_cast] using
        (Vector.getElem_mapFinRange (create := fun col => Cell.input { row := 0, column := col }) i hi)
    · simpa using hi
  · have hi' : i < size State + size Input := by
      simpa [ProvablePair.instance] using hi
    rw [CellAssignment.assignmentFromCircuit_offset]
    simp [table_assignment_norm]
    omega

theorem inductiveConstraint_finalAssignment_next_cell (table : InductiveTable F State Input)
  (i : ℕ) (hi : i < size (ProvablePair State Input))
  (hfinal :
    size (ProvablePair State Input) +
      Operations.localLength
        (table.step (varFromOffset (ProvablePair State Input) 0).1
          (varFromOffset (ProvablePair State Input) 0).2
          (size (ProvablePair State Input))).2 + i <
      table.inductiveConstraint.finalAssignment.offset) :
  table.inductiveConstraint.finalAssignment.vars[
    size (ProvablePair State Input) +
      Operations.localLength
        (table.step (varFromOffset (ProvablePair State Input) 0).1
          (varFromOffset (ProvablePair State Input) 0).2
          (size (ProvablePair State Input))).2 + i] =
    Cell.input { row := 1, column := ⟨i, hi⟩ } := by
  -- Again, try the short fully-normalized proof first. This theorem is only append-index bookkeeping, and after enough `simp only`, `grind` has a good chance of solving it directly.
  -- 
  -- Recommended first attempt:
  -- ```lean
  --   simp only [InductiveTable.inductiveConstraint, TableConstraint.finalAssignment,
  --     table_assignment_norm, circuit_norm,
  --     CellAssignment.assignmentFromCircuit_vars,
  --     CellAssignment.assignmentFromCircuit_offset,
  --     Vector.mapRange_zero, Vector.append_empty,
  --     Vector.getElem_cast]
  --   grind
  -- ```
  -- As above, do **not** pass local hypotheses explicitly to `grind`.
  -- 
  -- If the short proof still leaves a mismatch, the manual route is:
  -- 1. introduce the exact pair-syntax prefix assignment (`as`, `ops`),
  -- 2. simplify the specialized `assignmentFromCircuit_vars` / `assignmentFromCircuit_offset`,
  -- 3. align the goal with that specialized prefix theorem before rewriting,
  -- 4. then the remaining goal is solved by `Vector.getElem_append_left`, `Vector.getElem_append_right`, and `Vector.getElem_mapFinRange`.
  -- 
  -- This theorem is intentionally stated in the same pair-based syntax that appears after unfolding `inductiveConstraint`, so once the normalization is in the right form, the proof should be mechanical.
  sorry

theorem inductiveConstraint_finalAssignment_offset (table : InductiveTable F State Input) :
  table.inductiveConstraint.finalAssignment.offset =
    size State + size Input +
      Operations.localLength
        (table.step (varFromOffset State 0) (varFromOffset Input (size State))
          (size State + size Input)).2 +
      (size State + size Input) := by
  simp [InductiveTable.inductiveConstraint, TableConstraint.finalAssignment,
    table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_offset,
    add_assoc]

theorem inductiveConstraint_windowEnv_curr_coord (table : InductiveTable F State Input)
  (curr next : State F × Input F) (aux_env : Environment F)
  (i : ℕ) (hi : i < size (ProvablePair State Input)) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env).get i =
    (toElements (M := ProvablePair State Input) curr)[i] := by
  have hiRow : i < size State + size Input := by
    simpa [ProvablePair.instance] using hi
  have h_off : i < table.inductiveConstraint.finalAssignment.offset := by
    rw [inductiveConstraint_finalAssignment_offset (table := table)]
    omega
  have hcell := inductiveConstraint_finalAssignment_curr_cell table i hi h_off
  simp [windowEnv, h_off, hcell, TraceOfLength.get, Trace.getLeFromBottom,
    _root_.Row.get, Vector.mapRange_zero, Vector.append_empty, ProvablePair.instance]
  rfl

theorem inductiveConstraint_windowEnv_curr_pair (table : InductiveTable F State Input)
  (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset (ProvablePair State Input) 0) = curr := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements,
    Vector.getElem_mapRange, zero_add]
  exact inductiveConstraint_windowEnv_curr_coord table curr next aux_env i hi

theorem inductiveConstraint_windowEnv_next_coord (table : InductiveTable F State Input)
  (curr next : State F × Input F) (aux_env : Environment F)
  (i : ℕ) (hi : i < size State) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env).get
    (size State + size Input +
      Operations.localLength
        (table.step (varFromOffset State 0) (varFromOffset Input (size State))
          (size State + size Input)).2 + i) =
    (toElements next.1)[i] := by
  -- Prove the separate-syntax bound first, convert that bound to the pair syntax required by `inductiveConstraint_finalAssignment_next_cell`, then finish the final trace lookup explicitly.
  -- 
  -- Recommended proof:
  -- ```lean
  --   have hiRow : i < size State + size Input := by
  --     omega
  --   have hiPair : i < size (ProvablePair State Input) := by
  --     simpa [ProvablePair.instance] using hiRow
  --   have hlt :
  --       size State + size Input +
  --         Operations.localLength
  --           (table.step (varFromOffset State 0) (varFromOffset Input (size State))
  --             (size State + size Input)).2 + i <
  --         table.inductiveConstraint.finalAssignment.offset := by
  --     rw [inductiveConstraint_finalAssignment_offset (table := table)]
  --     omega
  --   have hltPair :
  --       size (ProvablePair State Input) +
  --         Operations.localLength
  --           (table.step (varFromOffset (ProvablePair State Input) 0).1
  --             (varFromOffset (ProvablePair State Input) 0).2
  --             (size (ProvablePair State Input))).2 + i <
  --         table.inductiveConstraint.finalAssignment.offset := by
  --     simpa [ProvablePair.instance, varFromOffset_pair, zero_add] using hlt
  --   have hcell :
  --       table.inductiveConstraint.finalAssignment.vars[
  --         size State + size Input +
  --           Operations.localLength
  --             (table.step (varFromOffset State 0) (varFromOffset Input (size State))
  --               (size State + size Input)).2 + i] =
  --         Cell.input { row := 1, column := ⟨i, hiPair⟩ } := by
  --     simpa [ProvablePair.instance, varFromOffset_pair, zero_add]
  --       using inductiveConstraint_finalAssignment_next_cell table i hiPair hltPair
  --   unfold windowEnv
  --   simp [hlt, hcell]
  --   simpa [TraceOfLength.get, Trace.getLeFromBottom, _root_.Row.get,
  --     Vector.getElem_append_left, hi]
  -- ```
  -- 
  -- Important fixes relative to earlier failed attempts:
  -- - prove `hlt` **before** stating `hcell`, so Lean has the index-validity proof for `vars[...]`;
  -- - derive `hltPair` from `hlt` rather than first trying to convert the offset equality;
  -- - the final `simpa` needs `Vector.getElem_append_left` because `next.1` is the prefix of the full pair row `next`.
  sorry

theorem inductiveConstraint_windowEnv_next_state (table : InductiveTable F State Input)
  (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset State
      (size State + size Input +
        Operations.localLength
          (table.step (varFromOffset State 0) (varFromOffset Input (size State))
            (size State + size Input)).2)) = next.1 := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements,
    Vector.getElem_mapRange]
  exact inductiveConstraint_windowEnv_next_coord table curr next aux_env i hi

theorem inductiveConstraint_soundness (table : InductiveTable F State Input) (initialState : State F)
  (xs : List (Input F)) (i : ℕ) (hxs : xs.length = i)
  (curr next : State F × Input F) (aux_env : Environment F) :
  table.Spec initialState xs i hxs curr.1 →
  Circuit.ConstraintsHold.Soundness
    (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (table.inductiveConstraint .empty).2.circuit →
  table.Spec initialState (xs.concat curr.2) (i + 1) (hxs ▸ List.length_concat) next.1 := by
  intro hspec hsound
  set env' := windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env
  simp only [InductiveTable.inductiveConstraint, table_norm, table_assignment_norm, circuit_norm] at hsound
  rcases hsound with ⟨hs_step, hs_eq⟩
  have hcurr : eval env' (varFromOffset (ProvablePair State Input) 0) = curr := by
    simpa [env'] using inductiveConstraint_windowEnv_curr_pair table curr next aux_env
  have hcurr' := hcurr
  rw [varFromOffset_pair, eval_pair] at hcurr'
  have hacc : eval env' (varFromOffset State 0) = curr.1 := by
    exact congrArg Prod.fst hcurr'
  have hx : eval env' (varFromOffset Input (0 + size State)) = curr.2 := by
    exact congrArg Prod.snd hcurr'
  have hnext_state :
      eval env'
        (varFromOffset State
          (size State + size Input +
            Operations.localLength
              (table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))
                (size State + size Input)).2)) = next.1 := by
    simpa [env', zero_add] using inductiveConstraint_windowEnv_next_state table curr next aux_env
  have hs_step' :=
    table.soundness initialState i env' (varFromOffset State 0)
      (varFromOffset Input (0 + size State)) curr.1 curr.2 xs hxs ⟨hacc, hx⟩
      (by simpa [Circuit.operations] using hs_step) hspec
  have hout :
      eval env'
        ((table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).output
          (size State + size Input)) = next.1 := by
    simpa [Circuit.output, zero_add] using hs_eq.symm.trans hnext_state
  exact hout ▸ hs_step'

theorem tableConstraintsHold_lastRow_eq (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.lastRow.1 = output := by
  intro h_constraints
  induction N, trace using TraceOfLength.everyRowTwoRowsInduction' with
  | one row =>
      simp +arith [table_norm, InductiveTable.tableConstraints] at h_constraints
      exact (InductiveTable.equalityConstraint.soundness (Input := Input) (row := row)
        (input_state := output) (env := env 2 0)).mp h_constraints.2
  | more N curr next rest ih =>
      simp +arith [table_norm, InductiveTable.tableConstraints] at h_constraints
      have h_end : Circuit.ConstraintsHold.Soundness
          (windowEnv (equalityConstraint Input output) ⟨<+> +> next, rfl⟩ (env 2 (N + 1)))
          (equalityConstraint Input output { circuit := [], assignment := CellAssignment.empty 1 }).2.circuit := by
        simpa [rest.property] using h_constraints.2.1 rest.property
      set_option maxHeartbeats 400000 in
      have h_eq := (InductiveTable.equalityConstraint.soundness (Input := Input) (row := next)
        (input_state := output) (env := env 2 (N + 1))).mp h_end
      simpa [table_norm] using h_eq

theorem traceInputs_snoc (N : ℕ) (trace : TraceOfLength F (ProvablePair State Input) N) (row : State F × Input F) :
  traceInputs (N := N + 1) ⟨trace.val +> row, by simp [Trace.len, trace.property]⟩ = (traceInputs trace).concat row.2 := by
  simp [traceInputs, Trace.toList, List.map_concat]

theorem table_soundness_rows (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) := by
  intro h_input
  let cs := (table.tableConstraints input output).mapIdx (fun i cs => (cs, env i))
  let P : Trace F (ProvablePair State Input) → Prop :=
    fun trace =>
      TableConstraintsHold.foldl N cs trace cs →
        trace.ForAllRowsWithPrevious (fun row rest =>
          table.Spec input (traceInputs ⟨rest, rfl⟩) rest.len (traceInputs_length ⟨rest, rfl⟩) row.1)
  have h_main : P trace.val := by
    induction trace.val using Trace.every_row_two_rows_induction with
    | zero =>
        intro _
        trivial
    | one row =>
        intro h_constraints
        simp [P, TableConstraintsHold.foldl, cs, tableConstraints, TableConstraint.ConstraintsHoldOnWindow,
          equalityConstraint.soundness, Trace.ForAllRowsWithPrevious] at h_constraints ⊢
        have h_eq : row.1 = input := by
          exact (equalityConstraint.soundness (Input := Input) (row := row) (input_state := input)
            (env := env 1 0)).1 (h_constraints.1 rfl)
        simpa [traceInputs, h_eq] using h_input
    | more curr next rest ih_rest ih_curr =>
        intro h_constraints
        simp [P, TableConstraintsHold.foldl, cs, tableConstraints, TableConstraint.ConstraintsHoldOnWindow,
          equalityConstraint.soundness, Trace.ForAllRowsWithPrevious] at h_constraints ⊢
        let restTrace : TraceOfLength F (ProvablePair State Input) rest.len := ⟨rest, rfl⟩
        let currTrace : TraceOfLength F (ProvablePair State Input) (rest.len + 1) :=
          ⟨rest +> curr, by simp [Trace.len]⟩
        have h_prev := ih_curr h_constraints.2.2.2
        have h_prefix :
            table.Spec input (traceInputs restTrace) rest.len (traceInputs_length restTrace) curr.1 := by
          have h_pair :
              table.Spec input (traceInputs restTrace) rest.len (traceInputs_length restTrace) curr.1 ∧
                rest.ForAllRowsWithPrevious (fun row rest =>
                  table.Spec input (traceInputs ⟨rest, rfl⟩) rest.len (traceInputs_length ⟨rest, rfl⟩) row.1) := by
            simpa [P, Trace.ForAllRowsWithPrevious, restTrace] using ih_curr h_constraints.2.2.2
          exact h_pair.1
        have h_next0 :=
          inductiveConstraint_soundness table input (traceInputs restTrace) rest.len
            (traceInputs_length restTrace) curr next (env 0 (rest.len + 1)) h_prefix
            (by simpa [TableConstraint.operations] using h_constraints.1)
        have h_snoc : traceInputs currTrace = (traceInputs restTrace).concat curr.2 := by
          simpa [currTrace, restTrace, Trace.len] using (traceInputs_snoc rest.len restTrace curr)
        have h_next :
            table.Spec input (traceInputs currTrace) (rest.len + 1) (traceInputs_length currTrace) next.1 := by
          simpa [h_snoc, currTrace, restTrace] using h_next0
        exact ⟨h_next, h_prev⟩
  simpa [P, cs, TraceOfLength.ForAllRowsWithPrevious] using h_main

theorem table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ trace.lastRow.1 = output := by
  intro h_input h_constraints
  constructor
  · exact table_soundness_rows table input output N trace env h_input h_constraints
  · exact tableConstraintsHold_lastRow_eq table input output N trace env h_constraints


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
