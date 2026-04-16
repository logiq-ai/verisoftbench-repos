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

def inductiveConstraint_assignment_blocks (table : InductiveTable F State Input) :
    Vector (Cell 2 (ProvablePair State Input))
      (((size State + size Input) +
        Operations.localLength
          (table.step (varFromOffset (ProvablePair State Input) 0).1
            (varFromOffset (ProvablePair State Input) 0).2 (size State + size Input)).2) +
        (size State + size Input)) :=
  ((Vector.mapFinRange (size State + size Input) fun col =>
      (Cell.input { row := 0, column := col } : Cell 2 (ProvablePair State Input))) ++
    (Vector.mapRange
      (Operations.localLength
        (table.step (varFromOffset (ProvablePair State Input) 0).1
          (varFromOffset (ProvablePair State Input) 0).2 (size State + size Input)).2)
      fun i => (Cell.aux i : Cell 2 (ProvablePair State Input)))) ++
    (Vector.mapFinRange (size State + size Input) fun col =>
      (Cell.input { row := 1, column := col } : Cell 2 (ProvablePair State Input)))

theorem inductiveConstraint_finalAssignment_vars (table : InductiveTable F State Input) :
  table.inductiveConstraint.finalAssignment.vars =
    (inductiveConstraint_assignment_blocks table).cast (by
      simp [inductiveConstraint_assignment_blocks, TableConstraint.finalAssignment, inductiveConstraint,
        table_norm, table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_offset,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, zero_add]) := by
  simp [inductiveConstraint_assignment_blocks, TableConstraint.finalAssignment, inductiveConstraint,
    table_norm, table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_vars,
    CellAssignment.assignmentFromCircuit_offset, Vector.mapRange_zero, Vector.empty_append,
    Vector.append_empty, zero_add]
  grind

theorem inductiveConstraint_finalAssignment_curr_var (table : InductiveTable F State Input) (i : ℕ) (hi : i < size (ProvablePair State Input)) :
  table.inductiveConstraint.finalAssignment.vars[i]'(by
    have hle : size (ProvablePair State Input) ≤ table.inductiveConstraint.finalAssignment.offset := by
      simpa [TableConstraint.finalAssignment, inductiveConstraint, table_assignment_norm, circuit_norm,
        CellAssignment.assignmentFromCircuit_offset, zero_add]
    exact lt_of_lt_of_le hi hle) =
    Cell.input { row := 0, column := ⟨i, hi⟩ } := by
  have hvars := inductiveConstraint_finalAssignment_vars table
  rw [hvars]
  repeat rw [Vector.getElem_cast]
  let rowLen := size State + size Input
  have hiPair : i < rowLen := by
    simpa [rowLen, ProvablePair.instance] using hi
  have hfirst : i < rowLen +
      Operations.localLength
        (table.step (varFromOffset (ProvablePair State Input) 0).1
          (varFromOffset (ProvablePair State Input) 0).2 rowLen).2 := by
    omega
  simp only [inductiveConstraint_assignment_blocks, rowLen]
  rw [Vector.getElem_append_left hfirst]
  rw [Vector.getElem_append_left hiPair]
  rw [Vector.getElem_mapFinRange]

theorem inductiveConstraint_eval_curr_get (table : InductiveTable F State Input) (curr next : State F × Input F) (env : Environment F)
  (i : ℕ) (hi : i < size (ProvablePair State Input)) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env).get i =
    (ProvableType.toElements (M := ProvablePair State Input) curr)[i] := by
  have hbound : i < table.inductiveConstraint.finalAssignment.offset := by
    have hle : size (ProvablePair State Input) ≤ table.inductiveConstraint.finalAssignment.offset := by
      simpa [TableConstraint.finalAssignment, inductiveConstraint, table_assignment_norm, circuit_norm,
        CellAssignment.assignmentFromCircuit_offset, zero_add]
    exact lt_of_lt_of_le hi hle
  have hbound' : i < (table.inductiveConstraint TableContext.empty).2.assignment.offset := by
    simpa [TableConstraint.finalAssignment] using hbound
  have hcell : table.inductiveConstraint.finalAssignment.vars[i]'(hbound) = Cell.input { row := 0, column := ⟨i, hi⟩ } := by
    simpa using inductiveConstraint_finalAssignment_curr_var table i hi
  have hcell' : (table.inductiveConstraint TableContext.empty).2.assignment.vars[i]'(hbound') = Cell.input { row := 0, column := ⟨i, hi⟩ } := by
    simpa [TableConstraint.finalAssignment] using hcell
  rw [windowEnv, TableConstraint.finalAssignment]
  simp only [hbound', reduceDIte]
  rw [hcell']
  simp [TraceOfLength.get]
  rfl

theorem inductiveConstraint_eval_curr (table : InductiveTable F State Input) (curr next : State F × Input F) (env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env)
    (varFromOffset (ProvablePair State Input) 0) = curr := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  simpa only [zero_add] using inductiveConstraint_eval_curr_get table curr next env i hi

def inductiveConstraint_nextOffset (table : InductiveTable F State Input) : ℕ :=
  size State + size Input +
    (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength (size State + size Input)

theorem inductiveConstraint_finalAssignment_nextState_var (table : InductiveTable F State Input) (i : ℕ) (hi : i < size State) :
  table.inductiveConstraint.finalAssignment.vars[inductiveConstraint_nextOffset table + i]'(by
    simp [TableConstraint.finalAssignment, inductiveConstraint, table_assignment_norm, circuit_norm,
      inductiveConstraint_nextOffset, CellAssignment.assignmentFromCircuit_offset, zero_add]
    omega) =
    Cell.input { row := 1, column := ⟨i, by
      have hiRow : i < size State + size Input := by omega
      simpa [ProvablePair.instance] using hiRow⟩ } := by
  simp only [TableConstraint.finalAssignment, inductiveConstraint, table_norm, table_assignment_norm,
    circuit_norm, CellAssignment.assignmentFromCircuit_offset, CellAssignment.assignmentFromCircuit_vars,
    Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, zero_add]
  let rowLen := size State + size Input
  let stepLen :=
    Operations.localLength
      (table.step (varFromOffset State 0) (varFromOffset Input (size State)) rowLen).2
  have h_pairLen0 :
      Operations.localLength
        (table.step (varFromOffset (ProvablePair State Input) 0).1
          (varFromOffset (ProvablePair State Input) 0).2 rowLen).2 = stepLen := by
    simpa [rowLen, stepLen, varFromOffset_pair, zero_add]
  repeat rw [Vector.getElem_cast]
  simp [inductiveConstraint_nextOffset, rowLen, stepLen, h_pairLen0,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [Vector.getElem_append_right
    (h := by
      simp [circuit_norm, inductiveConstraint_nextOffset, rowLen, stepLen, h_pairLen0,
        CellAssignment.assignmentFromCircuit_offset, varFromOffset_pair,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      omega)
    (hi := by
      simp [circuit_norm, inductiveConstraint_nextOffset, rowLen, stepLen, h_pairLen0,
        CellAssignment.assignmentFromCircuit_offset, varFromOffset_pair,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])]
  rw [Vector.getElem_mapFinRange]
  simpa [circuit_norm, inductiveConstraint_nextOffset, rowLen, stepLen, h_pairLen0,
    CellAssignment.assignmentFromCircuit_offset, varFromOffset_pair, ProvablePair.instance,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_sub_cancel_left]

theorem inductiveConstraint_eval_nextState_get (table : InductiveTable F State Input) (curr next : State F × Input F) (env : Environment F)
  (i : ℕ) (hi : i < size State) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env).get
    (inductiveConstraint_nextOffset table + i) = (toElements next.1)[i] := by
  have hbound : inductiveConstraint_nextOffset table + i < table.inductiveConstraint.finalAssignment.offset := by
    simp [TableConstraint.finalAssignment, inductiveConstraint, table_assignment_norm, circuit_norm,
      inductiveConstraint_nextOffset, CellAssignment.assignmentFromCircuit_offset, zero_add]
    omega
  have hiRow : i < size State + size Input := by omega
  have hbound' :
      inductiveConstraint_nextOffset table + i < (table.inductiveConstraint TableContext.empty).2.assignment.offset := by
    simpa [TableConstraint.finalAssignment] using hbound
  have hcell :
      table.inductiveConstraint.finalAssignment.vars[inductiveConstraint_nextOffset table + i]'hbound =
        Cell.input { row := 1, column := ⟨i, by
          simpa [ProvablePair.instance] using hiRow⟩ } := by
    simpa using inductiveConstraint_finalAssignment_nextState_var table i hi
  have hcell' :
      (table.inductiveConstraint TableContext.empty).2.assignment.vars[inductiveConstraint_nextOffset table + i]'hbound' =
        Cell.input { row := 1, column := ⟨i, by
          simpa [ProvablePair.instance] using hiRow⟩ } := by
    simpa [TableConstraint.finalAssignment] using hcell
  rw [windowEnv, TableConstraint.finalAssignment]
  simp only [hbound', reduceDIte]
  rw [hcell']
  simp only [TraceOfLength.get]
  norm_num
  change _root_.Row.get (S := ProvablePair State Input) next ⟨i, by simpa [ProvablePair.instance] using hiRow⟩ = (toElements next.1)[i]
  rw [_root_.Row.get]
  simpa [ProvablePair.instance] using
    (Vector.getElem_append_left (xs := toElements next.1) (ys := toElements next.2) (i := i) hi)

theorem inductiveConstraint_eval_nextState (table : InductiveTable F State Input) (curr next : State F × Input F) (env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env)
    (varFromOffset State (inductiveConstraint_nextOffset table)) = next.1 := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  simpa using inductiveConstraint_eval_nextState_get table curr next env i hi

theorem inductiveConstraint_soundness (table : InductiveTable F State Input) (input : State F)
  (xs : List (Input F)) (i : ℕ) (xs_len : xs.length = i)
  (curr next : State F × Input F) (env : Environment F) :
  table.Spec input xs i xs_len curr.1 →
  TableConstraint.ConstraintsHoldOnWindow table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env →
  table.Spec input (xs.concat curr.2) (i + 1) (xs_len ▸ List.length_concat) next.1 := by
  intro h_spec h_window
  let env' := windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env
  have h_split :
      Circuit.ConstraintsHold.Soundness
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env)
        ((table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).2)
      ∧
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env)
        (varFromOffset State (inductiveConstraint_nextOffset table))
      =
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ env)
        ((table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).1) := by
    simpa [TableConstraint.ConstraintsHoldOnWindow, inductiveConstraint, table_norm, table_assignment_norm, circuit_norm, inductiveConstraint_nextOffset] using h_window
  have h_step : Circuit.ConstraintsHold.Soundness env'
      ((table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).2) := by
    simpa [env'] using h_split.1
  have h_eq : eval env' (varFromOffset State (inductiveConstraint_nextOffset table)) =
      eval env' ((table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).1) := by
    simpa [env'] using h_split.2
  have hcurr_pair : eval env' (varFromOffset (ProvablePair State Input) 0) = curr := by
    simpa [env'] using inductiveConstraint_eval_curr table curr next env
  rw [varFromOffset_pair, eval_pair] at hcurr_pair
  have hcurr_state : eval env' (varFromOffset State 0) = curr.1 := by
    simpa using congrArg Prod.fst hcurr_pair
  have hcurr_input : eval env' (varFromOffset Input (size State)) = curr.2 := by
    simpa using congrArg Prod.snd hcurr_pair
  have hspec' := table.soundness input i env'
    (varFromOffset State 0) (varFromOffset Input (size State))
    curr.1 curr.2 xs xs_len ⟨hcurr_state, hcurr_input⟩ h_step h_spec
  have hnext_state : eval env' (varFromOffset State (inductiveConstraint_nextOffset table)) = next.1 := by
    simpa [env'] using inductiveConstraint_eval_nextState table curr next env
  have hout : eval env' ((table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).1) = next.1 := by
    rw [← h_eq, hnext_state]
  simpa [hout] using hspec'

theorem table_soundness_output (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env →
  trace.lastRow.1 = output := by
  intro h
  induction N, trace using TraceOfLength.everyRowTwoRowsInduction' with
  | one row =>
      simp [tableConstraints, TableConstraintsHold] at h ⊢
      unfold TableConstraintsHold.foldl at h
      have h₂ := h
      unfold TableConstraintsHold.foldl at h₂
      have h₃ := h₂.2
      unfold TableConstraintsHold.foldl at h₃
      simp at h₃
      have h₄ : TableConstraint.ConstraintsHoldOnWindow (equalityConstraint Input output) ⟨<+> +> row, rfl⟩ (env 2 0) := by
        exact h₃.1 rfl
      simpa using (equalityConstraint.soundness.mp h₄)
  | more N curr next rest ih =>
      simp [tableConstraints, TableConstraintsHold] at h ⊢
      unfold TableConstraintsHold.foldl at h
      have h₂ := h.2
      unfold TableConstraintsHold.foldl at h₂
      have h₃ := h₂.2
      unfold TableConstraintsHold.foldl at h₃
      simp at h₃
      have h₄ : TableConstraint.ConstraintsHoldOnWindow (equalityConstraint Input output) ⟨<+> +> next, rfl⟩ (env 2 (rest.val.len + 1)) := by
        exact h₃.1 (by simpa [Trace.len, rest.property])
      simpa using (equalityConstraint.soundness.mp h₄)

theorem table_soundness_rows (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
  trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) := by
  intro h_init h_constraints
  let cs : List (TableOperation (ProvablePair State Input) F × (ℕ → Environment F)) := [
    (.everyRowExceptLast table.inductiveConstraint, env 0),
    (.boundary (.fromStart 0) (equalityConstraint Input input), env 1),
    (.boundary (.fromEnd 0) (equalityConstraint Input output), env 2)
  ]
  change TableConstraintsHold.foldl (↑N) cs trace.val cs at h_constraints
  have h_raw : ∀ t : Trace F (ProvablePair State Input),
      TableConstraintsHold.foldl (↑N) cs t cs →
      t.ForAllRowsWithPrevious (fun row rest =>
        table.Spec input (rest.toList.map Prod.snd) rest.len
          (by rw [List.length_map, rest.toList_length]) row.1) := by
    intro t
    induction t using Trace.every_row_two_rows_induction with
    | zero =>
        intro h
        simp [Trace.ForAllRowsWithPrevious]
    | one row =>
        intro h
        simp only [cs, TableConstraintsHold.foldl, Trace.ForAllRowsWithPrevious,
          InductiveTable.equalityConstraint.soundness, table_norm] at h ⊢
        have h_eq : row.1 = input := by
          simpa using h.left
        rw [h_eq]
        exact ⟨h_init, trivial⟩
    | more curr next rest ihRest ihCurr =>
        intro h
        simp only [cs, TableConstraintsHold.foldl, Trace.ForAllRowsWithPrevious,
          InductiveTable.equalityConstraint.soundness, table_norm] at h ⊢
        have hprefix := ihCurr h.2.2.2
        simp only [Trace.ForAllRowsWithPrevious] at hprefix
        let restT : TraceOfLength F (ProvablePair State Input) rest.len := ⟨rest, rfl⟩
        have hnext := inductiveConstraint_soundness (table := table) (input := input)
          (xs := traceInputs restT) (i := rest.len)
          (xs_len := traceInputs_length restT)
          (curr := curr) (next := next) (env := env 0 (rest.len + 1))
          (by simpa [traceInputs, restT] using hprefix.left)
          h.1
        have hnext' :
            table.Spec input ((rest +> curr).toList.map Prod.snd) (rest.len + 1)
              (by rw [List.length_map, Trace.toList_length, Trace.len]) next.1 := by
          simpa [traceInputs, restT, Trace.toList] using hnext
        exact ⟨hnext', hprefix⟩
  simpa [TraceOfLength.ForAllRowsWithPrevious, traceInputs] using h_raw trace.val h_constraints

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ trace.lastRow.1 = output := by
  intro h_spec h_constraints
  exact ⟨
    table_soundness_rows table input output N trace env h_spec h_constraints,
    table_soundness_output table input output N trace env h_constraints
  ⟩


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
