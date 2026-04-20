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

def inductiveConstraint_currAssignment : CellAssignment 2 (ProvablePair State Input) :=
  CellAssignment.pushRow (CellAssignment.empty 2) 0

theorem inductiveConstraint_finalAssignment_curr_cell (table : InductiveTable F State Input) (i : Fin (size State + size Input))
  (hi_offset : i.val < table.inductiveConstraint.finalAssignment.offset) :
  table.inductiveConstraint.finalAssignment.vars[i.val]'hi_offset =
    Cell.input (W:=2) (S:=ProvablePair State Input)
      ⟨0, ⟨i.val, by simpa [ProvablePair.instance] using i.isLt⟩⟩ := by
  have hi : i.val < size State + size Input := i.isLt
  let currAs : CellAssignment 2 (ProvablePair State Input) :=
    inductiveConstraint_currAssignment (State:=State) (Input:=Input)
  let stepOps := Circuit.operations
    (table.step (varFromOffset State 0) (varFromOffset Input (size State)))
    (size State + size Input)
  have hi_stepNum : i.val < size State + size Input + Operations.localLength stepOps := by
    omega
  simp only [TableConstraint.finalAssignment, inductiveConstraint,
    table_assignment_norm, circuit_norm]
  simp only [currAs, stepOps,
    CellAssignment.assignmentFromCircuit_vars,
    CellAssignment.assignmentFromCircuit_offset,
    CellAssignment.pushRow_offset,
    inductiveConstraint_currAssignment,
    Vector.getElem_cast, Vector.getElem_append,
    Vector.getElem_mapFinRange,
    hi, hi_stepNum, hi_offset,
    varFromOffset_pair, ProvablePair.instance,
    zero_add, Nat.add_zero, Nat.sub_zero,
    Vector.mapRange_zero, Vector.append_empty,
    reduceDIte, Fin.val_zero, Nat.not_lt_zero]

theorem inductiveConstraint_nextState_eval (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset State
      ((size State + size Input) +
        (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
          (size State + size Input))) = next.1 := by
  set env' := windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env
  let L := Operations.localLength
    (table.step (varFromOffset State 0) (varFromOffset Input (size State))
      (size State + size Input)).2
  let start := (size State + size Input) + L
  have hlen_pair :
      Operations.localLength
        (table.step (varFromOffset (ProvablePair State Input) 0).1
          (varFromOffset (ProvablePair State Input) 0).2 (size State + size Input)).2 = L := by
    simp [L, varFromOffset_pair]
  have hlen_zero :
      Operations.localLength
        (table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))
          (size State + size Input)).2 = L := by
    simp [L]
  have h_next :
      eval env' (varFromOffset (ProvablePair State Input) start) = next := by
    rw [ProvableType.ext_iff]
    intro j hj
    rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
    have h_env' : env' = windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env := rfl
    have hj' : j < size State + size Input := by
      simpa [ProvablePair.instance] using hj
    simp only [h_env', inductiveConstraint, windowEnv, table_assignment_norm, circuit_norm,
      CellAssignment.assignmentFromCircuit_offset, CellAssignment.assignmentFromCircuit_vars,
      start, L, hlen_pair, hlen_zero]
    split_ifs at *
    case pos h_pos =>
      have h_vec : size State + size Input + L + j < (size State + size Input + L) + (size State + size Input) := by
        omega
      rw [Vector.getElem_append (by simpa [CellAssignment.assignmentFromCircuit_offset, L, hlen_pair] using h_vec)]
      simp [CellAssignment.assignmentFromCircuit_offset, L, hlen_pair, h_vec]
      have h_not_prefix : ¬ size State + size Input + L + j < size State + size Input + L := by
        omega
      rw [Vector.getElem_append (by simpa [CellAssignment.assignmentFromCircuit_offset, L, hlen_pair] using h_vec)]
      simp [CellAssignment.assignmentFromCircuit_offset, L, hlen_pair, h_not_prefix,
        Vector.getElem_cast, Trace.getLeFromBottom, _root_.Row.get, Vector.getElem_mapFinRange, hj]
      simpa [ProvablePair.instance, Vector.getElem_append] using (rfl : (toElements next)[j] = (toElements next)[j])
    case neg h_neg =>
      exfalso
      omega
  simpa [start, L, eval_pair, varFromOffset_pair] using congrArg Prod.fst h_next

theorem inductiveConstraint_windowEnv_curr_extends (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  Environment.ExtendsVector
    (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (ProvablePair.toElements (α:=State) (β:=Input) curr) 0 := by
  intro i
  have hi_offset : i.val < table.inductiveConstraint.finalAssignment.offset := by
    simp [TableConstraint.finalAssignment, inductiveConstraint, table_assignment_norm,
      circuit_norm, CellAssignment.assignmentFromCircuit_offset]
    omega
  have hcell := inductiveConstraint_finalAssignment_curr_cell table i hi_offset
  change (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env).get (0 + i.val) =
    (ProvablePair.toElements (α:=State) (β:=Input) curr)[i.val]
  simp only [windowEnv, hi_offset, hcell, Trace.getLeFromBottom,
    _root_.Row.get, ProvablePair.toElements, zero_add, Nat.add_zero,
    Vector.mapRange_zero, Vector.append_empty, reduceDIte, Fin.val_zero]
  rfl

theorem inductiveConstraint_windowEnv_curr_get (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F)
  (j : ℕ) (hj : j < size State + size Input) :
  (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env).get j =
    _root_.Row.get (F:=F) (S:=ProvablePair State Input) curr ⟨j, by simpa [ProvablePair.instance] using hj⟩ := by
  have h := inductiveConstraint_windowEnv_curr_extends table curr next aux_env
  have h' := h ⟨j, by simpa [ProvablePair.instance] using hj⟩
  simpa [Row.get, ProvablePair.toElements, Nat.zero_add] using h'

theorem inductiveConstraint_currInput_eval (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset Input (size State)) = curr.2 := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  have hj : size State + i < size State + size Input := by
    omega
  have hnot : ¬ size State + i < size State := by
    omega
  rw [inductiveConstraint_windowEnv_curr_get table curr next aux_env (size State + i) hj]
  simpa [_root_.Row.get, ProvablePair.instance, Vector.getElem_append, hnot]

theorem inductiveConstraint_currState_eval (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset State 0) = curr.1 := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange, zero_add]
  have hj : i < size State + size Input := by
    omega
  rw [inductiveConstraint_windowEnv_curr_get table curr next aux_env i hj]
  simpa [_root_.Row.get, ProvablePair.instance, Vector.getElem_append, hi]

theorem inductiveConstraint_curr_eval (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
    (varFromOffset (ProvablePair State Input) 0) = curr := by
  rw [varFromOffset_pair, eval_pair, Prod.mk.injEq]
  exact ⟨
    inductiveConstraint_currState_eval table curr next aux_env,
    by simpa [zero_add] using inductiveConstraint_currInput_eval table curr next aux_env
  ⟩

theorem inductiveConstraint_soundness (table : InductiveTable F State Input) (initialState : State F)
  (xs : List (Input F)) (i : ℕ) (hxs : xs.length = i)
  (curr next : State F × Input F) (aux_env : Environment F)
  (hconcat : (xs.concat curr.2).length = i + 1) :
  table.Spec initialState xs i hxs curr.1 →
  table.inductiveConstraint.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env →
  table.Spec initialState (xs.concat curr.2) (i + 1) hconcat next.1 := by
  intro hspec hhold
  have h_curr_pair :
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset (ProvablePair State Input) 0) = curr := by
    exact inductiveConstraint_curr_eval table curr next aux_env
  have h_curr_state :
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset State 0) = curr.1 := by
    have h := h_curr_pair
    simp only [varFromOffset_pair, eval_pair] at h
    exact congrArg Prod.fst h
  have h_curr_input :
      eval (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset Input (0 + size State)) = curr.2 := by
    have h := h_curr_pair
    simp only [varFromOffset_pair, eval_pair] at h
    exact congrArg Prod.snd h
  have h_next_state :
      eval
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset State
          ((size State + size Input) +
            (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
              (size State + size Input))) = next.1 := by
    exact inductiveConstraint_nextState_eval table curr next aux_env
  simp only [TableConstraint.ConstraintsHoldOnWindow] at hhold
  simp only [InductiveTable.inductiveConstraint, table_norm, table_assignment_norm, circuit_norm] at hhold
  rcases hhold with ⟨h_step, h_eq⟩
  have h_step' :
      Circuit.ConstraintsHold.Soundness
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        ((table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).operations
          (size State + size Input)) := by
    simpa [InductiveTable.inductiveConstraint, table_norm, table_assignment_norm, circuit_norm] using h_step
  have h_eq' :
      eval
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset State
          (size State + size Input +
            (table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).localLength
              (size State + size Input))) =
      eval
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        ((table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).output
          (size State + size Input)) := by
    simpa [InductiveTable.inductiveConstraint, table_norm, table_assignment_norm, circuit_norm] using h_eq
  have h_next_state' :
      eval
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        (varFromOffset State
          (size State + size Input +
            (table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).localLength
              (size State + size Input))) = next.1 := by
    simpa [zero_add] using h_next_state
  have h_spec_out :
      table.Spec initialState (xs.concat curr.2) (i + 1) (hxs ▸ List.length_concat)
        (eval
          (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
          ((table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).output
            (size State + size Input))) := by
    exact table.soundness initialState i
      (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
      (varFromOffset State 0) (varFromOffset Input (0 + size State)) curr.1 curr.2 xs hxs
      ⟨h_curr_state, h_curr_input⟩ h_step' hspec
  have h_output_eq_next :
      eval
        (windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env)
        ((table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))).output
          (size State + size Input)) = next.1 := by
    exact h_eq'.symm.trans h_next_state'
  have h_spec_next :
      table.Spec initialState (xs.concat curr.2) (i + 1) (hxs ▸ List.length_concat) next.1 := by
    rw [← h_output_eq_next]
    exact h_spec_out
  simpa using h_spec_next

def tableConstraintsNoEnd (table : InductiveTable F State Input) (input_state : State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .everyRowExceptLast table.inductiveConstraint,
    .boundary (.fromStart 0) (equalityConstraint Input input_state),
  ]

theorem tableConstraintsNoEnd_foldl_of_tableConstraints_foldl (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ) (trace : Trace F (ProvablePair State Input)) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold.foldl N
    (List.mapIdx (fun i cs => (cs, env i)) (table.tableConstraints input output))
    trace
    (List.mapIdx (fun i cs => (cs, env i)) (table.tableConstraints input output)) →
  TableConstraintsHold.foldl N
    (List.mapIdx (fun i cs => (cs, env i)) (tableConstraintsNoEnd table input))
    trace
    (List.mapIdx (fun i cs => (cs, env i)) (tableConstraintsNoEnd table input)) := by
  intro h
  induction trace using Trace.every_row_two_rows_induction with
  | zero =>
      simp [tableConstraintsNoEnd, InductiveTable.tableConstraints, TableConstraintsHold.foldl]
  | one row =>
      simp [tableConstraintsNoEnd, InductiveTable.tableConstraints, TableConstraintsHold.foldl] at h ⊢
      exact h.1
  | more curr next rest _ ih_curr =>
      simp [tableConstraintsNoEnd, InductiveTable.tableConstraints, TableConstraintsHold.foldl] at h ⊢
      exact ⟨h.1, h.2.1, ih_curr h.2.2.2⟩

theorem tableConstraintsNoEnd_of_tableConstraints (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env →
  TableConstraintsHold (tableConstraintsNoEnd table input) trace env := by
  intro h
  unfold TableConstraintsHold at h ⊢
  exact tableConstraintsNoEnd_foldl_of_tableConstraints_foldl (table := table) (input := input) (output := output) (N := N) (trace := trace.val) (env := env) h

theorem tableConstraints_output_eq (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) trace env →
  trace.lastRow.1 = output := by
  intro h_constraints
  induction N, trace using TraceOfLength.everyRowTwoRowsInduction' with
  | one row =>
      simp [tableConstraints, TableConstraintsHold, table_norm] at h_constraints
      have h_out : row.1 = output := (equalityConstraint.soundness).mp h_constraints.right
      simpa [TraceOfLength.lastRow, Trace.lastRow, table_norm] using h_out
  | more N curr next rest ih =>
      simp [tableConstraints, TableConstraintsHold, table_norm] at h_constraints
      have h_out := h_constraints.right.left rest.property
      have h_eq : next.1 = output := (equalityConstraint.soundness).mp h_out
      simpa [TraceOfLength.lastRow, Trace.lastRow, table_norm] using h_eq

theorem traceInputs_snoc (N : ℕ) (trace : TraceOfLength F (ProvablePair State Input) N) (row : State F × Input F) :
  traceInputs (State:=State) (Input:=Input) (N := N + 1)
    ⟨trace.val +> row, by rw [Trace.len, trace.property]⟩ =
    (traceInputs trace).concat row.2 := by
  simp [traceInputs, Trace.toList, List.map_concat]

theorem table_soundness_noEnd (table : InductiveTable F State Input) (input : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (tableConstraintsNoEnd table input) trace env →
  trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) := by
  intro h_init h_constraints
  let cs : List (TableOperation (ProvablePair State Input) F × (ℕ → Environment F)) :=
    List.mapIdx (fun i c => (c, env i)) (tableConstraintsNoEnd table input)
  have h_aux :
      ∀ (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N),
      ∀ M, TableConstraintsHold.foldl M cs trace.val cs →
        trace.ForAllRowsWithPrevious (fun row i rest =>
          table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) := by
    intro N trace
    induction N, trace using TraceOfLength.everyRowTwoRowsInduction' with
    | one row =>
        intro M hfold
        simp only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, and_true]
        simp only [cs, tableConstraintsNoEnd, TableConstraintsHold.foldl,
          List.mapIdx_cons, List.mapIdx_nil] at hfold
        have h_eqc : TableConstraint.ConstraintsHoldOnWindow (equalityConstraint Input input) ⟨<+> +> row, rfl⟩ ((env 1) 0) := by
          simpa [Trace.len] using hfold.1
        have h_row : row.1 = input := by
          exact (equalityConstraint.soundness (Input := Input) (row := row) (input_state := input)
            (env := (env 1) 0)).1 (by
              simpa [TableConstraint.ConstraintsHoldOnWindow] using h_eqc)
        rw [h_row]
        simpa [traceInputs, Trace.toList] using h_init
    | more N curr next rest ih =>
        intro M hfold
        let pref : TraceOfLength F (ProvablePair State Input) (N + 1) :=
          ⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩
        simp only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, table_norm]
        simp only [cs, tableConstraintsNoEnd, TableConstraintsHold.foldl,
          List.mapIdx_cons, List.mapIdx_nil] at hfold
        have h_window : table.inductiveConstraint.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ ((env 0) (N + 1)) := by
          simpa [rest.property] using hfold.1
        have h_all_pref :
            pref.ForAllRowsWithPrevious (fun row i rest =>
              table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) := by
          simpa [pref] using ih M hfold.2.2
        have h_all_pref' := h_all_pref
        simp only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, pref, table_norm] at h_all_pref'
        have h_curr : table.Spec input (traceInputs rest) N (traceInputs_length rest) curr.1 := by
          simpa [rest.property] using h_all_pref'.1
        have h_inputs : traceInputs pref = (traceInputs rest).concat curr.2 := by
          simpa [pref] using traceInputs_snoc N rest curr
        have h_next : table.Spec input (traceInputs pref) (N + 1) (traceInputs_length pref) next.1 := by
          simpa [h_inputs, pref, rest.property] using
            (inductiveConstraint_soundness table input (traceInputs rest) N (traceInputs_length rest)
              curr next ((env 0) (N + 1)) (by rw [List.length_concat, traceInputs_length rest])
              h_curr h_window)
        refine ⟨?_, h_all_pref'⟩
        · simpa [pref, rest.property] using h_next
  exact h_aux N trace N (by
    simpa [cs, TableConstraintsHold] using h_constraints)

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ trace.lastRow.1 = output := by
  intro hspec hconstraints
  have hNoEnd : TableConstraintsHold (tableConstraintsNoEnd table input) trace env :=
    tableConstraintsNoEnd_of_tableConstraints (table := table) (input := input) (output := output)
      (N := N) (trace := trace) (env := env) hconstraints
  have hRows :
      trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1) :=
    table_soundness_noEnd (table := table) (input := input) (N := N) (trace := trace) (env := env)
      hspec hNoEnd
  have hOut : trace.lastRow.1 = output :=
    tableConstraints_output_eq (table := table) (input := input) (output := output) (N := N)
      (trace := trace) (env := env) hconstraints
  exact ⟨hRows, hOut⟩


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
