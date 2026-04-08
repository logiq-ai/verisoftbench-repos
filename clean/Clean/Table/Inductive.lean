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

theorem inductiveConstraint_window_get_curr (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  let env' := TableConstraint.windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env
  ∀ i (hi : i < size (ProvablePair State Input)),
    env'.get i = (toElements (M := ProvablePair State Input) curr)[i]'hi := by
  dsimp
  intro i hi
  have hfirst : i < size State + size Input := by
    simpa using hi
  have hmid :
      i < (size State + size Input) +
            (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
              (size State + size Input) := by
    exact lt_of_lt_of_le hfirst (by omega)
  have hioff :
      i < (size State + size Input) +
            (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
              (size State + size Input) +
            (size State + size Input) := by
    exact lt_of_lt_of_le hmid (by omega)
  simpa [hioff, hmid, hfirst, Vector.getElem_append, TraceOfLength.get, Trace.getLeFromBottom,
    _root_.Row.get, ProvablePair.instance, Vector.mapRange_zero, Vector.append_empty,
    TableConstraint.windowEnv, InductiveTable.inductiveConstraint, table_assignment_norm, circuit_norm,
    CellAssignment.assignmentFromCircuit_offset, CellAssignment.assignmentFromCircuit_vars]

theorem inductiveConstraint_window_get_next (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  let env' := TableConstraint.windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env
  let nextOffset :=
    (size State) + (size Input) +
      (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength ((size State) + (size Input))
  ∀ i (hi : i < size (ProvablePair State Input)),
    env'.get (nextOffset + i) = (toElements (M := ProvablePair State Input) next)[i]'hi := by
  dsimp
  intro i hi
  have hi' : i < size State + size Input := by
    simpa [ProvablePair.instance] using hi
  have houter :
      (size State + size Input) +
            (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
              (size State + size Input) +
          i <
        (size State + size Input) +
            (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
              (size State + size Input) +
          (size State + size Input) := by
    omega
  have hge_first :
      size State + size Input ≤
        (size State + size Input) +
          (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
            (size State + size Input) +
          i := by
    omega
  have hafter_first :
      (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
            (size State + size Input) ≤
        ((size State + size Input) +
              (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength
                (size State + size Input) +
              i) -
          (size State + size Input) := by
    omega
  simpa [houter, hge_first, hafter_first,
    Vector.getElem_append, Trace.getLeFromBottom, _root_.Row.get,
    ProvablePair.instance, Vector.mapRange_zero, Vector.append_empty,
    TableConstraint.windowEnv, InductiveTable.inductiveConstraint,
    table_assignment_norm, circuit_norm,
    CellAssignment.assignmentFromCircuit_offset, CellAssignment.assignmentFromCircuit_vars]

theorem inductiveConstraint_window_eval (table : InductiveTable F State Input) (curr next : State F × Input F) (aux_env : Environment F) :
  let env' := TableConstraint.windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env
  let nextOffset :=
    (size State) + (size Input) +
      (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength ((size State) + (size Input))
  eval env' (varFromOffset (ProvablePair State Input) 0) = curr ∧
  eval env' (varFromOffset (ProvablePair State Input) nextOffset) = next := by
  dsimp
  constructor
  · rw [ProvableType.ext_iff]
    intro i hi
    rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
    simpa using inductiveConstraint_window_get_curr table curr next aux_env i hi
  · rw [ProvableType.ext_iff]
    intro i hi
    rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
    simpa using inductiveConstraint_window_get_next table curr next aux_env i hi

theorem inductiveConstraint_soundness (table : InductiveTable F State Input) (initialState : State F)
  (xs : List (Input F)) (i : ℕ) (hxs : xs.length = i)
  (curr next : State F × Input F) (aux_env : Environment F) :
  TableConstraint.ConstraintsHoldOnWindow (table.inductiveConstraint) ⟨<+> +> curr +> next, rfl⟩ aux_env →
  table.Spec initialState xs i hxs curr.1 →
  table.Spec initialState (xs.concat curr.2) (i + 1) (hxs ▸ List.length_concat) next.1 := by
  intro h_hold h_spec
  let env' := TableConstraint.windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, rfl⟩ aux_env
  let nextOffset :=
    (size State) + (size Input) +
      (table.step (varFromOffset State 0) (varFromOffset Input (size State))).localLength ((size State) + (size Input))
  have h_eval := inductiveConstraint_window_eval table curr next aux_env
  dsimp [env', nextOffset] at h_eval
  rcases h_eval with ⟨h_curr, h_next⟩
  have h_curr_state : eval env' (varFromOffset State 0) = curr.1 := by
    simpa [env', circuit_norm] using congrArg Prod.fst h_curr
  have h_curr_input : eval env' (varFromOffset Input (size State)) = curr.2 := by
    simpa [env', circuit_norm] using congrArg Prod.snd h_curr
  have h_next_state : eval env' (varFromOffset State nextOffset) = next.1 := by
    simpa [env', nextOffset, circuit_norm] using congrArg Prod.fst h_next
  have h_hold' :
      Circuit.ConstraintsHold.Soundness env'
        ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).operations
          ((size State) + (size Input))) ∧
      eval env' (varFromOffset State nextOffset) =
        eval env'
          ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).output
            ((size State) + (size Input))) := by
    simpa [env', nextOffset, TableConstraint.ConstraintsHoldOnWindow, InductiveTable.inductiveConstraint,
      table_norm, table_assignment_norm, circuit_norm] using h_hold
  have h_out_spec :=
    table.soundness initialState i env' (varFromOffset State 0) (varFromOffset Input (size State))
      curr.1 curr.2 xs hxs ⟨h_curr_state, h_curr_input⟩ h_hold'.1 h_spec
  have h_out_eq :
      eval env'
          ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).output
            ((size State) + (size Input))) =
        next.1 := by
    rw [← h_hold'.2, h_next_state]
  simpa [h_out_eq] using h_out_spec

theorem tableConstraints_prefix_foldl_iff (table : InductiveTable F State Input) (input output : State F) (N : ℕ)
  (rest : TraceOfLength F (ProvablePair State Input) N)
  (curr : State F × Input F) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold.foldl (N + 2)
    ((table.tableConstraints input output).mapIdx (fun i cs => (cs, env i)))
    (rest.val +> curr)
    ((table.tableConstraints input output).mapIdx (fun i cs => (cs, env i)))
  ↔
  TableConstraintsHold (table.tableConstraints input curr.1)
    ((⟨rest.val +> curr, by rw [Trace.len, rest.property]⟩ :
      TraceOfLength F (ProvablePair State Input) (N + 1))) env := by
  have h_base :
      ∀ (trace : Trace F (ProvablePair State Input)) (extra₁ extra₂ : ℕ),
        TableConstraintsHold.foldl (trace.len + extra₁)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
          trace
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
        ↔
        TableConstraintsHold.foldl (trace.len + extra₂)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
          trace
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)] := by
    intro trace
    induction trace using Trace.every_row_two_rows_induction with
    | zero =>
        intro extra₁ extra₂
        simp [TableConstraintsHold.foldl, table_norm]
    | one row =>
        intro extra₁ extra₂
        simp [TableConstraintsHold.foldl, table_norm]
    | more curr next rest ih_rest ih_prev =>
        intro extra₁ extra₂
        simp [TableConstraintsHold.foldl, table_norm]
        intro _
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Trace.len] using
          ih_prev (extra₁ + 1) (extra₂ + 1)
  have h_dropEnd :
      ∀ (trace : Trace F (ProvablePair State Input)) (extra : ℕ), 0 < extra → ∀ out : State F,
        TableConstraintsHold.foldl (trace.len + extra)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
            (boundary (.fromEnd 0) (equalityConstraint Input out), env 2)]
          trace
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
            (boundary (.fromEnd 0) (equalityConstraint Input out), env 2)]
        ↔
        TableConstraintsHold.foldl (trace.len + extra)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
          trace
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)] := by
    intro trace
    induction trace using Trace.every_row_two_rows_induction with
    | zero =>
        intro extra hextra out
        simp [TableConstraintsHold.foldl, table_norm]
    | one row =>
        intro extra hextra out
        simp [TableConstraintsHold.foldl, table_norm]
        intro _ hEq
        exact (hextra.ne' hEq.symm).elim
    | more prev curr rest ih_rest ih_prev =>
        intro extra hextra out
        simp [TableConstraintsHold.foldl, table_norm, hextra.ne']
        intro _
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Trace.len] using
          ih_prev (extra + 1) (Nat.succ_pos _) out
  have h_top :
      ∀ (trace : Trace F (ProvablePair State Input)) (top : State F × Input F),
        TableConstraintsHold.foldl (trace.len + 1)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
            (boundary (.fromEnd 0) (equalityConstraint Input top.1), env 2)]
          (trace +> top)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
            (boundary (.fromEnd 0) (equalityConstraint Input top.1), env 2)]
        ↔
        TableConstraintsHold.foldl (trace.len + 1)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
          (trace +> top)
          [(everyRowExceptLast table.inductiveConstraint, env 0),
            (boundary (.fromStart 0) (equalityConstraint Input input), env 1)] := by
    intro trace top
    cases trace with
    | empty =>
        simp [TableConstraintsHold.foldl, equalityConstraint.soundness, table_norm]
    | cons rest row =>
        simp [TableConstraintsHold.foldl, equalityConstraint.soundness, table_norm]
        intro _
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Trace.len] using
          h_dropEnd (rest +> row) 1 (Nat.succ_pos _) top.1
  have h_left :
      TableConstraintsHold.foldl (N + 2)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
          (boundary (.fromEnd 0) (equalityConstraint Input output), env 2)]
        (rest.val +> curr)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
          (boundary (.fromEnd 0) (equalityConstraint Input output), env 2)]
      ↔
      TableConstraintsHold.foldl (N + 2)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
        (rest.val +> curr)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)] := by
    simpa [Trace.len, rest.property, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      h_dropEnd (rest.val +> curr) 1 (Nat.succ_pos _) output
  have h_mid :
      TableConstraintsHold.foldl (N + 2)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
        (rest.val +> curr)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
      ↔
      TableConstraintsHold.foldl (N + 1)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
        (rest.val +> curr)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)] := by
    simpa [Trace.len, rest.property, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      h_base (rest.val +> curr) 1 0
  have h_right :
      TableConstraintsHold.foldl (N + 1)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
          (boundary (.fromEnd 0) (equalityConstraint Input curr.1), env 2)]
        (rest.val +> curr)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1),
          (boundary (.fromEnd 0) (equalityConstraint Input curr.1), env 2)]
      ↔
      TableConstraintsHold.foldl (N + 1)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)]
        (rest.val +> curr)
        [(everyRowExceptLast table.inductiveConstraint, env 0),
          (boundary (.fromStart 0) (equalityConstraint Input input), env 1)] := by
    simpa [Trace.len, rest.property, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      h_top rest.val curr
  simpa [TableConstraintsHold, tableConstraints] using h_left.trans (h_mid.trans h_right.symm)

theorem tableConstraints_cons_cons_split (table : InductiveTable F State Input) (input output : State F) (N : ℕ)
  (rest : TraceOfLength F (ProvablePair State Input) N)
  (curr next : State F × Input F) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output)
    ((⟨rest.val +> curr +> next, by rw [Trace.len, Trace.len, rest.property]⟩ :
      TraceOfLength F (ProvablePair State Input) (N + 2))) env →
    TableConstraint.ConstraintsHoldOnWindow (table.inductiveConstraint) ⟨<+> +> curr +> next, rfl⟩ (env 0 (N + 1)) ∧
    TableConstraintsHold (table.tableConstraints input curr.1)
      ((⟨rest.val +> curr, by rw [Trace.len, rest.property]⟩ :
        TraceOfLength F (ProvablePair State Input) (N + 1))) env ∧
    next.1 = output := by
  intro h
  have hsplit :
      TableConstraint.ConstraintsHoldOnWindow (table.inductiveConstraint) ⟨<+> +> curr +> next, rfl⟩ (env 0 (N + 1)) ∧
      TableConstraintsHold.foldl (N + 2)
        ((table.tableConstraints input output).mapIdx (fun i cs => (cs, env i)))
        (rest.val +> curr)
        ((table.tableConstraints input output).mapIdx (fun i cs => (cs, env i))) ∧
      next.1 = output := by
    simpa [TableConstraintsHold, tableConstraints, equalityConstraint.soundness, table_norm,
      rest.property, and_assoc, and_left_comm, and_comm] using h
  refine ⟨hsplit.1, ?_, hsplit.2.2⟩
  exact (tableConstraints_prefix_foldl_iff table input output N rest curr env).mp hsplit.2.1

theorem tableConstraints_singleton_state_eq (table : InductiveTable F State Input) (input output : State F)
  (row : State F × Input F) (env : ℕ → ℕ → Environment F) :
  TableConstraintsHold (table.tableConstraints input output) ⟨<+> +> row, rfl⟩ env →
    row.1 = input ∧ row.1 = output := by
  intro h
  simpa [TableConstraintsHold, InductiveTable.tableConstraints, equalityConstraint.soundness, table_norm] using h

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : ℕ → ℕ → Environment F) :
  table.Spec input [] 0 rfl input →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1)
    ∧ trace.lastRow.1 = output := by
  intro h_input h_constraints
  induction N, trace using TraceOfLength.everyRowTwoRowsInduction' generalizing output with
  | one row =>
      have h_eq := tableConstraints_singleton_state_eq table input output row env h_constraints
      rcases h_eq with ⟨hrow_input, hrow_output⟩
      constructor
      · simpa only [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, traceInputs, Trace.toList, List.map_nil, hrow_input] using And.intro h_input trivial
      · simpa only [TraceOfLength.lastRow] using hrow_output
  | more N curr next rest ih =>
      have h_split := tableConstraints_cons_cons_split table input output N rest curr next env h_constraints
      rcases h_split with ⟨h_window, h_prefix_constraints, h_output⟩
      have h_ih := ih curr.1 (by simpa [Trace.len, rest.property] using h_prefix_constraints)
      rcases h_ih with ⟨h_prefix_rows, h_curr_eq⟩
      have h_curr_spec : table.Spec input (traceInputs rest) N (traceInputs_length rest) curr.1 := by
        simpa [TraceOfLength.lastRow, TraceOfLength.tail, Trace.tail, Trace.len, rest.property] using
          (TraceOfLength.lastRow_of_forAllWithPrevious
            (N := ⟨N + 1, Nat.succ_pos N⟩)
            (trace := (⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ : TraceOfLength F (ProvablePair State Input) (N + 1)))
            h_prefix_rows)
      have h_next_spec : table.Spec input
          (traceInputs (⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ : TraceOfLength F (ProvablePair State Input) (N + 1)))
          (N + 1)
          (traceInputs_length (⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ : TraceOfLength F (ProvablePair State Input) (N + 1)))
          next.1 := by
        simpa [traceInputs, Trace.toList, List.map_concat, Trace.len, rest.property] using
          inductiveConstraint_soundness table input (traceInputs rest) N (traceInputs_length rest)
            curr next (env 0 (N + 1)) h_window h_curr_spec
      constructor
      · simpa [TraceOfLength.ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, Trace.len, rest.property] using
          And.intro h_next_spec h_prefix_rows
      · simpa only [TraceOfLength.lastRow] using h_output


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
