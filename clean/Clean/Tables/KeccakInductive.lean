/- Simple Keccak example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Circuit.Extensions
import Clean.Gadgets.Keccak.AbsorbBlock
import Clean.Specs.Keccak256
open Specs.Keccak256
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2 ^ 16 + 2 ^ 8)]

namespace Tables.KeccakInductive
open Gadgets.Keccak256

def table : InductiveTable (F p) KeccakState KeccakBlock where
  step state block := do
    KeccakBlock.normalized block
    AbsorbBlock.circuit { state, block }

  Spec _ blocks i _ state : Prop :=
    state.Normalized
    ∧ state.value = absorbBlocks (blocks.map KeccakBlock.value)

  InputAssumptions i block := block.Normalized

  soundness := by
    intro initialState i env state_var block_var state block blocks _ h_input h_holds spec_previous
    simp_all only [circuit_norm,
      AbsorbBlock.circuit, AbsorbBlock.Assumptions, AbsorbBlock.Spec,
      KeccakBlock.normalized, absorbBlocks]
    rw [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil, List.foldl_concat]

  completeness := by
    simp_all only [InductiveTable.Completeness, circuit_norm, AbsorbBlock.circuit, KeccakBlock.normalized,
      AbsorbBlock.Assumptions, AbsorbBlock.Spec]

-- the input is hard-coded to the initial keccak state of all zeros
def initialState : KeccakState (F p) := .fill 25 (U64.fromByte 0)

lemma initialState_value : (initialState (p:=p)).value = .fill 25 0 := by
  ext i hi
  simp only [initialState, KeccakState.value]
  rw [Vector.getElem_map, Vector.getElem_fill, Vector.getElem_fill, U64.fromByte_value, Fin.val_zero]

lemma initialState_normalized : (initialState (p:=p)).Normalized := by
  simp only [initialState, KeccakState.Normalized, Vector.getElem_fill, U64.fromByte_normalized]
  trivial

def formalTable (output : KeccakState (F p)) := table.toFormal initialState output

-- The table's statement implies that the output state is the result of keccak-hashing some list of input blocks
theorem table_initial_spec: table.Spec (initialState (p:=p)) [] 0 rfl (initialState (p:=p)) := by
  constructor
  · exact initialState_normalized (p:=p)
  · simpa [table, Specs.Keccak256.absorbBlocks] using (initialState_value (p:=p))

theorem tableStatement (output : KeccakState (F p)) : ∀ n > 0, ∀ trace, ∃ blocks, blocks.length = n - 1 ∧
  (formalTable output).statement n trace →
    output.Normalized ∧ output.value = absorbBlocks blocks := by
  intro n hn trace
  refine ⟨(InductiveTable.traceInputs trace.tail).map KeccakBlock.value, ?_⟩
  intro h
  rcases h with ⟨hlen, hstmt⟩
  have hs : table.Spec (initialState (p:=p))
      (InductiveTable.traceInputs trace.tail) (n - 1)
      (InductiveTable.traceInputs_length trace.tail) output := by
    simp only [FormalTable.statement, formalTable, InductiveTable.toFormal] at hstmt
    exact hstmt ⟨hn, table_initial_spec (p:=p)⟩
  simpa [table] using hs


end Tables.KeccakInductive
