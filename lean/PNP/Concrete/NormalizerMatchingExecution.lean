/-
Copyright (c) 2026 PNP Labs.

Closed matching register program. Initialization, repeated search/update
rounds and final table output execute from the original input alone.
These exact execution theorems do not yet assert a polynomial majorant
for the complete program or replace the subsequent tape-runtime proof.
-/
import PNP.Concrete.NormalizerMatchingInitialize

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister Occurrence

def finish : Block 33 := .action (.copy 8 31)
def finished (r : State) : State := r.withRegisters {r.registers with output := r.table}
theorem finish_exec (r : State) : Exec finish r.store 1 (finished r).store := by
  dsimp only [finish, finished, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _
theorem finished_output (r : State) : (finished r).registers.output = r.table := rfl

def block : Block 33 := .seq initializeBlock (.seq loop finish)
def program : Program 33 := block.program 0 8
def result (input : BitString) : State := finished (whole (initialized input)).state
def sourceSteps (input : BitString) : Nat := initializeFuel input + ((whole (initialized input)).fuel + 1)
theorem block_exec (input : BitString) :
    Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (initialize_exec input)
    (Exec.seq (whole_exec (initialized input)) (finish_exec (whole (initialized input)).state))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8
theorem result_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    (result (encode variables clauses)).registers.output =
      MatchingTable.encode (MatchingLoop.fullTable variables clauses) := by
  have start := initialized_canonical variables clauses
  have checked := whole_value variables clauses (List.replicate clauses.length none)
    (initialized (encode variables clauses)) start.1
  rw [start.2] at checked
  rw [result, finished_output]
  exact checked
theorem program_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    (BitRegister.run program (sourceSteps (encode variables clauses) + 1)
      (BitRegister.initial program (encode variables clauses))).store.get 8 =
        MatchingTable.encode (MatchingLoop.fullTable variables clauses) := by
  rw [closed_run, State.get_output, result_canonical]

end PNP.Concrete.NormalizerBlocks.MatchingDriver
