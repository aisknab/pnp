/-
Copyright (c) 2026 PNP Labs.

Complete search execution: generate exploration, derive seen variables,
choose a candidate, and return the exact terminal or augmentation result.
No trace, path, seen table, or successful-reconstruction premise is supplied.
-/
import PNP.Concrete.NormalizerSearchOutput

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister

def block : Block 29 := .seq explore (.seq deriveSeen (.seq select decideResult))
def program : Program 29 := block.program 0 8
def result (input : BitString) : State := decided (selected (seenDerived (explored input)))
def sourceSteps (input : BitString) : Nat :=
  exploreFuel input + (deriveSeenFuel (explored input) +
    (selectFuel (seenDerived (explored input)) + decideFuel (selected (seenDerived (explored input)))))

theorem block_exec (input : BitString) :
    Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (explore_exec input) (Exec.seq (deriveSeen_exec (explored input))
    (Exec.seq (select_exec (seenDerived (explored input)))
      (decideResult_exec (selected (seenDerived (explored input))))))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem result_canonical (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    (result (Exploration.encode variables clauses entries)).registers.output = answer (value variables clauses entries) := by
  let input := Exploration.encode variables clauses entries
  let trace := traceValue variables clauses entries
  have exploredTrace : (explored input).core.core.trace = TraceData.encode trace :=
    explored_trace variables clauses entries
  have seen := seenDerived_canonical (explored input) trace exploredTrace
  have seenFrame := seenDerived_frame (explored input)
  have matching : (seenDerived (explored input)).parent.graph.core.matching = MatchingTable.encode entries :=
    seenFrame.2.2.trans (explored_matching variables clauses entries)
  have width : (TableInit.readCount (seenDerived (explored input)).original).state.target =
      List.replicate variables true := by
    rw [seenFrame.2.1]
    exact (Exploration.source_canonical variables clauses entries).1
  have chosen := selected_canonical (seenDerived (explored input)) variables entries (SeenTrace.value trace) width matching seen
  have traceKept := (selected_frame (seenDerived (explored input))).1.trans (seenFrame.1.trans exploredTrace)
  change (decided (selected (seenDerived (explored input)))).registers.output =
    answer (match Candidate.selectFrom entries (SeenTrace.value trace) variables 0 with
      | none => .terminal trace
      | some index => .augment index ((TracePath.value trace ⟨false, index⟩).getD []))
  generalize choice : Candidate.selectFrom entries (SeenTrace.value trace) variables 0 = candidate at chosen ⊢
  cases candidate <;> exact decided_canonical _ _ trace chosen traceKept

end PNP.Concrete.NormalizerBlocks.Search
