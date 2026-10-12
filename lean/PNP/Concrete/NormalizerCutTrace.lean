/-
Copyright (c) 2026 PNP Labs.

The final cut trace is computed after internally generated matching.
The caller supplies neither a table nor a trace. Scratch is reset before
the final exploration while width, formula and matching stay protected.
-/
import PNP.Concrete.NormalizerMatchingPolynomial

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver

theorem finished_frame (r : State) :
    (finished r).width = r.width ∧ (finished r).formula = r.formula ∧
      (finished r).table = r.table := ⟨rfl,rfl,rfl⟩
theorem finished_table_output (r : State) :
    (finished r).table = (finished r).registers.output := rfl
theorem Within.finished {bound : Nat} {r : State} (data : Within bound r) :
    Within bound (finished r) := by
  have frame := finished_frame r
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frame.1]; exact data.width
  · rw [frame.2.1]; exact data.formula
  · rw [frame.1, frame.2.1]; exact data.indexRange
  · obtain ⟨entries, read, count, indices⟩ := data.table
    exact ⟨entries, frame.2.2.trans read, count, indices⟩

theorem result_frame (input : BitString) :
    (result input).width = Exploration.sourceWidth input ∧
      (result input).formula = Exploration.sourceFormula input := by
  have frame := scan_frame ((initialized input).remaining.length + 1) (initialized input)
  have start := initialized_fields input
  rw [result, (finished_frame _).1, (finished_frame _).2.1]
  exact ⟨frame.1.trans start.1, frame.2.trans start.2.1⟩

theorem result_table_output (input : BitString) :
    (result input).table = (result input).registers.output := by
  rw [result]
  exact finished_table_output _

theorem result_within (input : BitString) :
    Within (6 * input.length + 6) (result input) := by
  unfold result
  exact (whole_within _ (initialized input) (initialized_within input)).finished

theorem result_data (variables : Nat) (clauses : List (List CNFLiteral)) :
    Canonical variables clauses (MatchingLoop.fullTable variables clauses)
      (result (encode variables clauses)) := by
  have frame := result_frame (encode variables clauses)
  have input := input_fields variables clauses
  refine ⟨frame.1.trans input.1, frame.2.trans input.2.1, ?_⟩
  rw [result_table_output, result_canonical]

end PNP.Concrete.NormalizerBlocks.MatchingDriver

namespace PNP.Concrete.NormalizerBlocks.Exploration
theorem finished_output (r : State) : (finished r).registers.output = r.core.trace := rfl
theorem result_trace_output (input : BitString) :
    (result input).core.trace = (result input).registers.output := by
  rw [result, finished_trace, finished_output]
end PNP.Concrete.NormalizerBlocks.Exploration

namespace PNP.Concrete.NormalizerBlocks.CutTrace
open BitRegister
abbrev State := MatchingDriver.State

def exploreCore : Block 29 := .seq MatchingCall.resetSearch Search.explore
def coreResult (r : Search.State) : Search.State := Search.explored r.registers.input
def coreFuel (r : Search.State) : Nat := 29 + Search.exploreFuel r.registers.input
theorem exploreCore_exec (r : Search.State) :
    Exec exploreCore r.store (coreFuel r) (coreResult r).store :=
  Exec.seq (MatchingCall.resetSearch_exec r) (Search.explore_exec r.registers.input)

def explore : Block 33 := MatchingDriver.liftSearch exploreCore
def explored (r : State) : State := r.withCore (coreResult r.core)
def exploreFuel (r : State) : Nat := coreFuel r.core
theorem explore_exec (r : State) :
    Exec explore r.store (exploreFuel r) (explored r).store :=
  MatchingDriver.liftSearch_exec _ r _ _ (exploreCore_exec r.core)
theorem explored_frame (r : State) :
    (explored r).width = r.width ∧ (explored r).formula = r.formula ∧
      (explored r).table = r.table := ⟨rfl,rfl,rfl⟩

def emit : Block 33 :=
  MatchingDriver.liftSearch (Search.liftExploration Exploration.finish)
def emitted (r : State) : State :=
  r.withCore (r.core.withCore (Exploration.finished r.core.core))
theorem emit_exec (r : State) : Exec emit r.store 1 (emitted r).store :=
  MatchingDriver.liftSearch_exec _ r _ _
    (Search.liftExploration_exec _ r.core _ _ (Exploration.finish_exec r.core.core))
theorem emitted_output (r : State) :
    (emitted r).registers.output = r.core.core.core.trace := rfl
theorem explored_trace_output (r : State) :
    (explored r).core.core.core.trace = (Exploration.result r.registers.input).registers.output := by
  dsimp only [explored, MatchingDriver.State.withCore, coreResult, Search.explored]
  exact Exploration.result_trace_output _
theorem emitted_frame (r : State) :
    (emitted r).width = r.width ∧ (emitted r).formula = r.formula ∧
      (emitted r).table = r.table := ⟨rfl,rfl,rfl⟩

def packet (input : BitString) : BitString :=
  MatchingDriver.searchPacket (MatchingDriver.result input).width
    (MatchingDriver.result input).formula (MatchingDriver.result input).table
def packed (input : BitString) : State :=
  MatchingDriver.searchPacked (MatchingDriver.result input)
theorem packed_input (input : BitString) : (packed input).registers.input = packet input :=
  MatchingDriver.searchPacked_input (MatchingDriver.result input)
def scanned (input : BitString) : State := explored (packed input)
def result (input : BitString) : State := emitted (scanned input)
def block : Block 33 :=
  .seq MatchingDriver.block <| .seq MatchingDriver.packSearch (.seq explore emit)
def program : Program 33 := block.program 0 8
def sourceSteps (input : BitString) : Nat :=
  MatchingDriver.sourceSteps input +
    (MatchingDriver.packSearchFuel (MatchingDriver.result input) + (exploreFuel (packed input) + 1))

theorem block_exec (input : BitString) :
    Exec block (MatchingDriver.initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (MatchingDriver.block_exec input) <|
    Exec.seq (MatchingDriver.packSearch_exec (MatchingDriver.result input)) <|
      Exec.seq (explore_exec (packed input)) (emit_exec (scanned input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (MatchingDriver.initial input).store⟩ := rfl
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem packet_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    packet (MatchingDriver.encode variables clauses) =
      Exploration.encode variables clauses (MatchingLoop.fullTable variables clauses) := by
  have data := MatchingDriver.result_data variables clauses
  unfold packet
  rw [data.width, data.formula, data.table]
  exact MatchingDriver.searchPacket_canonical _ _ _

theorem result_trace (input : BitString) :
    (result input).registers.output = (Exploration.result (packet input)).registers.output := by
  rw [result, emitted_output, scanned, explored_trace_output, packed_input]
theorem result_frame (input : BitString) :
    (result input).width = (MatchingDriver.result input).width ∧
      (result input).formula = (MatchingDriver.result input).formula ∧
        (result input).table = (MatchingDriver.result input).table := by
  have first := MatchingDriver.searchPacked_frame (MatchingDriver.result input)
  have second := explored_frame (packed input)
  have third := emitted_frame (scanned input)
  exact ⟨third.1.trans (second.1.trans first.1),
    third.2.1.trans (second.2.1.trans first.2.1),
    third.2.2.trans (second.2.2.trans first.2.2.1)⟩

theorem result_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    (result (MatchingDriver.encode variables clauses)).registers.output =
      TraceData.encode (Search.traceValue variables clauses (MatchingLoop.fullTable variables clauses)) := by
  rw [result_trace, packet_canonical, ← Exploration.polynomial_output,
    Exploration.polynomial_canonical]
  rfl

theorem result_matching (variables : Nat) (clauses : List (List CNFLiteral)) :
    (result (MatchingDriver.encode variables clauses)).table =
      MatchingTable.encode (MatchingLoop.fullTable variables clauses) := by
  rw [(result_frame _).2.2, MatchingDriver.result_table_output, MatchingDriver.result_canonical]

end PNP.Concrete.NormalizerBlocks.CutTrace
