/-
Copyright (c) 2026 PNP Labs.

One complete matching round: assemble and run the search, stop immediately
on a terminal answer, otherwise derive and apply path updates and consume
one outer round. No externally supplied search result or update list enters.
-/
import PNP.Concrete.NormalizerMatchingAdvance

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister Occurrence

def stop : Block 33 := .action (.clear (Frame.frameIndex 29 (3 : Fin 4)))
def stopped (r : State) : State := {r with remaining := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := by
  have checked := Exec.action (.clear (Frame.frameIndex 29 (3 : Fin 4))) r.store
  simpa only [stop, State.store, State.frame, stopped, Action.update, Action.instruction,
    Instruction.update, Frame.set_frame, Store.set, Store.indexCases] using checked

def consume : Block 33 := .action (.pop (Frame.frameIndex 29 (3 : Fin 4)))
def consumed (r : State) : State := {r with remaining := r.remaining.tail}
theorem consume_exec (r : State) : Exec consume r.store 1 (consumed r).store := by
  have checked := Exec.action (.pop (Frame.frameIndex 29 (3 : Fin 4))) r.store
  simpa only [consume, State.store, State.frame, consumed, Action.update, Action.instruction,
    Instruction.update, Frame.get_frame, Frame.set_frame, Store.get, Store.set, Store.indexCases] using checked
def continueRound : Block 33 := .seq advance consume
def continued (r : State) : State := consumed (advanced r)
theorem continueRound_exec (r : State) :
    Exec continueRound r.store (advanceFuel r + 1) (continued r).store :=
  Exec.seq (advance_exec r) (consume_exec (advanced r))

theorem stopped_frame (r : State) :
    (stopped r).width = r.width ∧ (stopped r).formula = r.formula ∧
      (stopped r).table = r.table ∧ (stopped r).remaining = [] := ⟨rfl,rfl,rfl,rfl⟩
theorem continued_frame (r : State) :
    (continued r).width = r.width ∧ (continued r).formula = r.formula ∧
      (continued r).remaining = r.remaining.tail ∧ (continued r).table = (advanced r).table := by
  dsimp only [continued, consumed]
  have frame := advanced_frame r
  exact ⟨frame.1, frame.2.1, congrArg List.tail frame.2.2, rfl⟩
theorem State.get_output (r : State) : r.store.get (8 : Fin 33) = r.registers.output := by
  dsimp only [State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, Store.get, Store.indexCases]
  all_goals rfl

def choose : Block 33 := .branch 8 stop stop continueRound
def chosen (r : State) : State := if ForwardEdge.present r.registers.output then continued r else stopped r
def chooseFuel (r : State) : Nat := 1 + if ForwardEdge.present r.registers.output then advanceFuel r + 1 else 1
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 33) r.store stop continueRound 1 (advanceFuel r + 1)
    (stopped r).store (continued r).store (stop_exec r) (continueRound_exec r)
  rw [State.get_output] at checked
  cases tag : r.registers.output.headD false <;>
    simpa only [choose, chooseFuel, chosen, ForwardEdge.present, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def body : Block 33 := .seq search choose
def bodyResult (r : State) : State := chosen (searchResult r)
def bodyFuel (r : State) : Nat := searchSteps r + chooseFuel (searchResult r)
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (search_exec r) (choose_exec (searchResult r))
theorem body_frame (r : State) :
    (bodyResult r).width = r.width ∧ (bodyResult r).formula = r.formula := by
  have searched := searchResult_frame r
  have advancing := continued_frame (searchResult r)
  cases tag : ForwardEdge.present (searchResult r).registers.output <;>
    simp only [bodyResult, chosen, tag, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨(stopped_frame _).1.trans searched.1, (stopped_frame _).2.1.trans searched.2.1⟩
  · exact ⟨advancing.1.trans searched.1, advancing.2.1.trans searched.2.1⟩
theorem body_progress (r : State) :
    (bodyResult r).remaining = [] ∨ (bodyResult r).remaining = r.remaining.tail := by
  have searched := searchResult_frame r
  have advancing := continued_frame (searchResult r)
  cases tag : ForwardEdge.present (searchResult r).registers.output <;>
    simp only [bodyResult, chosen, tag, Bool.false_eq_true, ite_false, ite_true]
  · exact Or.inl (stopped_frame _).2.2.2
  · exact Or.inr (advancing.2.2.1.trans (congrArg List.tail searched.2.2.2))
theorem body_shorter (r : State) (nonempty : r.remaining ≠ []) :
    (bodyResult r).remaining.length < r.remaining.length := by
  have positive := List.length_pos_iff.mpr nonempty
  cases body_progress r with
  | inl empty => rw [empty, List.length_nil]; exact positive
  | inr consumed => rw [consumed, List.length_tail]; omega

structure Canonical (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (r : State) : Prop where
  width : r.width = List.replicate variables true
  formula : r.formula = GraphQuery.clauseData clauses
  table : r.table = MatchingTable.encode entries
theorem searchResult_canonical (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (r : State) (data : Canonical variables clauses entries r) :
    (searchResult r).registers.output = Search.answer (Search.value variables clauses entries) := by
  rw [searchResult_output, data.width, data.formula, data.table, searchPacket_canonical]
  exact Search.result_canonical variables clauses entries

theorem body_terminal (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (r : State) (data : Canonical variables clauses entries r)
    (trace : List TraceData.Row) (terminal : Search.value variables clauses entries = .terminal trace) :
    (bodyResult r).remaining = [] ∧ (bodyResult r).table = r.table := by
  have output := searchResult_canonical variables clauses entries r data
  rw [terminal] at output
  have tag : ForwardEdge.present (searchResult r).registers.output = false := by rw [output]; rfl
  simp only [bodyResult, chosen, tag, Bool.false_eq_true, ite_false]
  exact ⟨(stopped_frame _).2.2.2, (stopped_frame _).2.2.1.trans (searchResult_frame r).2.2.1⟩

theorem body_augment (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (r : State) (data : Canonical variables clauses entries r)
    (index : Nat) (path : List CNFLiteral)
    (augment : Search.value variables clauses entries = .augment index path) :
    (bodyResult r).remaining = r.remaining.tail ∧
      Canonical variables clauses (MatchingTable.writeAll entries (PathPairs.value path)) (bodyResult r) := by
  have output := searchResult_canonical variables clauses entries r data
  rw [augment] at output
  have tag : ForwardEdge.present (searchResult r).registers.output = true := by rw [output]; rfl
  have searchFrame := searchResult_frame r
  have update := advanced_canonical (searchResult r) entries index path
    (searchFrame.2.2.1.trans data.table) output
  have updateFrame := continued_frame (searchResult r)
  simp only [bodyResult, chosen, tag, ite_true]
  exact ⟨updateFrame.2.2.1.trans (congrArg List.tail searchFrame.2.2.2),
    ⟨updateFrame.1.trans (searchFrame.1.trans data.width),
      updateFrame.2.1.trans (searchFrame.2.1.trans data.formula), updateFrame.2.2.2.trans update⟩⟩

end PNP.Concrete.NormalizerBlocks.MatchingDriver
