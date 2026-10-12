/-
Copyright (c) 2026 PNP Labs.

One concrete exploration transition. The actual extractor either finds no
eligible vertex and clears the outer countdown, or emits a discovery that
is prepended to the trace while preserving every unselected vertex.
-/

import PNP.Concrete.NormalizerExplorationAccept

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister

def stop : Block 28 := .action (.clear (Frame.frameIndex 27 (0 : Fin 1)))
def stopped (r : State) : State := {r with remaining := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := by
  have checked := Exec.action (.clear (Frame.frameIndex 27 (0 : Fin 1))) r.store
  simpa only [stop, Action.update, Action.instruction, Instruction.update, State.store,
    Frame.set_frame, State.frame, stopped, Store.set, Store.indexCases] using checked

def choose : Block 28 := .branch 19 stop stop accept
def chosen (r : State) : State :=
  if ForwardEdge.present r.core.parent.output then accepted r else stopped r
def chooseFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.core.parent.output then acceptFuel r else 1
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  have checked := EdgeKinds.branch_head (19 : Fin 28) r.store stop accept
    1 (acceptFuel r) (stopped r).store (accepted r).store (stop_exec r) (accept_exec r)
  change Exec choose r.store (chooseFuel r)
    (if ForwardEdge.present r.core.parent.output then (accepted r).store else (stopped r).store) at checked
  cases found : ForwardEdge.present r.core.parent.output <;>
    simpa only [chosen, found, Bool.false_eq_true, ite_false, ite_true] using checked

def body : Block 28 := .seq begin choose
def bodyResult (r : State) : State := chosen (begun r)
def bodyFuel (r : State) : Nat := beginFuel r + chooseFuel (begun r)
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (begin_exec r) (choose_exec (begun r))

theorem body_preserves (r : State) :
    (bodyResult r).core.parent.graph.core.formula = r.core.parent.graph.core.formula ∧
      (bodyResult r).core.parent.graph.core.matching = r.core.parent.graph.core.matching := by
  have first := begun_fields r
  cases found : ForwardEdge.present (begun r).core.parent.output <;>
    simp only [bodyResult, chosen, found, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨first.1, first.2.1⟩
  · have last := accepted_fields (begun r)
    exact ⟨last.1.trans first.1, last.2.1.trans first.2.1⟩

theorem body_progress (r : State) :
    (bodyResult r).remaining = [] ∨ (bodyResult r).remaining = r.remaining.tail := by
  cases found : ForwardEdge.present (begun r).core.parent.output <;>
    simp only [bodyResult, chosen, found, Bool.false_eq_true, ite_false, ite_true]
  · exact Or.inl rfl
  · exact Or.inr ((accepted_fields (begun r)).2.2.2.trans
      (congrArg List.tail (begun_fields r).2.2.2))

def StepFrom (r : State) (unseen : List CNFLiteral) (trace : List TraceData.Row) (after : State) : Prop :=
  (after.remaining = [] ∧ after.core.trace = TraceData.encode trace) ∨
    ∃ vertex parent rest,
      after.remaining = r.remaining.tail ∧
      after.core.pending = SearchVertices.encodeVertices rest ∧
      after.core.trace = TraceData.encode ((vertex, parent) :: trace) ∧
      ExplorationData.Removes vertex unseen rest ∧ Extraction.ParentWithin trace parent

theorem body_range (r : State) (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace) :
    StepFrom r unseen trace (bodyResult r) := by
  have range := begun_range r unseen trace pendingRead traceRead
  have traceStable : (begun r).core.trace = TraceData.encode trace := (begun_fields r).2.2.1.trans traceRead
  cases found : ForwardEdge.present (begun r).core.parent.output with
  | false =>
      apply Or.inl
      simp only [bodyResult, chosen, found, Bool.false_eq_true, ite_false]
      exact ⟨rfl, traceStable⟩
  | true =>
      cases range with
      | inl unavailable =>
          rw [unavailable] at found
          cases found
      | inr available =>
          obtain ⟨vertex, parent, rest, selected, removed, parentRange⟩ := available
          have stored := accepted_selected (begun r) vertex parent rest trace selected traceStable
          apply Or.inr
          refine ⟨vertex, parent, rest, ?_, ?_, ?_, removed, parentRange⟩
          · simp only [bodyResult, chosen, found, ite_true]
            exact (accepted_fields (begun r)).2.2.2.trans (congrArg List.tail (begun_fields r).2.2.2)
          · simpa only [bodyResult, chosen, found, ite_true] using stored.1
          · simpa only [bodyResult, chosen, found, ite_true] using stored.2

theorem body_none (r : State) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (formulaRead : r.core.parent.graph.core.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.core.parent.graph.core.matching = MatchingTable.encode entries)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace)
    (result : Extraction.value clauses entries trace unseen = none) :
    (bodyResult r).remaining = [] ∧ (bodyResult r).core.trace = TraceData.encode trace := by
  have checked := begun_outcome r clauses entries unseen trace formulaRead matchingRead pendingRead traceRead
  rw [result] at checked
  have absent : (begun r).core.parent.output = [false] := checked
  have choice : bodyResult r = stopped (begun r) := by
    unfold bodyResult chosen
    rw [absent]
    rfl
  rw [choice]
  exact ⟨rfl, (begun_fields r).2.2.1.trans traceRead⟩

theorem body_some (r : State) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (vertex : CNFLiteral) (parent : Option CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.core.parent.graph.core.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.core.parent.graph.core.matching = MatchingTable.encode entries)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace)
    (result : Extraction.value clauses entries trace unseen = some ((vertex, parent), rest)) :
    (bodyResult r).remaining = r.remaining.tail ∧
      (bodyResult r).core.pending = SearchVertices.encodeVertices rest ∧
        (bodyResult r).core.trace = TraceData.encode ((vertex, parent) :: trace) := by
  have checked := begun_outcome r clauses entries unseen trace formulaRead matchingRead pendingRead traceRead
  rw [result] at checked
  have selected : Extraction.Selected (begun r).core vertex parent rest := checked
  have present : ForwardEdge.present (begun r).core.parent.output = true := by
    rw [selected.parentRead]
    cases parent <;> rfl
  have stored := accepted_selected (begun r) vertex parent rest trace selected
    ((begun_fields r).2.2.1.trans traceRead)
  simp only [bodyResult, chosen, present, ite_true]
  exact ⟨(accepted_fields (begun r)).2.2.2.trans (congrArg List.tail (begun_fields r).2.2.2),
    stored.1, stored.2⟩

end PNP.Concrete.NormalizerBlocks.Exploration
