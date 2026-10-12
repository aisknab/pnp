/-
Copyright (c) 2026 PNP Labs.

One full trace-membership iteration. It consumes the node and optional
predecessor fields, compares the actual signed vertex, and stops on a
match. Only matching node identity matters; predecessor data is skipped.
-/

import PNP.Concrete.NormalizerMemberCompare

namespace PNP.Concrete.NormalizerBlocks.TraceMember

open BitRegister

def accept : Block 21 :=
  .seq (.action (.clear 19)) (.seq (.action (.push 19 true)) (.action (.clear 16)))
def accepted (r : State) : State := {r with pending := [], output := [true]}
theorem accept_exec (r : State) : Exec accept r.store 3 (accepted r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def choose : Block 21 := .branch 8 .skip .skip accept
def chosen (r : State) : State := if ForwardEdge.present r.registers.output then accepted r else r
def chooseFuel (r : State) : Nat := if ForwardEdge.present r.registers.output then 4 else 2
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 21) r.store .skip accept 1 3 r.store (accepted r).store
    (Exec.skip r.store) (accept_exec r)
  change Exec choose r.store (1 + if ForwardEdge.present r.registers.output then 3 else 1)
    (if ForwardEdge.present r.registers.output then (accepted r).store else r.store) at checked
  cases found : ForwardEdge.present r.registers.output <;>
    simpa only [chosen, chooseFuel, found, Bool.false_eq_true, ite_false, ite_true] using checked
theorem chooseFuel_bound (r : State) : chooseFuel r ≤ 4 := by
  unfold chooseFuel
  cases ForwardEdge.present r.registers.output <;> decide

theorem chosen_preserves (r : State) :
    (chosen r).targetIndex = r.targetIndex ∧ (chosen r).targetTag = r.targetTag ∧
      (chosen r).graph.core.formula = r.graph.core.formula ∧
        (chosen r).graph.core.matching = r.graph.core.matching := by
  cases found : ForwardEdge.present r.registers.output <;>
    simp only [chosen, found, Bool.false_eq_true, ite_false, ite_true, accepted] <;> trivial
theorem chosen_pending (r : State) : (chosen r).pending = [] ∨ (chosen r).pending = r.pending := by
  cases found : ForwardEdge.present r.registers.output
  · apply Or.inr
    simp only [chosen, found, Bool.false_eq_true, ite_false]
  · apply Or.inl
    simp only [chosen, found, ite_true, accepted]

def body : Block 21 := .seq ParentQuery.readNode (.seq comparison choose)
def bodyResult (r : State) : State := chosen (compared (ParentQuery.nodeResult r))
def bodyFuel (r : State) : Nat :=
  ParentQuery.nodeFuel r + (comparisonFuel (ParentQuery.nodeResult r) + chooseFuel (compared (ParentQuery.nodeResult r)))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (ParentQuery.readNode_exec r) (Exec.seq (comparison_exec (ParentQuery.nodeResult r))
    (choose_exec (compared (ParentQuery.nodeResult r))))

def stepBound (r : State) : Nat := 28 * r.pending.length + 80
theorem bodyFuel_bound (r : State) : bodyFuel r ≤ stepBound r := by
  have parse := ParentQuery.nodeFuel_bound r
  have index := TraceData.nodeIndex_length r.pending
  have compare := comparisonFuel_bound (ParentQuery.nodeResult r)
  rw [(ParentQuery.node_fields r).2.1] at compare
  have pick := chooseFuel_bound (compared (ParentQuery.nodeResult r))
  unfold bodyFuel stepBound
  omega

theorem body_preserves (r : State) :
    (bodyResult r).targetIndex = r.targetIndex ∧ (bodyResult r).targetTag = r.targetTag ∧
      (bodyResult r).graph.core.formula = r.graph.core.formula ∧
        (bodyResult r).graph.core.matching = r.graph.core.matching := by
  have parse := ParentQuery.node_preserves r
  have compare := comparison_preserves (ParentQuery.nodeResult r)
  have pick := chosen_preserves (compared (ParentQuery.nodeResult r))
  exact ⟨pick.1.trans (compare.2.1.trans parse.1),
    pick.2.1.trans (compare.2.2.1.trans parse.2.1),
    pick.2.2.1.trans (compare.2.2.2.1.trans parse.2.2.1),
    pick.2.2.2.trans (compare.2.2.2.2.1.trans parse.2.2.2.1)⟩

theorem body_progress (r : State) (nonempty : r.pending ≠ []) :
    (bodyResult r).pending = [] ∨ (bodyResult r).pending.length < r.pending.length := by
  cases chosen_pending (compared (ParentQuery.nodeResult r)) with
  | inl stopped => exact Or.inl stopped
  | inr next =>
      apply Or.inr
      change (chosen (compared (ParentQuery.nodeResult r))).pending.length < _
      rw [next, (comparison_preserves (ParentQuery.nodeResult r)).1]
      exact ParentQuery.node_shorter r nonempty
theorem body_size (r : State) (nonempty : r.pending ≠ []) : (bodyResult r).pending.length ≤ r.pending.length := by
  cases body_progress r nonempty with
  | inl stopped => rw [stopped]; exact Nat.zero_le _
  | inr smaller => exact Nat.le_of_lt smaller
theorem stepBound_mono (r : State) (nonempty : r.pending ≠ []) : stepBound (bodyResult r) ≤ stepBound r := by
  have bound := body_size r nonempty
  unfold stepBound
  omega

theorem row_comparison (r : State) (target : CNFLiteral) (entry : TraceData.Row) (suffix : BitString)
    (indexRead : r.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.targetTag = target.positive)
    (traceRead : r.pending = TraceData.row entry suffix) :
    (compared (ParentQuery.nodeResult r)).registers.output = [same entry.1 target] := by
  rw [comparison_output, (ParentQuery.node_fields r).2.1, (ParentQuery.node_preserves r).1,
    (ParentQuery.node_fields r).2.2.2.2.1, (ParentQuery.node_preserves r).2.1,
    traceRead, TraceData.nodeIndex_canonical, indexRead, List.length_replicate, List.length_replicate, tagRead]
  rfl

theorem body_row (r : State) (target : CNFLiteral) (entry : TraceData.Row) (suffix : BitString)
    (indexRead : r.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.targetTag = target.positive)
    (traceRead : r.pending = TraceData.row entry suffix) :
    (bodyResult r).pending = (if same entry.1 target then [] else suffix) ∧
      (bodyResult r).output = (if same entry.1 target then [true] else r.output) := by
  have query := row_comparison r target entry suffix indexRead tagRead traceRead
  have found : ForwardEdge.present (compared (ParentQuery.nodeResult r)).registers.output = same entry.1 target := by
    rw [query]
    rfl
  have next : (compared (ParentQuery.nodeResult r)).pending = suffix := by
    rw [(comparison_preserves (ParentQuery.nodeResult r)).1, (ParentQuery.node_fields r).1,
      traceRead, TraceData.next_canonical]
  cases equal : same entry.1 target with
  | false =>
      have selectedEq : bodyResult r = compared (ParentQuery.nodeResult r) := by
        unfold bodyResult chosen
        rw [found, equal]
        rfl
      rw [selectedEq]
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨next, (comparison_preserves (ParentQuery.nodeResult r)).2.2.2.2.2.trans (ParentQuery.node_preserves r).2.2.2.2⟩
  | true =>
      have selectedEq : bodyResult r = accepted (compared (ParentQuery.nodeResult r)) := by
        unfold bodyResult chosen
        rw [found, equal]
        rfl
      rw [selectedEq]
      exact ⟨rfl, rfl⟩

end PNP.Concrete.NormalizerBlocks.TraceMember
