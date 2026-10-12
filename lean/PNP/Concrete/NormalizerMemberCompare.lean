/-
Copyright (c) 2026 PNP Labs.

Actual signed-vertex comparison for trace membership. Index words are
compared by finite counter instructions, then unequal vertex kinds clear
the result. The original trace, target and graph data remain protected.
-/

import PNP.Concrete.NormalizerTraceCount

namespace PNP.Concrete.NormalizerBlocks.TraceMember

open BitRegister
abbrev State := ParentQuery.State

def prepare : Block 21 :=
  .seq (.action (.copy 1 20)) (.seq (.action (.copy 2 17)) (.action (.clear 3)))
def prepared (r : State) : State :=
  r.withRegisters {r.registers with target := r.currentIndex, remaining := r.targetIndex, excess := []}
theorem prepare_exec (r : State) : Exec prepare r.store 3 (prepared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def countQuery : Block 21 := .seq prepare (ParentQuery.liftCore TraceCount.block)
def counted (r : State) : State := r.withRegisters (TraceCount.result (prepared r).registers)
def countFuel (r : State) : Nat := 3 + TraceCount.fuel (prepared r).registers
theorem countQuery_exec (r : State) : Exec countQuery r.store (countFuel r) (counted r).store :=
  Exec.seq (prepare_exec r) (ParentQuery.liftCore_exec _ (prepared r) _ _ (TraceCount.block_exec (prepared r).registers))
theorem counted_output (r : State) :
    (counted r).registers.output = [r.currentIndex.length == r.targetIndex.length] :=
  TraceCount.result_output (prepared r).registers rfl
theorem countFuel_bound (r : State) : countFuel r ≤ 4 * r.currentIndex.length + 8 := by
  have bound := TraceCount.fuel_bound (prepared r).registers
  change TraceCount.fuel (prepared r).registers ≤ 4 * r.currentIndex.length + 5 at bound
  unfold countFuel
  omega

def reject : Block 21 := ParentQuery.liftCore (TraceCount.emit false)
def rejected (r : State) : State := r.withRegisters (TraceCount.emitted false r.registers)
theorem reject_exec (r : State) : Exec reject r.store 2 (rejected r).store :=
  ParentQuery.liftCore_exec _ r _ _ (TraceCount.emit_exec false r.registers)

def zeroKind : Block 21 := .branch 18 .skip .skip reject
def oneKind : Block 21 := .branch 18 reject reject .skip
def filter : Block 21 := .branch 14 zeroKind zeroKind oneKind
def filtered (r : State) : State :=
  if ForwardEdge.present r.graph.first then
    if ForwardEdge.present r.targetTag then r else rejected r
  else if ForwardEdge.present r.targetTag then rejected r else r
def filterFuel (r : State) : Nat :=
  2 + if ForwardEdge.present r.graph.first then
    if ForwardEdge.present r.targetTag then 1 else 2
  else if ForwardEdge.present r.targetTag then 2 else 1

theorem filter_exec (r : State) : Exec filter r.store (filterFuel r) (filtered r).store := by
  have low := EdgeKinds.branch_head (18 : Fin 21) r.store .skip reject 1 2 r.store (rejected r).store
    (Exec.skip r.store) (reject_exec r)
  have high := EdgeKinds.branch_head (18 : Fin 21) r.store reject .skip 2 1 (rejected r).store r.store
    (reject_exec r) (Exec.skip r.store)
  change Exec zeroKind r.store (1 + if ForwardEdge.present r.targetTag then 2 else 1)
    (if ForwardEdge.present r.targetTag then (rejected r).store else r.store) at low
  change Exec oneKind r.store (1 + if ForwardEdge.present r.targetTag then 1 else 2)
    (if ForwardEdge.present r.targetTag then r.store else (rejected r).store) at high
  have checked := EdgeKinds.branch_head (14 : Fin 21) r.store zeroKind oneKind _ _ _ _ low high
  change Exec filter r.store
    (1 + if ForwardEdge.present r.graph.first then
      1 + if ForwardEdge.present r.targetTag then 1 else 2
    else 1 + if ForwardEdge.present r.targetTag then 2 else 1)
    (if ForwardEdge.present r.graph.first then
      if ForwardEdge.present r.targetTag then r.store else (rejected r).store
    else if ForwardEdge.present r.targetTag then (rejected r).store else r.store) at checked
  cases first : ForwardEdge.present r.graph.first <;> cases second : ForwardEdge.present r.targetTag <;>
    simpa only [filtered, filterFuel, first, second, Bool.false_eq_true, ite_false, ite_true] using checked

theorem filterFuel_bound (r : State) : filterFuel r ≤ 4 := by
  unfold filterFuel
  cases ForwardEdge.present r.graph.first <;> cases ForwardEdge.present r.targetTag <;> decide

theorem filtered_output (r : State) :
    (filtered r).registers.output =
      if ForwardEdge.present r.graph.first == ForwardEdge.present r.targetTag then r.registers.output else [false] := by
  cases first : ForwardEdge.present r.graph.first <;> cases second : ForwardEdge.present r.targetTag <;>
    simp only [filtered, first, second, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem filtered_preserves (r : State) :
    (filtered r).pending = r.pending ∧ (filtered r).targetIndex = r.targetIndex ∧
      (filtered r).targetTag = r.targetTag ∧ (filtered r).graph.core.formula = r.graph.core.formula ∧
        (filtered r).graph.core.matching = r.graph.core.matching ∧ (filtered r).output = r.output := by
  cases first : ForwardEdge.present r.graph.first <;> cases second : ForwardEdge.present r.targetTag <;>
    simp only [filtered, first, second, Bool.false_eq_true, ite_false, ite_true, rejected, ParentQuery.State.withRegisters] <;> trivial

def comparison : Block 21 := .seq countQuery filter
def compared (r : State) : State := filtered (counted r)
def comparisonFuel (r : State) : Nat := countFuel r + filterFuel (counted r)
theorem comparison_exec (r : State) : Exec comparison r.store (comparisonFuel r) (compared r).store :=
  Exec.seq (countQuery_exec r) (filter_exec (counted r))
theorem comparisonFuel_bound (r : State) : comparisonFuel r ≤ 4 * r.currentIndex.length + 12 := by
  have count := countFuel_bound r
  have tag := filterFuel_bound (counted r)
  unfold comparisonFuel
  omega
theorem comparison_output (r : State) :
    (compared r).registers.output =
      [(r.currentIndex.length == r.targetIndex.length) &&
        (ForwardEdge.present r.graph.first == ForwardEdge.present r.targetTag)] := by
  rw [compared, filtered_output, counted_output]
  change (if ForwardEdge.present r.graph.first == ForwardEdge.present r.targetTag
    then [r.currentIndex.length == r.targetIndex.length] else [false]) = _
  cases r.currentIndex.length == r.targetIndex.length <;>
    cases ForwardEdge.present r.graph.first <;> cases ForwardEdge.present r.targetTag <;> rfl

theorem comparison_preserves (r : State) :
    (compared r).pending = r.pending ∧ (compared r).targetIndex = r.targetIndex ∧
      (compared r).targetTag = r.targetTag ∧ (compared r).graph.core.formula = r.graph.core.formula ∧
        (compared r).graph.core.matching = r.graph.core.matching ∧ (compared r).output = r.output :=
  filtered_preserves (counted r)

def same (first second : CNFLiteral) : Bool :=
  (first.variableIndex == second.variableIndex) && (first.positive == second.positive)

end PNP.Concrete.NormalizerBlocks.TraceMember
