/-
Copyright (c) 2026 PNP Labs.

Root-first parent selection. Roothood is computed from the actual target
and matching table. Only a non-root proceeds to the ordered trace scan.
Unavailable, root and predecessor remain distinct encoded answers.
-/

import PNP.Concrete.NormalizerParentSemantics

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister

def defaultAnswer : Block 21 := .seq (.action (.clear 19)) (.action (.push 19 false))
def defaulted (r : State) : State := {r with output := answer none}
theorem defaultAnswer_exec (r : State) : Exec defaultAnswer r.store 2 (defaulted r).store :=
  Exec.seq (.action _ _) (.action _ _)

def acceptRoot : Block 21 :=
  .seq (.action (.clear 19)) <| .seq (.action (.push 19 false)) <|
    .seq (.action (.push 19 true)) (.action (.clear 16))
def rootAccepted (r : State) : State := {r with pending := [], output := answer (some none)}
theorem acceptRoot_exec (r : State) : Exec acceptRoot r.store 4 (rootAccepted r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def selectRoot : Block 21 := .branch 8 .skip .skip acceptRoot
def rootSelected (r : State) : State := if ForwardEdge.present r.registers.output then rootAccepted r else r
def selectRootFuel (r : State) : Nat := if ForwardEdge.present r.registers.output then 5 else 2
theorem selectRoot_exec (r : State) : Exec selectRoot r.store (selectRootFuel r) (rootSelected r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 21) r.store .skip acceptRoot 1 4 r.store (rootAccepted r).store
    (Exec.skip r.store) (acceptRoot_exec r)
  change Exec selectRoot r.store (1 + if ForwardEdge.present r.registers.output then 4 else 1)
    (if ForwardEdge.present r.registers.output then (rootAccepted r).store else r.store) at checked
  cases found : ForwardEdge.present r.registers.output <;>
    simpa only [rootSelected, selectRootFuel, found, Bool.false_eq_true, ite_false, ite_true] using checked

def firstPhase : Block 21 := .seq defaultAnswer (.seq rootQuery selectRoot)
def firstResult (r : State) : State := rootSelected (rootResult (defaulted r))
def firstFuel (r : State) : Nat := 2 + (rootFuel (defaulted r) + selectRootFuel (rootResult (defaulted r)))
theorem firstPhase_exec (r : State) : Exec firstPhase r.store (firstFuel r) (firstResult r).store :=
  Exec.seq (defaultAnswer_exec r) (Exec.seq (rootQuery_exec (defaulted r)) (selectRoot_exec (rootResult (defaulted r))))

theorem rootSelected_preserves (r : State) :
    (rootSelected r).targetIndex = r.targetIndex ∧ (rootSelected r).targetTag = r.targetTag ∧
      (rootSelected r).graph.core.formula = r.graph.core.formula ∧
        (rootSelected r).graph.core.matching = r.graph.core.matching := by
  cases found : ForwardEdge.present r.registers.output <;>
    simp only [rootSelected, found, Bool.false_eq_true, ite_false, ite_true, rootAccepted] <;> trivial

theorem first_preserves (r : State) :
    (firstResult r).targetIndex = r.targetIndex ∧ (firstResult r).targetTag = r.targetTag ∧
      (firstResult r).graph.core.formula = r.graph.core.formula ∧
        (firstResult r).graph.core.matching = r.graph.core.matching := by
  have stable := rootSelected_preserves (rootResult (defaulted r))
  exact ⟨stable.1, stable.2.1, stable.2.2.1, stable.2.2.2⟩

theorem first_pending (r : State) : (firstResult r).pending = [] ∨ (firstResult r).pending = r.pending := by
  cases found : ForwardEdge.present (rootResult (defaulted r)).registers.output
  · apply Or.inr
    simp only [firstResult, rootSelected, found, Bool.false_eq_true, ite_false]
    rfl
  · apply Or.inl
    simp only [firstResult, rootSelected, found, ite_true, rootAccepted]

theorem first_size (r : State) : (firstResult r).pending.length ≤ r.pending.length := by
  cases first_pending r with
  | inl stopped => rw [stopped]; exact Nat.zero_le _
  | inr same => rw [same]; exact Nat.le_refl _

theorem first_bound (r : State) : stepBound (firstResult r) ≤ stepBound r := by
  have stable := first_preserves r
  have size := first_size r
  simp only [stepBound, stable.1, stable.2.2.1, stable.2.2.2]
  omega

theorem firstFuel_bound (r : State) :
    firstFuel r ≤ 342 * r.targetIndex.length + 339 * r.graph.core.matching.length + 1323 := by
  have root := rootFuel_bound (defaulted r)
  change rootFuel (defaulted r) ≤ 342 * r.targetIndex.length + 339 * r.graph.core.matching.length + 1316 at root
  cases found : ForwardEdge.present (rootResult (defaulted r)).registers.output <;>
    simp only [firstFuel, selectRootFuel, found, Bool.false_eq_true, ite_false, ite_true] <;> omega

def phase : Block 21 := .seq firstPhase loop
def phaseResult (r : State) : State := (whole (firstResult r)).state
def phaseFuel (r : State) : Nat := firstFuel r + (whole (firstResult r)).fuel
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (firstPhase_exec r) (whole_exec (firstResult r))

theorem phaseFuel_bound (r : State) :
    phaseFuel r ≤ 342 * r.targetIndex.length + 339 * r.graph.core.matching.length + 1323 +
      ((stepBound r + 1) * (r.pending.length + 1) + 1) := by
  have first := firstFuel_bound r
  have scanned := whole_fuel_bound (firstResult r)
  have product := Nat.mul_le_mul (Nat.add_le_add_right (first_bound r) 1) (Nat.add_le_add_right (first_size r) 1)
  unfold phaseFuel
  omega

theorem phase_stopped (r : State) : (phaseResult r).pending = [] := whole_stopped (firstResult r)

theorem phase_canonical (r : State) (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : Canonical r target clauses entries) (traceRead : r.pending = TraceData.encode trace) :
    (phaseResult r).output = answer (value target clauses entries trace) := by
  have root := root_canonical (defaulted r) target entries data.indexRead data.tagRead data.matchingRead
  have found : ForwardEdge.present (rootResult (defaulted r)).registers.output = RootKinds.value target entries := by
    rw [root]
    rfl
  cases isRoot : RootKinds.value target entries with
  | false =>
      have first : firstResult r = rootResult (defaulted r) := by
        unfold firstResult rootSelected
        rw [found, isRoot]
        rfl
      have firstData : Canonical (firstResult r) target clauses entries := by
        rw [first]
        exact ⟨data.indexRead, data.tagRead, data.formulaRead, data.matchingRead⟩
      have pending : (firstResult r).pending = TraceData.encode trace := by rw [first]; exact traceRead
      have initial : (firstResult r).output = answer none := by rw [first]; rfl
      change (whole (firstResult r)).state.output = _
      rw [whole_canonical (firstResult r) target clauses entries trace firstData pending initial]
      simp only [value, isRoot, Bool.false_eq_true, ite_false]
  | true =>
      have first : firstResult r = rootAccepted (rootResult (defaulted r)) := by
        unfold firstResult rootSelected
        rw [found, isRoot]
        rfl
      have stopped : (firstResult r).pending = [] := by rw [first]; rfl
      change (scan _ (firstResult r)).state.output = _
      rw [scan_empty _ (firstResult r) stopped, first]
      simp only [rootAccepted, value, isRoot, ite_true]

end PNP.Concrete.NormalizerBlocks.ParentQuery
