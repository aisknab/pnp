/-
Copyright (c) 2026 PNP Labs.

Internally assembled root query for parent selection. The finite controller
copies the saved matching, writes the target's unary header and its actual
tag, and runs the verified root machine. No root Boolean is supplied.
-/

import PNP.Concrete.NormalizerParentState

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister Occurrence

def rootData : Block 21 :=
  .seq (.action (.copy 0 12)) (.seq (.action (.push 0 false)) (.action (.copy 2 17)))
def rootCopied (r : State) : State :=
  r.withRegisters {r.registers with input := false :: r.graph.core.matching, remaining := r.targetIndex}

theorem rootData_exec (r : State) : Exec rootData r.store 3 (rootCopied r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def rootTag : Block 21 :=
  .branch 18 (.action (.push 0 false)) (.action (.push 0 false)) (.action (.push 0 true))
def rootTagged (r : State) : State :=
  r.withRegisters {r.registers with input := ForwardEdge.present r.targetTag :: r.registers.input}

theorem rootTag_exec (r : State) : Exec rootTag r.store 2 (rootTagged r).store := by
  cases tag : r.targetTag with
  | nil =>
      simp only [rootTagged, ForwardEdge.present, tag, List.headD]
      exact Exec.empty (source := (18 : Fin 21)) (before := r.store) tag (.action _ _)
  | cons bit rest =>
      cases bit with
      | false =>
          simp only [rootTagged, ForwardEdge.present, tag, List.headD]
          exact Exec.zero (source := (18 : Fin 21)) (before := r.store) tag (.action _ _)
      | true =>
          simp only [rootTagged, ForwardEdge.present, tag, List.headD]
          exact Exec.one (source := (18 : Fin 21)) (before := r.store) tag (.action _ _)

def rootInput (r : State) : BitString :=
  ForwardEdge.present r.targetTag :: (List.replicate r.targetIndex.length true ++ false :: r.graph.core.matching)
def rootPrepare : Block 21 := .seq reset (.seq rootData (.seq prepend rootTag))
def rootReady (r : State) : State := r.withRegisters (initialRegisters (rootInput r))
def rootPrepareFuel (r : State) : Nat := 14 + 3 * r.targetIndex.length

theorem rootPrepare_exec (r : State) :
    Exec rootPrepare r.store (rootPrepareFuel r) (rootReady r).store := by
  have checked := Exec.seq (reset_exec r) (Exec.seq (rootData_exec (resetResult r))
    (Exec.seq (prependCore_exec (rootCopied (resetResult r)))
      (rootTag_exec (prependResult (rootCopied (resetResult r))))))
  have cost : rootPrepareFuel r =
      8 + (3 + ((3 * r.targetIndex.length + 1) + 2)) := by
    unfold rootPrepareFuel
    omega
  rw [cost]
  exact checked

def rootQuery : Block 21 := .seq rootPrepare (liftCore RootKinds.block)
def rootResult (r : State) : State := r.withRegisters (RootKinds.result (rootInput r))
def rootFuel (r : State) : Nat := rootPrepareFuel r + RootKinds.sourceSteps (rootInput r)

theorem rootQuery_exec (r : State) : Exec rootQuery r.store (rootFuel r) (rootResult r).store := by
  have checked := liftCore_exec RootKinds.block (rootReady r) _ _ (RootKinds.block_exec (rootInput r))
  exact Exec.seq (rootPrepare_exec r) checked

theorem rootInput_length (r : State) :
    (rootInput r).length = r.targetIndex.length + r.graph.core.matching.length + 2 := by
  simp only [rootInput, List.length_cons, List.length_append, List.length_replicate]
  omega

theorem rootFuel_bound (r : State) :
    rootFuel r ≤ 342 * r.targetIndex.length + 339 * r.graph.core.matching.length + 1316 := by
  have bound := RootKinds.sourceSteps_bound (rootInput r)
  change RootKinds.sourceSteps (rootInput r) + 1 ≤ 339 * (rootInput r).length + 625 at bound
  rw [rootInput_length] at bound
  change (14 + 3 * r.targetIndex.length) + RootKinds.sourceSteps (rootInput r) ≤ _
  omega

theorem root_output (r : State) :
    (rootResult r).registers.output = RootKinds.polynomial.output (rootInput r) :=
  (RootKinds.polynomial_output (rootInput r)).symm

theorem root_canonical (r : State) (target : CNFLiteral) (entries : MatchingTable.Entries)
    (indexRead : r.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.targetTag = target.positive)
    (matchingRead : r.graph.core.matching = MatchingTable.encode entries) :
    (rootResult r).registers.output = [RootKinds.value target entries] := by
  rw [root_output]
  have input : rootInput r = RootKinds.encode target entries := by
    simp only [rootInput, indexRead, tagRead, matchingRead, List.length_replicate, RootKinds.encode, TableInit.encodeCount]
  rw [input, RootKinds.polynomial_canonical]

theorem root_preserves (r : State) :
    (rootResult r).pending = r.pending ∧ (rootResult r).targetIndex = r.targetIndex ∧
      (rootResult r).targetTag = r.targetTag ∧
        (rootResult r).graph.core.formula = r.graph.core.formula ∧
          (rootResult r).graph.core.matching = r.graph.core.matching := ⟨rfl, rfl, rfl, rfl, rfl⟩

end PNP.Concrete.NormalizerBlocks.ParentQuery
