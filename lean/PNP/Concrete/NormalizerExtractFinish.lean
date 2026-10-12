/-
Copyright (c) 2026 PNP Labs.

Complete concrete output controller for ordered extraction. It emits an
explicit unavailable answer or the selected vertex, computed optional
predecessor and order-preserving remainder. Serialization cost is linear
in the actual retained words.
-/

import PNP.Concrete.NormalizerExtractPack

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister

def copyTargetCounter : Block 27 := .action (.copy 2 17)
def targetCounted (r : State) : State := r.withRegisters {r.registers with remaining := r.parent.targetIndex}
theorem copyTargetCounter_exec (r : State) : Exec copyTargetCounter r.store 1 (targetCounted r).store := .action _ _

def copyTargetSign : Block 27 := .action (.copy 4 18)
def targetSigned (r : State) : State := r.withRegisters {r.registers with sign := r.parent.targetTag}
theorem copyTargetSign_exec (r : State) : Exec copyTargetSign r.store 1 (targetSigned r).store := .action _ _

def saveResult : Block 27 := .action (.copy 26 0)
def resultSaved (r : State) : State := {r with output := r.registers.input}
theorem saveResult_exec (r : State) : Exec saveResult r.store 1 (resultSaved r).store := .action _ _

def packVertex : Block 27 :=
  .seq pushFalse (.seq copyTargetCounter (.seq prepend (.seq copyTargetSign (.seq pushSign (.seq pushTrue saveResult)))))
def vertexPacked (r : State) : State :=
  resultSaved (truePushed (signPushed (targetSigned (prepended (targetCounted (falsePushed r))))))
def packVertexFuel (r : State) : Nat := 3 * r.parent.targetIndex.length + 8
theorem packVertex_exec (r : State) : Exec packVertex r.store (packVertexFuel r) (vertexPacked r).store := by
  have checked := Exec.seq (pushFalse_exec r) <| Exec.seq (copyTargetCounter_exec (falsePushed r)) <|
    Exec.seq (prepend_exec (targetCounted (falsePushed r))) <|
      Exec.seq (copyTargetSign_exec (prepended (targetCounted (falsePushed r)))) <|
        Exec.seq (pushSign_exec (targetSigned (prepended (targetCounted (falsePushed r))))) <|
          Exec.seq (pushTrue_exec (signPushed (targetSigned (prepended (targetCounted (falsePushed r))))))
            (saveResult_exec (truePushed (signPushed (targetSigned (prepended (targetCounted (falsePushed r)))))))
  change Exec packVertex r.store
    (1 + (1 + ((3 * r.parent.targetIndex.length + 1) + (1 + (2 + (1 + 1)))))) (vertexPacked r).store at checked
  have cost : 1 + (1 + ((3 * r.parent.targetIndex.length + 1) + (1 + (2 + (1 + 1))))) = packVertexFuel r := by
    unfold packVertexFuel
    omega
  rw [cost] at checked
  exact checked

theorem vertexPacked_output (r : State) :
    (vertexPacked r).output = true :: TraceData.vertex
      ⟨ForwardEdge.present r.parent.targetTag, r.parent.targetIndex.length⟩ r.registers.input := rfl

def finishSome : Block 27 := .seq packRemaining (.seq packParent packVertex)
def someFinished (r : State) : State := vertexPacked (parentPacked (remainingPacked r))
def finishSomeFuel (r : State) : Nat :=
  (4 * r.skipped.length + 4) + (packParentFuel (remainingPacked r) + packVertexFuel (parentPacked (remainingPacked r)))
theorem finishSome_exec (r : State) : Exec finishSome r.store (finishSomeFuel r) (someFinished r).store :=
  Exec.seq (packRemaining_exec r) (Exec.seq (packParent_exec (remainingPacked r)) (packVertex_exec (parentPacked (remainingPacked r))))

theorem someFinished_output (r : State) :
    (someFinished r).output = true :: TraceData.vertex
      ⟨ForwardEdge.present r.parent.targetTag, r.parent.targetIndex.length⟩
        (parentBytes r.parent.output (r.skipped.reverse ++ r.pending)) := by
  have stable := parentPacked_fields (remainingPacked r)
  change (vertexPacked (parentPacked (remainingPacked r))).output = _
  rw [vertexPacked_output, stable.1, stable.2.1, parentPacked_input, remainingPacked_input]
  rfl

theorem finishSomeFuel_bound (r : State) :
    finishSomeFuel r ≤ 4 * r.skipped.length + 3 * r.parent.output.length + 3 * r.parent.targetIndex.length + 24 := by
  have parent := packParentFuel_bound (remainingPacked r)
  change packParentFuel (remainingPacked r) ≤ 3 * r.parent.output.length + 12 at parent
  have index := (parentPacked_fields (remainingPacked r)).1
  unfold finishSomeFuel packVertexFuel
  rw [index]
  change (4 * r.skipped.length + 4) +
    (packParentFuel (remainingPacked r) + (3 * r.parent.targetIndex.length + 8)) ≤ _
  omega

def finishNone : Block 27 := .seq (.action (.clear 26)) (.action (.push 26 false))
def noneFinished (r : State) : State := {r with output := [false]}
theorem finishNone_exec (r : State) : Exec finishNone r.store 2 (noneFinished r).store :=
  Exec.seq (.action _ _) (.action _ _)

def finish : Block 27 := .branch 19 finishNone finishNone finishSome
def finished (r : State) : State := if ForwardEdge.present r.parent.output then someFinished r else noneFinished r
def finishFuel (r : State) : Nat := 1 + if ForwardEdge.present r.parent.output then finishSomeFuel r else 2
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have checked := EdgeKinds.branch_head (19 : Fin 27) r.store finishNone finishSome 2 (finishSomeFuel r)
    (noneFinished r).store (someFinished r).store (finishNone_exec r) (finishSome_exec r)
  change Exec finish r.store (finishFuel r)
    (if ForwardEdge.present r.parent.output then (someFinished r).store else (noneFinished r).store) at checked
  cases found : ForwardEdge.present r.parent.output <;>
    simpa only [finished, found, Bool.false_eq_true, ite_false, ite_true] using checked

theorem finished_output (r : State) : (finished r).output = observation r := by
  cases found : ForwardEdge.present r.parent.output <;>
    simp only [finished, observation, found, Bool.false_eq_true, ite_false, ite_true]
  · rfl
  · exact someFinished_output r

theorem finishFuel_bound (r : State) :
    finishFuel r ≤ 4 * r.skipped.length + 3 * r.parent.output.length + 3 * r.parent.targetIndex.length + 25 := by
  have bound := finishSomeFuel_bound r
  cases found : ForwardEdge.present r.parent.output <;>
    simp only [finishFuel, found, Bool.false_eq_true, ite_false, ite_true] <;> omega

def phase : Block 27 := .seq loop finish
def phaseResult (r : State) : State := finished (whole r).state
def phaseFuel (r : State) : Nat := (whole r).fuel + finishFuel (whole r).state
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (whole_exec r) (finish_exec (whole r).state)

theorem phase_canonical (r : State) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (unseen : List CNFLiteral)
    (data : Canonical r clauses entries trace unseen []) :
    (phaseResult r).output = answer (value clauses entries trace unseen) := by
  change (finished (whole r).state).output = _
  rw [finished_output]
  exact whole_canonical r clauses entries trace unseen data

end PNP.Concrete.NormalizerBlocks.Extraction
