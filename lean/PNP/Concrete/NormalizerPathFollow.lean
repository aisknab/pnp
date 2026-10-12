/-
Copyright (c) 2026 PNP Labs.

Follow a saved predecessor without resetting the trace cursor. Only the
strictly older suffix remains available. A root row ends reconstruction.
-/
import PNP.Concrete.NormalizerPathAppend

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def beginFollow : Block 23 :=
  .seq (.action (.copy 0 22)) (.seq (.action (.pop 0)) (.seq (.action (.copy 18 0)) (.action (.pop 0))))
def followBegun (r : State) : State :=
  {r with core := {r.core.withRegisters {r.registers with input := r.parentBytes.tail.tail} with targetTag := r.parentBytes.tail}}
theorem beginFollow_exec (r : State) : Exec beginFollow r.store 4 (followBegun r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def readFollow : Block 23 := lift ParentQuery.readHeader
def followRead (r : State) : State := r.withCore (ParentQuery.headerResult r.core)
theorem readFollow_exec (r : State) :
    Exec readFollow r.store (ParentQuery.headerFuel r.core) (followRead r).store :=
  lift_exec _ r _ _ (ParentQuery.readHeader_exec r.core)

def saveTarget : Block 23 := .action (.copy 17 1)
def targetSaved (r : State) : State := r.withCore {r.core with targetIndex := r.registers.target}
theorem saveTarget_exec (r : State) : Exec saveTarget r.store 1 (targetSaved r).store := .action _ _

def followParent : Block 23 := .seq beginFollow (.seq readFollow saveTarget)
def parentFollowed (r : State) : State := targetSaved (followRead (followBegun r))
def followFuel (r : State) : Nat := 13 + TableInit.headerFuel r.parentBytes.tail.tail
theorem followParent_exec (r : State) : Exec followParent r.store (followFuel r) (parentFollowed r).store := by
  have checked := Exec.seq (beginFollow_exec r) (Exec.seq (readFollow_exec (followBegun r)) (saveTarget_exec (followRead (followBegun r))))
  change Exec followParent r.store (4 + ((8 + TableInit.headerFuel r.parentBytes.tail.tail) + 1)) (parentFollowed r).store at checked
  have cost : 4 + ((8 + TableInit.headerFuel r.parentBytes.tail.tail) + 1) = followFuel r := by
    unfold followFuel
    omega
  rw [cost] at checked
  exact checked

theorem followFuel_bound (r : State) : followFuel r ≤ 4 * r.parentBytes.length + 19 := by
  have header := TableInit.headerFuel_bound r.parentBytes.tail.tail
  have tail := EdgeKinds.tail_length_le r.parentBytes
  unfold followFuel
  omega

theorem parentFollowed_preserves (r : State) :
    (parentFollowed r).core.pending = r.core.pending ∧
      (parentFollowed r).core.output = r.core.output ∧
        (parentFollowed r).buffer = r.buffer ∧
          (parentFollowed r).parentBytes = r.parentBytes ∧
            (parentFollowed r).core.graph.core.formula = r.core.graph.core.formula ∧
              (parentFollowed r).core.graph.core.matching = r.core.graph.core.matching :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem parentFollowed_canonical (r : State) (parent : CNFLiteral) (suffix : BitString)
    (read : r.parentBytes = TraceData.predecessor (some parent) suffix) :
    (parentFollowed r).core.targetIndex = List.replicate parent.variableIndex true ∧
      ForwardEdge.present (parentFollowed r).core.targetTag = parent.positive := by
  change (TableInit.readCount r.parentBytes.tail.tail).state.target = _ ∧
    ForwardEdge.present r.parentBytes.tail = _
  rw [read]
  simp only [TraceData.predecessor, TraceData.vertex, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]
  constructor <;> trivial

def finishRoot : Block 23 :=
  .seq (.action (.clear 16)) (.seq (.action (.clear 19)) (.action (.push 19 true)))
def rootFinished (r : State) : State := r.withCore {r.core with pending := [], output := [true]}
theorem finishRoot_exec (r : State) : Exec finishRoot r.store 3 (rootFinished r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def choosePredecessor : Block 23 := .branch 22 finishRoot finishRoot followParent
def predecessorChosen (r : State) : State := if ForwardEdge.present r.parentBytes then parentFollowed r else rootFinished r
def predecessorFuel (r : State) : Nat := 1 + if ForwardEdge.present r.parentBytes then followFuel r else 3
theorem choosePredecessor_exec (r : State) :
    Exec choosePredecessor r.store (predecessorFuel r) (predecessorChosen r).store := by
  have checked := EdgeKinds.branch_head (22 : Fin 23) r.store finishRoot followParent 3 (followFuel r)
    (rootFinished r).store (parentFollowed r).store (finishRoot_exec r) (followParent_exec r)
  change Exec choosePredecessor r.store (predecessorFuel r)
    (if ForwardEdge.present r.parentBytes then (parentFollowed r).store else (rootFinished r).store) at checked
  cases tag : ForwardEdge.present r.parentBytes <;>
    simpa only [predecessorChosen, tag, Bool.false_eq_true, ite_false, ite_true] using checked

theorem predecessorFuel_bound (r : State) : predecessorFuel r ≤ 4 * r.parentBytes.length + 20 := by
  have bound := followFuel_bound r
  cases tag : ForwardEdge.present r.parentBytes <;>
    simp only [predecessorFuel, tag, Bool.false_eq_true, ite_false, ite_true] <;> omega

end PNP.Concrete.NormalizerBlocks.TracePath
