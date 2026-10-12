/-
Copyright (c) 2026 PNP Labs.

Append the matched row's vertex to the reversed path accumulator. The unary
loop uses the parsed row index, never an unbounded caller-supplied target.
-/
import PNP.Concrete.NormalizerPathCompare

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def loadBuffer : Block 23 := .action (.copy 0 21)
def bufferLoaded (r : State) : State := r.withRegisters {r.registers with input := r.buffer}
theorem loadBuffer_exec (r : State) : Exec loadBuffer r.store 1 (bufferLoaded r).store := .action _ _

def pushTag (bit : Bool) : Block 23 := .action (.push 0 bit)
def tagPushed (bit : Bool) (r : State) : State := r.withRegisters {r.registers with input := bit :: r.registers.input}
theorem pushTag_exec (bit : Bool) (r : State) : Exec (pushTag bit) r.store 1 (tagPushed bit r).store := .action _ _

def appendTag : Block 23 := .branch 14 (pushTag false) (pushTag false) (pushTag true)
def tagAppended (r : State) : State := tagPushed (ForwardEdge.present r.core.graph.first) r
theorem appendTag_exec (r : State) : Exec appendTag r.store 2 (tagAppended r).store := by
  have checked := EdgeKinds.branch_head (14 : Fin 23) r.store (pushTag false) (pushTag true) 1 1
    (tagPushed false r).store (tagPushed true r).store (pushTag_exec false r) (pushTag_exec true r)
  change Exec appendTag r.store (1 + if ForwardEdge.present r.core.graph.first then 1 else 1)
    (if ForwardEdge.present r.core.graph.first then (tagPushed true r).store else (tagPushed false r).store) at checked
  cases tag : ForwardEdge.present r.core.graph.first <;>
    simpa only [tagAppended, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def loadNodeCounter : Block 23 := .action (.copy 2 20)
def nodeCounterLoaded (r : State) : State := r.withRegisters {r.registers with remaining := r.core.currentIndex}
theorem loadNodeCounter_exec (r : State) : Exec loadNodeCounter r.store 1 (nodeCounterLoaded r).store := .action _ _

def appendIndex : Block 23 := liftCore ParentQuery.prependLoop
def indexAppended (r : State) : State := r.withRegisters (ParentQuery.prepended r.registers.remaining r.registers)
theorem appendIndex_exec (r : State) :
    Exec appendIndex r.store (3 * r.registers.remaining.length + 1) (indexAppended r).store :=
  liftCore_exec _ r _ _ (ParentQuery.prepend_exec r.registers.remaining r.registers)

def saveBuffer : Block 23 := .action (.copy (Frame.frameIndex 21 (0 : Fin 2)) (Frame.index 2 (0 : Fin 21)))
def bufferSaved (r : State) : State := {r with buffer := r.registers.input}
theorem saveBuffer_exec (r : State) : Exec saveBuffer r.store 1 (bufferSaved r).store := by
  have input : r.core.store.get (0 : Fin 21) = r.registers.input := rfl
  have checked := Exec.action (.copy (Frame.frameIndex 21 (0 : Fin 2)) (Frame.index 2 (0 : Fin 21))) r.store
  simpa only [saveBuffer, Action.update, Action.instruction, Instruction.update, State.store,
    Frame.get_core, Frame.set_frame, input, State.frame, bufferSaved, Store.set, Store.indexCases] using checked

def appendNode : Block 23 :=
  .seq loadBuffer (.seq appendTag (.seq loadNodeCounter (.seq appendIndex (.seq (pushTag false) saveBuffer))))
def nodeAppended (r : State) : State :=
  bufferSaved (tagPushed false (indexAppended (nodeCounterLoaded (tagAppended (bufferLoaded r)))))
def appendFuel (r : State) : Nat := 3 * r.core.currentIndex.length + 7
theorem appendNode_exec (r : State) : Exec appendNode r.store (appendFuel r) (nodeAppended r).store := by
  have checked := Exec.seq (loadBuffer_exec r) <| Exec.seq (appendTag_exec (bufferLoaded r)) <|
    Exec.seq (loadNodeCounter_exec (tagAppended (bufferLoaded r))) <|
      Exec.seq (appendIndex_exec (nodeCounterLoaded (tagAppended (bufferLoaded r)))) <|
        Exec.seq (pushTag_exec false (indexAppended (nodeCounterLoaded (tagAppended (bufferLoaded r)))))
          (saveBuffer_exec (tagPushed false (indexAppended (nodeCounterLoaded (tagAppended (bufferLoaded r))))))
  change Exec appendNode r.store (1 + (2 + (1 + ((3 * r.core.currentIndex.length + 1) + (1 + 1)))))
    (nodeAppended r).store at checked
  have cost : 1 + (2 + (1 + ((3 * r.core.currentIndex.length + 1) + (1 + 1)))) = appendFuel r := by
    unfold appendFuel
    omega
  rw [cost] at checked
  exact checked

theorem nodeAppended_buffer (r : State) :
    (nodeAppended r).buffer =
      (TraceData.vertex ⟨ForwardEdge.present r.core.graph.first, r.core.currentIndex.length⟩ []).reverse ++ r.buffer := by
  rw [PathData.vertex_reverse]
  rfl

theorem nodeAppended_preserves (r : State) :
    (nodeAppended r).core.pending = r.core.pending ∧
      (nodeAppended r).core.targetIndex = r.core.targetIndex ∧
        (nodeAppended r).core.targetTag = r.core.targetTag ∧
          (nodeAppended r).core.output = r.core.output ∧
            (nodeAppended r).parentBytes = r.parentBytes ∧
              (nodeAppended r).core.graph.core.formula = r.core.graph.core.formula ∧
                (nodeAppended r).core.graph.core.matching = r.core.graph.core.matching :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nodeAppended_canonical (r : State) (vertex : CNFLiteral)
    (indexRead : r.core.currentIndex = List.replicate vertex.variableIndex true)
    (tagRead : ForwardEdge.present r.core.graph.first = vertex.positive) :
    (nodeAppended r).buffer = (TraceData.vertex vertex []).reverse ++ r.buffer := by
  rw [nodeAppended_buffer, indexRead, List.length_replicate, tagRead]

end PNP.Concrete.NormalizerBlocks.TracePath
