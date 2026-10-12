/-
Copyright (c) 2026 PNP Labs.

Read one full predecessor row while retaining its optional-parent bytes.
The old row parser still determines the exact following suffix. Two
protected registers retain the path buffer and saved predecessor.
-/

import PNP.Concrete.NormalizerPathData

namespace PNP.Concrete.NormalizerBlocks.ParentQuery
open BitRegister

def pathNodePrefix : Block 21 := .seq beginNode (.seq readHeader saveNode)
def pathNodePrefixed (r : State) : State := nodeSaved (headerResult (nodeStarted r))
def pathNodePrefixFuel (r : State) : Nat := 3 + (headerFuel (nodeStarted r) + 2)
theorem pathNodePrefix_exec (r : State) :
    Exec pathNodePrefix r.store (pathNodePrefixFuel r) (pathNodePrefixed r).store :=
  Exec.seq (beginNode_exec r) (Exec.seq (readHeader_exec (nodeStarted r))
    (saveNode_exec (headerResult (nodeStarted r))))

def pathNodeSuffix : Block 21 := .seq skipParent finishNode
def pathNodeSuffixed (r : State) : State := nodeFinished (parentSkipped r)
def pathNodeSuffixFuel (r : State) : Nat := skipFuel r + 4
theorem pathNodeSuffix_exec (r : State) :
    Exec pathNodeSuffix r.store (pathNodeSuffixFuel r) (pathNodeSuffixed r).store :=
  Exec.seq (skipParent_exec r) (finishNode_exec (parentSkipped r))

end PNP.Concrete.NormalizerBlocks.ParentQuery

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister Occurrence

structure State where
  core : ParentQuery.State
  buffer : BitString
  parentBytes : BitString
def State.frame (r : State) : Store 2 := .cons r.buffer (.cons r.parentBytes .nil)
def State.store (r : State) : Store 23 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : ParentQuery.State) : State := {r with core := core}
def State.withRegisters (r : State) (registers : Registers) : State := r.withCore (r.core.withRegisters registers)

def lift (body : Block 21) : Block 23 := Frame.block 2 body
theorem lift_exec (body : Block 21) (r : State) (fuel : Nat) (after : ParentQuery.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame
def liftCore (body : Block 9) : Block 23 := lift (ParentQuery.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  lift_exec _ r _ _ (ParentQuery.liftCore_exec body r.core fuel after checked)

def readPrefix : Block 23 := lift ParentQuery.pathNodePrefix
def prefixRead (r : State) : State := r.withCore (ParentQuery.pathNodePrefixed r.core)
theorem readPrefix_exec (r : State) :
    Exec readPrefix r.store (ParentQuery.pathNodePrefixFuel r.core) (prefixRead r).store :=
  lift_exec _ r _ _ (ParentQuery.pathNodePrefix_exec r.core)

def saveParent : Block 23 :=
  .action (.copy (Frame.frameIndex 21 (1 : Fin 2)) (Frame.index 2 (0 : Fin 21)))
def parentSaved (r : State) : State := {r with parentBytes := r.registers.input}
theorem saveParent_exec (r : State) : Exec saveParent r.store 1 (parentSaved r).store := by
  have input : r.core.store.get (0 : Fin 21) = r.registers.input := rfl
  have checked := Exec.action (.copy (Frame.frameIndex 21 (1 : Fin 2)) (Frame.index 2 (0 : Fin 21))) r.store
  simpa only [saveParent, Action.update, Action.instruction, Instruction.update, State.store,
    Frame.get_core, Frame.set_frame, input, State.frame, parentSaved, Store.set, Store.indexCases] using checked

def readSuffix : Block 23 := lift ParentQuery.pathNodeSuffix
def suffixRead (r : State) : State := r.withCore (ParentQuery.pathNodeSuffixed r.core)
theorem readSuffix_exec (r : State) :
    Exec readSuffix r.store (ParentQuery.pathNodeSuffixFuel r.core) (suffixRead r).store :=
  lift_exec _ r _ _ (ParentQuery.pathNodeSuffix_exec r.core)

def readNode : Block 23 := .seq readPrefix (.seq saveParent readSuffix)
def nodeRead (r : State) : State := suffixRead (parentSaved (prefixRead r))
def nodeFuel (r : State) : Nat :=
  ParentQuery.pathNodePrefixFuel r.core + (1 + ParentQuery.pathNodeSuffixFuel (prefixRead r).core)
theorem readNode_exec (r : State) : Exec readNode r.store (nodeFuel r) (nodeRead r).store :=
  Exec.seq (readPrefix_exec r) (Exec.seq (saveParent_exec (prefixRead r)) (readSuffix_exec (parentSaved (prefixRead r))))

theorem nodeRead_fields (r : State) :
    (nodeRead r).core = ParentQuery.nodeResult r.core ∧ (nodeRead r).buffer = r.buffer ∧
      (nodeRead r).parentBytes = (TableInit.readCount r.core.pending.tail).state.input := ⟨rfl, rfl, rfl⟩

theorem nodeFuel_bound (r : State) : nodeFuel r ≤ 8 * r.core.pending.length + 41 := by
  have bound := ParentQuery.nodeFuel_bound r.core
  have same : nodeFuel r = ParentQuery.nodeFuel r.core + 1 := by
    change (3 + (ParentQuery.headerFuel (ParentQuery.nodeStarted r.core) + 2)) +
      (1 + (ParentQuery.skipFuel (ParentQuery.pathNodePrefixed r.core) + 4)) =
      (3 + (ParentQuery.headerFuel (ParentQuery.nodeStarted r.core) +
        (2 + (ParentQuery.skipFuel (ParentQuery.pathNodePrefixed r.core) + 4)))) + 1
    omega
  omega

theorem parentBytes_bound (r : State) : (nodeRead r).parentBytes.length ≤ r.core.pending.length := by
  rw [(nodeRead_fields r).2.2]
  have read := Occurrence.header_input_bound r.core.pending.tail (TableInit.seeded r.core.pending.tail)
  have tail := ParentQuery.input_tail_bound r.core.pending
  exact Nat.le_trans read tail

theorem nodeRead_canonical (r : State) (entry : TraceData.Row) (suffix : BitString)
    (read : r.core.pending = TraceData.row entry suffix) :
    (nodeRead r).core.pending = suffix ∧
      (nodeRead r).parentBytes = TraceData.predecessor entry.2 suffix ∧
        (nodeRead r).core.currentIndex = List.replicate entry.1.variableIndex true ∧
          ForwardEdge.present (nodeRead r).core.graph.first = entry.1.positive := by
  have fields := nodeRead_fields r
  rw [fields.1, fields.2.2, (ParentQuery.node_fields r.core).1,
    (ParentQuery.node_fields r.core).2.1, (ParentQuery.node_fields r.core).2.2.2.2.1,
    read, TraceData.next_canonical, TraceData.nodeIndex_canonical]
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp only [TraceData.row, TraceData.vertex, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]

end PNP.Concrete.NormalizerBlocks.TracePath
