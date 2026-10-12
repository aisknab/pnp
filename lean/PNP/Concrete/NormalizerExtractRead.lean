/-
Copyright (c) 2026 PNP Labs.

Finite state and a concrete reader for the existing ordered vertex list.
The selected index is counted from the actual input; the next cursor is
strictly shorter on every nonempty raw input. Formula, matching and the
original predecessor trace are protected from parser scratch registers.
-/

import PNP.Concrete.NormalizerUnseenData

namespace PNP.Concrete.NormalizerBlocks.Extraction

open BitRegister Occurrence

structure State where
  core : Eligibility.State
  pending : BitString
  skipped : BitString
  trace : BitString
  active : BitString
  output : BitString

def State.frame (r : State) : Store 5 :=
  .cons r.pending (.cons r.skipped (.cons r.trace (.cons r.active (.cons r.output .nil))))
def State.store (r : State) : Store 27 := Frame.join r.core.store r.frame
def State.parent (r : State) : ParentQuery.State := r.core.core
def State.registers (r : State) : Registers := r.parent.registers
def State.withParent (r : State) (parent : ParentQuery.State) : State :=
  {r with core := {r.core with core := parent}}
def State.withRegisters (r : State) (registers : Registers) : State :=
  r.withParent (r.parent.withRegisters registers)
def State.coreFrame (r : State) : Store 18 :=
  Frame.join r.parent.coreFrame (Frame.join r.core.frame r.frame)

def liftCore (body : Block 9) : Block 27 := Frame.block 18 body
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  Frame.execution checked r.coreFrame

def copyCursor : Block 27 := .action (.copy 0 22)
def cursorCopied (r : State) : State := r.withRegisters {r.registers with input := r.pending}
theorem copyCursor_exec (r : State) : Exec copyCursor r.store 1 (cursorCopied r).store := .action _ _

def popInput2 : Block 27 := .seq (.action (.pop 0)) (.action (.pop 0))
def inputPopped2 (r : State) : State := r.withRegisters {r.registers with input := r.registers.input.tail.tail}
theorem popInput2_exec (r : State) : Exec popInput2 r.store 2 (inputPopped2 r).store :=
  Exec.seq (.action _ _) (.action _ _)

def saveTag : Block 27 := .action (.copy 18 0)
def tagSaved (r : State) : State := r.withParent {r.parent with targetTag := r.registers.input}
theorem saveTag_exec (r : State) : Exec saveTag r.store 1 (tagSaved r).store := .action _ _

def readPrefix : Block 27 := .seq copyCursor (.seq popInput2 (.seq saveTag popInput2))
def prefixed (r : State) : State := inputPopped2 (tagSaved (inputPopped2 (cursorCopied r)))
theorem readPrefix_exec (r : State) : Exec readPrefix r.store 6 (prefixed r).store :=
  Exec.seq (copyCursor_exec r) (Exec.seq (popInput2_exec (cursorCopied r))
    (Exec.seq (saveTag_exec (inputPopped2 (cursorCopied r))) (popInput2_exec (tagSaved (inputPopped2 (cursorCopied r))))))

def reset : Block 27 := liftCore CandidatePacket.resetCore
def resetResult (r : State) : State := r.withRegisters (initialRegisters r.registers.input)
theorem reset_exec (r : State) : Exec reset r.store 8 (resetResult r).store :=
  liftCore_exec _ r _ _ (CandidatePacket.resetCore_exec r.registers)

def startRead : Block 27 := .action (.push 6 true)
def startedRead (r : State) : State := r.withRegisters {r.registers with active := true :: r.registers.active}
theorem startRead_exec (r : State) : Exec startRead r.store 1 (startedRead r).store := .action _ _

def prepareRead : Block 27 := .seq readPrefix (.seq reset startRead)
def preparedRead (r : State) : State := startedRead (resetResult (prefixed r))
theorem prepareRead_exec (r : State) : Exec prepareRead r.store 15 (preparedRead r).store :=
  Exec.seq (readPrefix_exec r) (Exec.seq (reset_exec (prefixed r)) (startRead_exec (resetResult (prefixed r))))

def readPairs : Block 27 := liftCore MatchingValue.loop
def pairsRead (r : State) : State := (prefixed r).withRegisters (UnseenData.parsed r.pending).state
theorem readPairs_exec (r : State) :
    Exec readPairs (preparedRead r).store (UnseenData.parsed r.pending).fuel (pairsRead r).store :=
  liftCore_exec _ (preparedRead r) _ _
    (MatchingValue.scan_exec (UnseenData.tail4 r.pending) (initialRegisters (UnseenData.tail4 r.pending)))

def saveIndex : Block 27 := .action (.copy 17 8)
def indexSaved (r : State) : State := r.withParent {r.parent with targetIndex := r.registers.output}
theorem saveIndex_exec (r : State) : Exec saveIndex r.store 1 (indexSaved r).store := .action _ _

def savePending : Block 27 := .action (.copy 22 0)
def pendingSaved (r : State) : State := {r with pending := r.registers.input}
theorem savePending_exec (r : State) : Exec savePending r.store 1 (pendingSaved r).store := .action _ _

def readSuffix : Block 27 := .seq saveIndex (.seq popInput2 (.seq popInput2 savePending))
def suffixed (r : State) : State := pendingSaved (inputPopped2 (inputPopped2 (indexSaved r)))
theorem readSuffix_exec (r : State) : Exec readSuffix r.store 6 (suffixed r).store :=
  Exec.seq (saveIndex_exec r) (Exec.seq (popInput2_exec (indexSaved r))
    (Exec.seq (popInput2_exec (inputPopped2 (indexSaved r))) (savePending_exec (inputPopped2 (inputPopped2 (indexSaved r))))))

def readVertex : Block 27 := .seq prepareRead (.seq readPairs readSuffix)
def vertexRead (r : State) : State := suffixed (pairsRead r)
def readFuel (r : State) : Nat := 15 + ((UnseenData.parsed r.pending).fuel + 6)
theorem readVertex_exec (r : State) : Exec readVertex r.store (readFuel r) (vertexRead r).store :=
  Exec.seq (prepareRead_exec r) (Exec.seq (readPairs_exec r) (readSuffix_exec (pairsRead r)))

theorem readFuel_bound (r : State) : readFuel r ≤ 3 * r.pending.length + 27 := by
  have scan := MatchingValue.scan_fuel_bound (UnseenData.tail4 r.pending) (initialRegisters (UnseenData.tail4 r.pending))
  have tail := UnseenData.tail4_le r.pending
  unfold readFuel UnseenData.parsed
  omega

theorem read_fields (r : State) :
    (vertexRead r).parent.targetIndex = UnseenData.index r.pending ∧
      (vertexRead r).parent.targetTag = r.pending.tail.tail ∧
        (vertexRead r).pending = UnseenData.next r.pending ∧
          (vertexRead r).parent.graph.core.formula = r.parent.graph.core.formula ∧
            (vertexRead r).parent.graph.core.matching = r.parent.graph.core.matching ∧
              (vertexRead r).trace = r.trace ∧ (vertexRead r).skipped = r.skipped ∧
                (vertexRead r).active = r.active ∧ (vertexRead r).parent.output = r.parent.output :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem read_index_bound (r : State) : (vertexRead r).parent.targetIndex.length ≤ r.pending.length :=
  UnseenData.index_bound r.pending
theorem read_progress (r : State) (nonempty : r.pending ≠ []) :
    (vertexRead r).pending.length < r.pending.length :=
  UnseenData.next_shorter r.pending nonempty

theorem read_canonical (r : State) (vertex : CNFLiteral) (rest : List CNFLiteral)
    (pending : r.pending = SearchVertices.encodeVertices (vertex :: rest)) :
    (vertexRead r).parent.targetIndex = List.replicate vertex.variableIndex true ∧
      ForwardEdge.present (vertexRead r).parent.targetTag = vertex.positive ∧
        (vertexRead r).pending = SearchVertices.encodeVertices rest := by
  have data := UnseenData.parsed_canonical vertex (SearchVertices.encodeVertices rest)
  have bytes : r.pending = UnseenData.entry vertex ++ SearchVertices.encodeVertices rest :=
    pending.trans (UnseenData.encoded_cons vertex rest)
  change UnseenData.index r.pending = _ ∧ UnseenData.tag r.pending = _ ∧ UnseenData.next r.pending = _
  rw [bytes]
  exact ⟨data.1, data.2.2, data.2.1⟩

end PNP.Concrete.NormalizerBlocks.Extraction
