/-
Copyright (c) 2026 PNP Labs.

Source-ordered augmentation pairs and their finite-register header reader.
A valid pair is a variable vertex followed by a clause vertex. Decoding
stops at the first other shape; it does not skip malformed prefixes.
-/
import PNP.Concrete.NormalizerSearchPolynomial

namespace PNP.Concrete.NormalizerBlocks.PathPairs
open BitRegister Occurrence

def value : List CNFLiteral → List (Nat × Nat)
  | ⟨false, variableIndex⟩ :: ⟨true, clauseIndex⟩ :: rest =>
      (clauseIndex, variableIndex) :: value rest
  | _ => []

theorem pair_reverse (index value : Nat) (rest : BitString) :
    (TableBatch.encodePair index value []).reverse ++ rest =
      false :: (List.replicate value true ++ (false :: (List.replicate index true ++ rest))) := by
  simp only [TableBatch.encodePair, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.reverse_replicate, List.nil_append, List.cons_append, List.append_assoc]

structure State where
  core : Registers
  pending : BitString
  firstIndex : BitString
  buffer : BitString

def State.frame (r : State) : Store 3 := .cons r.pending (.cons r.firstIndex (.cons r.buffer .nil))
def State.store (r : State) : Store 12 := Frame.join r.core.store r.frame
def State.withCore (r : State) (core : Registers) : State := {r with core := core}

def liftCore (body : Block 9) : Block 12 := Frame.block 3 body
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame

def readHeader : Block 12 := liftCore (.seq CandidatePacket.resetCore TableInit.header)
def headerRead (r : State) : State := r.withCore (TableInit.readCount r.core.input).state
def headerFuel (r : State) : Nat := 8 + TableInit.headerFuel r.core.input
theorem readHeader_exec (r : State) : Exec readHeader r.store (headerFuel r) (headerRead r).store :=
  liftCore_exec _ r _ _ (Exec.seq (CandidatePacket.resetCore_exec r.core) (TableInit.header_exec r.core.input))

def startFirst : Block 12 := .seq (.action (.copy 0 9)) (.action (.pop 0))
def firstStarted (r : State) : State := r.withCore {r.core with input := r.pending.tail}
theorem startFirst_exec (r : State) : Exec startFirst r.store 2 (firstStarted r).store :=
  Exec.seq (.action _ _) (.action _ _)
def saveFirst : Block 12 := .action (.copy 10 1)
def firstSaved (r : State) : State := {r with firstIndex := r.core.target}
theorem saveFirst_exec (r : State) : Exec saveFirst r.store 1 (firstSaved r).store := .action _ _
def readFirst : Block 12 := .seq startFirst (.seq readHeader saveFirst)
def firstRead (r : State) : State := firstSaved (headerRead (firstStarted r))
def firstFuel (r : State) : Nat := 11 + TableInit.headerFuel r.pending.tail
theorem readFirst_exec (r : State) : Exec readFirst r.store (firstFuel r) (firstRead r).store := by
  have checked := Exec.seq (startFirst_exec r) (Exec.seq (readHeader_exec (firstStarted r)) (saveFirst_exec (headerRead (firstStarted r))))
  change Exec readFirst r.store (2 + ((8 + TableInit.headerFuel r.pending.tail) + 1)) (firstRead r).store at checked
  have cost : 2 + ((8 + TableInit.headerFuel r.pending.tail) + 1) = firstFuel r := by unfold firstFuel; omega
  rw [cost] at checked
  exact checked

def startSecond : Block 12 := .action (.pop 0)
def secondStarted (r : State) : State := r.withCore {r.core with input := r.core.input.tail}
theorem startSecond_exec (r : State) : Exec startSecond r.store 1 (secondStarted r).store := .action _ _
def saveSuffix : Block 12 := .action (.copy 9 0)
def suffixSaved (r : State) : State := {r with pending := r.core.input}
theorem saveSuffix_exec (r : State) : Exec saveSuffix r.store 1 (suffixSaved r).store := .action _ _
def readSecond : Block 12 := .seq startSecond (.seq readHeader saveSuffix)
def secondRead (r : State) : State := suffixSaved (headerRead (secondStarted r))
def secondFuel (r : State) : Nat := 10 + TableInit.headerFuel r.core.input.tail
theorem readSecond_exec (r : State) : Exec readSecond r.store (secondFuel r) (secondRead r).store := by
  have checked := Exec.seq (startSecond_exec r) (Exec.seq (readHeader_exec (secondStarted r)) (saveSuffix_exec (headerRead (secondStarted r))))
  change Exec readSecond r.store (1 + ((8 + TableInit.headerFuel r.core.input.tail) + 1)) (secondRead r).store at checked
  have cost : 1 + ((8 + TableInit.headerFuel r.core.input.tail) + 1) = secondFuel r := by unfold secondFuel; omega
  rw [cost] at checked
  exact checked

theorem firstRead_canonical (r : State) (vertex : CNFLiteral) (rest : BitString)
    (read : r.pending = TraceData.vertex vertex rest) :
    (firstRead r).core.input = rest ∧
      (firstRead r).firstIndex = List.replicate vertex.variableIndex true ∧
        (firstRead r).buffer = r.buffer := by
  change (TableInit.readCount r.pending.tail).state.input = _ ∧
    (TableInit.readCount r.pending.tail).state.target = _ ∧ r.buffer = _
  rw [read]
  simp only [TraceData.vertex, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]
  repeat constructor

theorem secondRead_canonical (r : State) (vertex : CNFLiteral) (rest : BitString)
    (read : r.core.input = TraceData.vertex vertex rest) :
    (secondRead r).pending = rest ∧
      (secondRead r).core.target = List.replicate vertex.variableIndex true ∧
        (secondRead r).firstIndex = r.firstIndex ∧ (secondRead r).buffer = r.buffer := by
  change (TableInit.readCount r.core.input.tail).state.input = _ ∧
    (TableInit.readCount r.core.input.tail).state.target = _ ∧ r.firstIndex = _ ∧ r.buffer = _
  rw [read]
  simp only [TraceData.vertex, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]
  repeat constructor

end PNP.Concrete.NormalizerBlocks.PathPairs
