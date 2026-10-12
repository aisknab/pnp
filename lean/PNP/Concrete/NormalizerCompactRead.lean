/-
Copyright (c) 2026 PNP Labs.

Literal compaction uses one protected selected-variable list and one output
buffer. This concrete reader consumes the actual encoded literal, preserves
its polarity, and has a strict cursor decrease even on malformed raw input.
No decoded literal or dense index is accepted as a machine instruction.
-/
import PNP.Concrete.NormalizerOwnerVertices
import PNP.Concrete.NormalizerUnseenData

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

structure State where
  core : Registers
  pending : BitString
  variables : BitString
  buffer : BitString
  positive : BitString

def State.frame (r : State) : Store 4 :=
  .cons r.pending (.cons r.variables (.cons r.buffer (.cons r.positive .nil)))
def State.store (r : State) : Store 13 := Frame.join r.core.store r.frame
def State.withCore (r : State) (core : Registers) : State := {r with core := core}
def liftCore (body : Block 9) : Block 13 := Frame.block 4 body
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame

def parsed (input : BitString) : Result :=
  MatchingValue.scan input.tail.tail (initialRegisters input.tail.tail)
def index (input : BitString) : BitString := (parsed input).state.output
def next (input : BitString) : BitString := (parsed input).state.input.tail.tail

theorem index_bound (input : BitString) : (index input).length ≤ input.length := by
  have size := UnseenData.scan_output_bound input.tail.tail (initialRegisters input.tail.tail)
  have tail := EdgeKinds.tail_length_le input
  change (index input).length ≤ 0 + input.tail.tail.length at size
  omega

theorem next_shorter (input : BitString) (nonempty : input ≠ []) :
    (next input).length < input.length := by
  have read := UnseenData.scan_input_bound input.tail.tail (initialRegisters input.tail.tail)
  change (parsed input).state.input.length ≤ input.tail.tail.length at read
  have suffix := EdgeKinds.tail_length_le (parsed input).state.input
  have second := ParentQuery.input_tail_bound input.tail
  have first : input.tail.length < input.length := by
    cases input with
    | nil => exact False.elim (nonempty rfl)
    | cons bit rest => exact Nat.lt_succ_self _
  unfold next
  omega

theorem parsed_canonical (literal : CNFLiteral) (suffix : BitString) :
    index (NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) =
        List.replicate literal.variableIndex true ∧
    next (NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) = suffix ∧
    ForwardEdge.present
      (NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) = literal.positive := by
  simp only [NANDFrontend.literalBits, List.cons_append, List.nil_append, List.append_assoc]
  constructor
  · change (MatchingValue.scan
      (List.replicate (2 * literal.variableIndex) true ++ false :: false :: suffix)
      (initialRegisters _)).state.output = _
    rw [MatchingValue.scan_true_pairs]
    exact List.append_nil _
  · constructor
    · change (MatchingValue.scan
        (List.replicate (2 * literal.variableIndex) true ++ false :: false :: suffix)
        (initialRegisters _)).state.input.tail.tail = _
      rw [UnseenData.scan_true_pairs_input]
      rfl
    · rfl

def readPrefix : Block 13 :=
  .seq (.action (.copy 12 9)) <| .seq (.action (.copy 0 9)) <|
    .seq (.action (.pop 0)) (.action (.pop 0))
def prefixed (r : State) : State :=
  {r with core := {r.core with input := r.pending.tail.tail}, positive := r.pending}
theorem readPrefix_exec (r : State) : Exec readPrefix r.store 4 (prefixed r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def resetRead : Block 13 :=
  liftCore (.seq CandidatePacket.resetCore (.action (.push 6 true)))
def resetReadResult (r : State) : State :=
  r.withCore {initialRegisters r.core.input with active := [true]}
theorem resetRead_exec (r : State) : Exec resetRead r.store 9 (resetReadResult r).store :=
  liftCore_exec _ r _ _
    (Exec.seq (CandidatePacket.resetCore_exec r.core) (.action _ _))

def prepareRead : Block 13 := .seq readPrefix resetRead
def preparedRead (r : State) : State := resetReadResult (prefixed r)
theorem prepareRead_exec (r : State) : Exec prepareRead r.store 13 (preparedRead r).store :=
  Exec.seq (readPrefix_exec r) (resetRead_exec (prefixed r))

def readPairs : Block 13 := liftCore MatchingValue.loop
def pairsRead (r : State) : State := (prefixed r).withCore (parsed r.pending).state
theorem readPairs_exec (r : State) :
    Exec readPairs (preparedRead r).store (parsed r.pending).fuel (pairsRead r).store :=
  liftCore_exec _ (preparedRead r) _ _
    (MatchingValue.scan_exec r.pending.tail.tail (initialRegisters r.pending.tail.tail))

def readSuffix : Block 13 :=
  .seq (.action (.copy 1 8)) <| .seq (.action (.copy 9 0)) <|
    .seq (.action (.pop 9)) (.action (.pop 9))
def suffixed (r : State) : State :=
  {r with core := {r.core with target := r.core.output}, pending := r.core.input.tail.tail}
theorem readSuffix_exec (r : State) : Exec readSuffix r.store 4 (suffixed r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def readLiteral : Block 13 := .seq prepareRead (.seq readPairs readSuffix)
def literalRead (r : State) : State := suffixed (pairsRead r)
def readFuel (r : State) : Nat := 13 + ((parsed r.pending).fuel + 4)
theorem readLiteral_exec (r : State) :
    Exec readLiteral r.store (readFuel r) (literalRead r).store :=
  Exec.seq (prepareRead_exec r) (Exec.seq (readPairs_exec r) (readSuffix_exec (pairsRead r)))

theorem readFuel_bound (r : State) : readFuel r ≤ 3 * r.pending.length + 23 := by
  have bound := MatchingValue.scan_fuel_bound r.pending.tail.tail
    (initialRegisters r.pending.tail.tail)
  have tail := EdgeKinds.tail_length_le r.pending
  unfold readFuel parsed
  omega

theorem read_fields (r : State) :
    (literalRead r).core.target = index r.pending ∧
    (literalRead r).pending = next r.pending ∧
    (literalRead r).positive = r.pending ∧
    (literalRead r).variables = r.variables ∧
    (literalRead r).buffer = r.buffer := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem read_progress (r : State) (nonempty : r.pending ≠ []) :
    (literalRead r).pending.length < r.pending.length :=
  next_shorter r.pending nonempty

theorem read_canonical (r : State) (literal : CNFLiteral) (suffix : BitString)
    (pending : r.pending =
      NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) :
    (literalRead r).core.target = List.replicate literal.variableIndex true ∧
    (literalRead r).pending = suffix ∧
    ForwardEdge.present (literalRead r).positive = literal.positive := by
  change index r.pending = _ ∧ next r.pending = _ ∧ ForwardEdge.present r.pending = _
  rw [pending]
  exact parsed_canonical literal suffix

end PNP.Concrete.NormalizerBlocks.CompactClause
