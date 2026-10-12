/-
Copyright (c) 2026 PNP Labs.

Protected state for all selected-clause construction. The actual next clause
index is decoded from the selected-vertex byte list. Formula, selected
variables and the accumulated dense-clause buffer survive parser scratch.
-/
import PNP.Concrete.NormalizerCompactSemantics

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

structure State where
  core : CompactClause.State
  formula : BitString
  remaining : BitString
  index : BitString

def State.frame (r : State) : Store 3 :=
  .cons r.formula (.cons r.remaining (.cons r.index .nil))
def State.store (r : State) : Store 16 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.core
def State.withCompact (r : State) (core : CompactClause.State) : State := {r with core := core}
def State.withRegisters (r : State) (core : Registers) : State :=
  r.withCompact (r.core.withCore core)

def liftCompact (body : Block 13) : Block 16 := Frame.block 3 body
theorem liftCompact_exec (body : Block 13) (r : State) (fuel : Nat) (after : CompactClause.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftCompact body) r.store fuel (r.withCompact after).store :=
  Frame.execution checked r.frame
def liftCore (body : Block 9) : Block 16 := liftCompact (CompactClause.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftCompact_exec _ r _ _ (CompactClause.liftCore_exec body r.core fuel after checked)

def readStart : Block 16 :=
  .seq (.action (.copy 0 14)) <| .seq (.action (.pop 0)) <|
    .seq (.action (.pop 0)) (.action (.copy 9 0))
def readStarted (r : State) : State :=
  {r with core := {r.core with core := {r.registers with input := r.remaining.tail.tail}, pending := r.remaining.tail.tail}}
theorem readStart_exec (r : State) : Exec readStart r.store 4 (readStarted r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def readValue : Block 16 := liftCompact CompactClause.readLiteral
def valueRead (r : State) : State :=
  (readStarted r).withCompact (CompactClause.literalRead (readStarted r).core)
theorem readValue_exec (r : State) :
    Exec readValue (readStarted r).store (CompactClause.readFuel (readStarted r).core)
      (valueRead r).store :=
  liftCompact_exec _ (readStarted r) _ _ (CompactClause.readLiteral_exec (readStarted r).core)

def readSave : Block 16 :=
  .seq (.action (.copy 15 1)) <| .seq (.action (.copy 14 9)) <|
    .seq (.action (.pop 14)) (.action (.pop 14))
def readSaved (r : State) : State :=
  {r with index := r.registers.target, remaining := r.core.pending.tail.tail}
theorem readSave_exec (r : State) : Exec readSave r.store 4 (readSaved r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def readEntry : Block 16 := .seq readStart (.seq readValue readSave)
def entryRead (r : State) : State := readSaved (valueRead r)
def readFuel (r : State) : Nat := 4 + (CompactClause.readFuel (readStarted r).core + 4)
theorem readEntry_exec (r : State) : Exec readEntry r.store (readFuel r) (entryRead r).store :=
  Exec.seq (readStart_exec r) (Exec.seq (readValue_exec r) (readSave_exec (valueRead r)))

theorem read_fields (r : State) :
    (entryRead r).index = UnseenData.index r.remaining ∧
    (entryRead r).remaining = UnseenData.next r.remaining ∧
    (entryRead r).formula = r.formula ∧
    (entryRead r).core.variables = r.core.variables ∧
    (entryRead r).core.buffer = r.core.buffer := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem readFuel_bound (r : State) : readFuel r ≤ 3 * r.remaining.length + 31 := by
  have read := CompactClause.readFuel_bound (readStarted r).core
  change CompactClause.readFuel (readStarted r).core ≤ 3 * r.remaining.tail.tail.length + 23 at read
  have tail := EdgeKinds.tail_length_le r.remaining
  unfold readFuel
  omega

theorem read_progress (r : State) (nonempty : r.remaining ≠ []) :
    (entryRead r).remaining.length < r.remaining.length := by
  rw [(read_fields r).2.1]
  exact UnseenData.next_shorter r.remaining nonempty

theorem read_index_bound (r : State) : (entryRead r).index.length ≤ r.remaining.length := by
  rw [(read_fields r).1]
  exact UnseenData.index_bound r.remaining

theorem read_canonical (r : State) (vertex : CNFLiteral) (rest : List CNFLiteral)
    (remaining : r.remaining = SearchVertices.encodeVertices (vertex :: rest)) :
    (entryRead r).index = List.replicate vertex.variableIndex true ∧
    (entryRead r).remaining = SearchVertices.encodeVertices rest := by
  have bytes : r.remaining = UnseenData.entry vertex ++ SearchVertices.encodeVertices rest :=
    remaining.trans (UnseenData.encoded_cons vertex rest)
  rw [(read_fields r).1, (read_fields r).2.1, bytes]
  have parsed := UnseenData.parsed_canonical vertex (SearchVertices.encodeVertices rest)
  exact ⟨parsed.1,parsed.2.1⟩

end PNP.Concrete.NormalizerBlocks.DenseClauses
