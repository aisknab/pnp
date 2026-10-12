/-
Copyright (c) 2026 PNP Labs.

Finite framed operations for the combined forward-edge query. The saved
words are target, clause index, formula bytes, matching bytes and the actual
first query answer. They are data, not externally supplied truth values.
-/

import PNP.Concrete.NormalizerGraphQuery

namespace PNP.Concrete.NormalizerBlocks.ForwardEdge

open BitRegister Occurrence

structure State where
  core : Registers
  target : BitString
  index : BitString
  formula : BitString
  matching : BitString
  mark : BitString

def State.frame (r : State) : Store 5 :=
  .cons r.target (.cons r.index (.cons r.formula (.cons r.matching (.cons r.mark .nil))))
def State.store (r : State) : Store 14 := Frame.join r.core.store r.frame

def readHeader : Block 14 := Frame.block 5 (.seq CandidatePacket.resetCore TableInit.header)
def headerResult (r : State) : State := {r with core := (TableInit.readCount r.core.input).state}
def headerFuel (r : State) : Nat := 8 + TableInit.headerFuel r.core.input

theorem readHeader_exec (r : State) :
    Exec readHeader r.store (headerFuel r) (headerResult r).store :=
  Frame.execution (Exec.seq (CandidatePacket.resetCore_exec r.core) (TableInit.header_exec r.core.input)) r.frame

def saveTarget : Block 14 := .action (.copy 9 1)
def targeted (r : State) : State := {r with target := r.core.target}
theorem saveTarget_exec (r : State) : Exec saveTarget r.store 1 (targeted r).store := .action _ _

def saveIndex : Block 14 := .action (.copy 10 1)
def indexed (r : State) : State := {r with index := r.core.target}
theorem saveIndex_exec (r : State) : Exec saveIndex r.store 1 (indexed r).store := .action _ _

def loadData : Block 14 := Frame.block 5 (.seq CandidatePacket.resetCore BatchPacket.coreLoader)
def dataResult (r : State) : State := {r with core := BatchPacket.coreResult r.core.input}
def dataFuel (r : State) : Nat := 8 + BatchPacket.coreFuel r.core.input
theorem loadData_exec (r : State) : Exec loadData r.store (dataFuel r) (dataResult r).store :=
  Frame.execution (Exec.seq (CandidatePacket.resetCore_exec r.core) (BatchPacket.core_exec r.core.input)) r.frame

def saveData : Block 14 := .seq (.action (.copy 11 8)) (.action (.copy 12 0))
def saved (r : State) : State := {r with formula := r.core.output, matching := r.core.input}
theorem saveData_exec (r : State) : Exec saveData r.store 2 (saved r).store :=
  Exec.seq (.action _ _) (.action _ _)

def data (first : Bool) (r : State) : BitString := if first then r.formula else r.matching
def setupLeft (first : Bool) : Block 14 :=
  .seq (.action (.copy 0 (if first then 11 else 12))) <|
    .seq (.action (.copy 1 10)) (.action (.copy 2 10))
def leftReady (first : Bool) (r : State) : State :=
  {r with core := {r.core with input := data first r, target := r.index, remaining := r.index}}
theorem setupLeft_exec (first : Bool) (r : State) :
    Exec (setupLeft first) r.store 3 (leftReady first r).store := by
  cases first <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def setupRight : Block 14 :=
  .seq (.action (.copy 3 9)) <| .seq (.action (.push 3 false)) <|
    .seq (.action (.push 6 true)) (.action (.copy 7 9))
def rightReady (r : State) : State :=
  {r with core := {r.core with excess := false :: r.target, active := true :: r.core.active, reserved := r.target}}
theorem setupRight_exec (r : State) : Exec setupRight r.store 4 (rightReady r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def reset : Block 14 := Frame.block 5 CandidatePacket.resetCore
def resetResult (r : State) : State := {r with core := initialRegisters r.core.input}
theorem reset_exec (r : State) : Exec reset r.store 8 (resetResult r).store :=
  Frame.execution (CandidatePacket.resetCore_exec r.core) r.frame

def prepare (first : Bool) : Block 14 := .seq reset (.seq (setupLeft first) setupRight)
def ready (first : Bool) (r : State) : State :=
  {r with core := GraphQuery.prepared r.target r.index (data first r)}
theorem prepare_exec (first : Bool) (r : State) :
    Exec (prepare first) r.store 15 (ready first r).store :=
  Exec.seq (reset_exec r) (Exec.seq (setupLeft_exec first (resetResult r))
    (setupRight_exec (leftReady first (resetResult r))))

def query : Block 14 := Frame.block 5 GraphQuery.block
def queried (r : State) : State := {r with core := GraphQuery.result r.core}
theorem query_exec (r : State) : Exec query r.store (GraphQuery.fuel r.core) (queried r).store :=
  Frame.execution (GraphQuery.block_exec r.core) r.frame

def saveAnswer : Block 14 := .action (.copy 13 8)
def marked (r : State) : State := {r with mark := r.core.output}
theorem saveAnswer_exec (r : State) : Exec saveAnswer r.store 1 (marked r).store := .action _ _

def present (bits : BitString) : Bool := bits.headD false
def emit (bit : Bool) : Block 14 := .seq (.action (.clear 8)) (.action (.push 8 bit))
def emitted (bit : Bool) (r : State) : State := {r with core := {r.core with output := [bit]}}
theorem emit_exec (bit : Bool) (r : State) : Exec (emit bit) r.store 2 (emitted bit r).store :=
  Exec.seq (.action _ _) (.action _ _)

def finish : Block 14 :=
  .branch 13 (emit false) (emit false) (.branch 8 (emit true) (emit true) (emit false))
def finished (r : State) : State := emitted (present r.mark && !present r.core.output) r
def finishFuel (r : State) : Nat := if present r.mark then 4 else 3

theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  cases mark : r.mark with
  | nil =>
      simpa only [finish, finishFuel, finished, present, mark, List.headD, Bool.false_and, Bool.false_eq_true, ite_false] using
        (Exec.empty (source := (13 : Fin 14)) (before := r.store) mark (emit_exec false r))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [finish, finishFuel, finished, present, mark, List.headD, Bool.false_and, Bool.false_eq_true, ite_false] using
            (Exec.zero (source := (13 : Fin 14)) (before := r.store) mark (emit_exec false r))
      | true =>
          cases answer : r.core.output with
          | nil =>
              simpa only [finish, finishFuel, finished, present, mark, answer, List.headD, Bool.true_and, Bool.not_true, Bool.not_false, ite_true] using
                (Exec.one (source := (13 : Fin 14)) (before := r.store) mark
                  (Exec.empty (source := (8 : Fin 14)) answer (emit_exec true r)))
          | cons found tail =>
              cases found with
              | false =>
                  simpa only [finish, finishFuel, finished, present, mark, answer, List.headD, Bool.true_and, Bool.not_true, Bool.not_false, ite_true] using
                    (Exec.one (source := (13 : Fin 14)) (before := r.store) mark
                      (Exec.zero (source := (8 : Fin 14)) answer (emit_exec true r)))
              | true =>
                  simpa only [finish, finishFuel, finished, present, mark, answer, List.headD, Bool.true_and, Bool.not_true, Bool.not_false, ite_true] using
                    (Exec.one (source := (13 : Fin 14)) (before := r.store) mark
                      (Exec.one (source := (8 : Fin 14)) answer (emit_exec false r)))

theorem finishFuel_bound (r : State) : finishFuel r ≤ 4 := by
  unfold finishFuel
  cases present r.mark <;> decide

theorem present_answer (found : Option CNFLiteral) : present (Occurrence.answer found) = found.isSome := by
  cases found <;> rfl

end PNP.Concrete.NormalizerBlocks.ForwardEdge
