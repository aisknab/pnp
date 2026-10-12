/-
Copyright (c) 2026 PNP Labs.

Protected finite state for ordered parent selection. The graph-query
registers are reused directly. The pending trace, fixed target, answer and
current node index remain outside the graph query's mutable register frame.
-/

import PNP.Concrete.NormalizerTraceData

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister Occurrence

structure State where
  graph : EdgeKinds.State
  pending : BitString
  targetIndex : BitString
  targetTag : BitString
  output : BitString
  currentIndex : BitString

def State.frame (r : State) : Store 5 :=
  .cons r.pending (.cons r.targetIndex (.cons r.targetTag (.cons r.output (.cons r.currentIndex .nil))))
def State.store (r : State) : Store 21 := Frame.join r.graph.store r.frame
def State.registers (r : State) : Registers := r.graph.core.core
def State.coreFrame (r : State) : Store 12 :=
  Frame.join r.graph.core.frame (Frame.join r.graph.frame r.frame)
def State.withRegisters (r : State) (registers : Registers) : State :=
  {r with graph := {r.graph with core := {r.graph.core with core := registers}}}

def liftCore (body : Block 9) : Block 21 := Frame.block 12 body

theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  Frame.execution checked r.coreFrame

def reset : Block 21 := liftCore CandidatePacket.resetCore
def resetResult (r : State) : State := r.withRegisters (initialRegisters r.registers.input)
theorem reset_exec (r : State) : Exec reset r.store 8 (resetResult r).store :=
  liftCore_exec _ r _ _ (CandidatePacket.resetCore_exec r.registers)

def readHeader : Block 21 := liftCore (.seq CandidatePacket.resetCore TableInit.header)
def headerResult (r : State) : State := r.withRegisters (TableInit.readCount r.registers.input).state
def headerFuel (r : State) : Nat := 8 + TableInit.headerFuel r.registers.input
theorem readHeader_exec (r : State) : Exec readHeader r.store (headerFuel r) (headerResult r).store :=
  liftCore_exec _ r _ _ (Exec.seq (CandidatePacket.resetCore_exec r.registers) (TableInit.header_exec r.registers.input))

def loadData : Block 21 := liftCore (.seq CandidatePacket.resetCore BatchPacket.coreLoader)
def dataResult (r : State) : State := r.withRegisters (BatchPacket.coreResult r.registers.input)
def dataFuel (r : State) : Nat := 8 + BatchPacket.coreFuel r.registers.input
theorem loadData_exec (r : State) : Exec loadData r.store (dataFuel r) (dataResult r).store :=
  liftCore_exec _ r _ _ (Exec.seq (CandidatePacket.resetCore_exec r.registers) (BatchPacket.core_exec r.registers.input))

def prependStep : Block 9 := .seq (.action (.pop 2)) (.action (.push 0 true))
def prependLoop : Block 9 := .loop 2 prependStep
def prepended (word : BitString) (r : Registers) : Registers :=
  {r with remaining := [], input := List.replicate word.length true ++ r.input}

theorem prepend_exec (word : BitString) (r : Registers) :
    Exec prependLoop ({r with remaining := word}).store (3 * word.length + 1) (prepended word r).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
      have step : Exec prependStep ({r with remaining := bit :: rest}).store 2
          ({r with remaining := rest, input := true :: r.input}).store :=
        Exec.seq (.action _ _) (.action _ _)
      have checked := Exec.loopStep (source := (2 : Fin 9)) (body := prependStep)
        (before := ({r with remaining := bit :: rest}).store) rfl step (ih {r with input := true :: r.input})
      have cost : 3 * (bit :: rest).length + 1 = 1 + (2 + (3 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      rw [cost]
      simpa only [prependLoop, prepended, List.length_cons, List.replicate_succ',
        List.append_assoc, List.cons_append, List.nil_append] using checked

def prepend : Block 21 := liftCore prependLoop
def prependResult (r : State) : State := r.withRegisters (prepended r.registers.remaining r.registers)
def prependFuel (r : State) : Nat := 3 * r.registers.remaining.length + 1
theorem prependCore_exec (r : State) : Exec prepend r.store (prependFuel r) (prependResult r).store :=
  liftCore_exec _ r _ _ (prepend_exec r.registers.remaining r.registers)

end PNP.Concrete.NormalizerBlocks.ParentQuery
