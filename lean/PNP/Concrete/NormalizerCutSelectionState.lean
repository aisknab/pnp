/-
Copyright (c) 2026 PNP Labs.

Protected finite state for complete source-order cut selection. The original
trace, remaining index range and output buffer are outside the membership
query's scratch registers. A query supplies no membership certificate.
-/
import PNP.Concrete.NormalizerCutTracePolynomial

namespace PNP.Concrete.NormalizerBlocks.CutSelection
open BitRegister Occurrence

structure State where
  core : TraceMember.State
  trace : BitString
  remaining : BitString
  buffer : BitString

def State.frame (r : State) : Store 3 :=
  .cons r.trace (.cons r.remaining (.cons r.buffer .nil))
def State.store (r : State) : Store 24 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : TraceMember.State) : State := {r with core := core}
def State.withRegisters (r : State) (registers : Registers) : State :=
  r.withCore (r.core.withRegisters registers)

def liftMember (body : Block 21) : Block 24 := Frame.block 3 body
def liftCore (body : Block 9) : Block 24 := liftMember (ParentQuery.liftCore body)

theorem liftMember_exec (body : Block 21) (r : State) (fuel : Nat) (after : TraceMember.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftMember body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftMember_exec _ r _ _ (ParentQuery.liftCore_exec _ r.core _ _ checked)

def loadTrace : Block 24 := .action (.copy 16 21)
def traceLoaded (r : State) : State := {r with core := {r.core with pending := r.trace}}
theorem loadTrace_exec (r : State) : Exec loadTrace r.store 1 (traceLoaded r).store := .action _ _

def query : Block 24 := .seq loadTrace (liftMember TraceMember.phase)
def queried (r : State) : State :=
  (traceLoaded r).withCore (TraceMember.phaseResult (traceLoaded r).core)
def queryFuel (r : State) : Nat := 1 + TraceMember.phaseFuel (traceLoaded r).core
theorem query_exec (r : State) : Exec query r.store (queryFuel r) (queried r).store :=
  Exec.seq (loadTrace_exec r) (liftMember_exec _ (traceLoaded r) _ _ (TraceMember.phase_exec _))
theorem queried_frame (r : State) :
    (queried r).trace = r.trace ∧ (queried r).remaining = r.remaining ∧
      (queried r).buffer = r.buffer ∧
      (queried r).core.targetIndex = r.core.targetIndex ∧
      (queried r).core.targetTag = r.core.targetTag := by
  have kept := TraceMember.phase_preserves (traceLoaded r).core
  exact ⟨rfl, rfl, rfl, kept.1, kept.2.1⟩
theorem queryFuel_bound (r : State) :
    queryFuel r ≤ (28 * r.trace.length + 81) * (r.trace.length + 1) + 4 := by
  have bound := TraceMember.phaseFuel_bound (traceLoaded r).core
  unfold queryFuel
  change TraceMember.phaseFuel (traceLoaded r).core ≤
    (28 * r.trace.length + 81) * (r.trace.length + 1) + 3 at bound
  omega

def prepareEmission : Block 24 := .seq (.action (.copy 1 17)) (.action (.copy 3 23))
def emissionReady (r : State) : State :=
  r.withRegisters {r.registers with target := r.core.targetIndex, excess := r.buffer}
theorem prepareEmission_exec (r : State) :
    Exec prepareEmission r.store 2 (emissionReady r).store :=
  Exec.seq (.action _ _) (.action _ _)

def saveBuffer : Block 24 := .action (.copy 23 3)
def bufferSaved (r : State) : State := {r with buffer := r.registers.excess}
theorem saveBuffer_exec (r : State) : Exec saveBuffer r.store 1 (bufferSaved r).store := .action _ _

def emit (tag : Bool) : Block 24 :=
  .seq prepareEmission (.seq (liftCore (SearchVertices.emitEntry tag)) saveBuffer)
def emitted (tag : Bool) (r : State) : State :=
  bufferSaved ((emissionReady r).withRegisters (SearchVertices.emitted tag (emissionReady r).registers))
def emitFuel (r : State) : Nat := 4 * r.core.targetIndex.length + 13
theorem emit_exec (tag : Bool) (r : State) :
    Exec (emit tag) r.store (emitFuel r) (emitted tag r).store := by
  have checked := Exec.seq (prepareEmission_exec r) <|
    Exec.seq (liftCore_exec _ (emissionReady r) _ _ (SearchVertices.emitEntry_exec tag _))
      (saveBuffer_exec _)
  have cost : emitFuel r = 2 + ((4 * r.core.targetIndex.length + 10) + 1) := by
    unfold emitFuel; omega
  rw [cost]
  exact checked
theorem emitted_buffer (tag : Bool) (r : State) :
    (emitted tag r).buffer =
      (SearchVertices.entryBits tag r.core.targetIndex.length).reverse ++ r.buffer := rfl
theorem emitted_frame (tag : Bool) (r : State) :
    (emitted tag r).trace = r.trace ∧ (emitted tag r).remaining = r.remaining ∧
      (emitted tag r).core.targetIndex = r.core.targetIndex ∧
        (emitted tag r).core.targetTag = r.core.targetTag := ⟨rfl,rfl,rfl,rfl⟩

def choose (tag : Bool) : Block 24 := .branch 19 .skip .skip (emit tag)
def chosen (tag : Bool) (r : State) : State :=
  if ForwardEdge.present r.core.output then emitted tag r else r
def chooseFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.core.output then emitFuel r else 1
theorem choose_exec (tag : Bool) (r : State) :
    Exec (choose tag) r.store (chooseFuel r) (chosen tag r).store := by
  have checked := EdgeKinds.branch_head (19 : Fin 24) r.store .skip (emit tag)
    1 (emitFuel r) r.store (emitted tag r).store (Exec.skip r.store) (emit_exec tag r)
  change Exec (choose tag) r.store
    (1 + if ForwardEdge.present r.core.output then emitFuel r else 1)
    (if ForwardEdge.present r.core.output then (emitted tag r).store else r.store) at checked
  cases found : ForwardEdge.present r.core.output <;>
    simpa only [choose, chooseFuel, chosen, found, Bool.false_eq_true, ite_false, ite_true] using checked

end PNP.Concrete.NormalizerBlocks.CutSelection
