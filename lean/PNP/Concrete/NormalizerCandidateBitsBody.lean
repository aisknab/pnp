/-
Copyright (c) 2026 PNP Labs.

One finite candidate-assignment iteration. The ordinal is copied into the
verified cache reader, its computed sign is appended to a reversed buffer,
and exactly one runtime counter cell is consumed.
-/
import PNP.Concrete.NormalizerCacheSigmaCall

namespace PNP.Concrete.NormalizerBlocks.CandidateBits
open BitRegister Occurrence
structure State where
  core : CacheSigma.State
  remaining : BitString
  counter : BitString
  buffer : BitString
def State.frame (r : State) : Store 3 :=
  .cons r.remaining (.cons r.counter (.cons r.buffer .nil))
def State.store (r : State) : Store 22 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : CacheSigma.State) : State := {r with core := core}
def liftCore (body : Block 19) : Block 22 := Frame.block 3 body
theorem liftCore_exec (body : Block 19) (r : State) (fuel : Nat) (after : CacheSigma.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withCore after).store := Frame.execution checked r.frame

def load : Block 22 := .action (.copy 15 20)
def loaded (r : State) : State := r.withCore (r.core.withDense {r.core.core with index := r.counter})
theorem load_exec (r : State) : Exec load r.store 1 (loaded r).store := .action _ _
def query : Block 22 := .seq load (liftCore CacheSigma.read)
def queried (r : State) : State := (loaded r).withCore (CacheSigma.result (loaded r).core)
def queryFuel (r : State) : Nat := 1 + CacheSigma.fuel (loaded r).core
theorem query_exec (r : State) : Exec query r.store (queryFuel r) (queried r).store :=
  Exec.seq (load_exec r) (liftCore_exec _ (loaded r) _ _ (CacheSigma.read_exec _))

def append : Block 22 :=
  .branch 8 (.action (.push 21 false)) (.action (.push 21 false)) (.action (.push 21 true))
def appended (r : State) : State :=
  {r with buffer := ForwardEdge.present r.registers.output :: r.buffer}
theorem append_exec (r : State) : Exec append r.store 2 (appended r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 22) r.store
    (.action (.push 21 false)) (.action (.push 21 true)) 1 1
    ({r with buffer := false::r.buffer}).store ({r with buffer := true::r.buffer}).store
    (.action _ _) (.action _ _)
  change Exec append r.store (1 + if ForwardEdge.present r.registers.output then 1 else 1)
    (if ForwardEdge.present r.registers.output then
      ({r with buffer := true::r.buffer}).store else
      ({r with buffer := false::r.buffer}).store) at checked
  cases h : ForwardEdge.present r.registers.output <;>
    simpa only [appended,h,Bool.false_eq_true,ite_false,ite_true] using checked
def advance : Block 22 := .seq (.action (.pop 19)) (.action (.push 20 true))
def advanced (r : State) : State :=
  {r with remaining := r.remaining.tail, counter := true::r.counter}
theorem advance_exec (r : State) : Exec advance r.store 2 (advanced r).store :=
  Exec.seq (.action _ _) (.action _ _)
def body : Block 22 := .seq query (.seq append advance)
def bodyResult (r : State) : State := advanced (appended (queried r))
def bodyFuel (r : State) : Nat := queryFuel r + 4
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (query_exec r) (Exec.seq (append_exec (queried r)) (advance_exec (appended (queried r))))
theorem body_fields (r : State) :
    (bodyResult r).core.core.formula = r.core.core.formula ∧
    (bodyResult r).core.matching = r.core.matching ∧
    (bodyResult r).core.counter = r.core.counter ∧
    (bodyResult r).remaining = r.remaining.tail ∧
    (bodyResult r).counter = true::r.counter := by
  have fields := CacheSigma.result_fields (loaded r).core
  exact ⟨fields.1,fields.2.2.2.1,fields.2.2.2.2,rfl,rfl⟩
theorem body_buffer (r : State) :
    (bodyResult r).buffer =
      ForwardEdge.present (CacheSigma.result (loaded r).core).registers.output :: r.buffer := rfl
def bodyBound : NatPolynomial := .add CacheSigma.bound (.constant 5)
theorem bodyFuel_bound (r : State) (n : Nat)
    (formula : r.core.core.formula.length ≤ n) (owners : r.core.matching.length ≤ n)
    (slots : r.core.counter.length ≤ n) (counter : r.counter.length ≤ n) :
    bodyFuel r ≤ bodyBound.eval n := by
  have cost := CacheSigma.fuel_bound (loaded r).core n ⟨formula,owners,slots,counter⟩
  change bodyFuel r ≤ CacheSigma.bound.eval n + 5
  unfold bodyFuel queryFuel
  omega

end PNP.Concrete.NormalizerBlocks.CandidateBits
