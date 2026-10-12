/-
Copyright (c) 2026 PNP Labs.

One ordered-clause search step. The query checks actual candidate bytes.
A failed clause records its runtime ordinal and clears the cursor; a true
clause advances by one. No failed-row certificate is supplied.
-/
import PNP.Concrete.NormalizerCandidateClause
import PNP.Concrete.NormalizerCandidateBitsBody

namespace PNP.Concrete.NormalizerBlocks.FirstFailure
open BitRegister Occurrence
abbrev State := CandidateBits.State
attribute [local irreducible] CandidateTruth.clauseResult

def load : Block 22 := .action (.copy 15 20)
def loaded (r : State) : State := r.withCore (r.core.withDense {r.core.core with index := r.counter})
theorem load_exec (r : State) : Exec load r.store 1 (loaded r).store := .action _ _
def query : Block 22 := .seq load (CandidateBits.liftCore CandidateTruth.clause)
def queried (r : State) : State := (loaded r).withCore (CandidateTruth.clauseResult (loaded r).core)
def queryFuel (r : State) : Nat := 1 + CandidateTruth.clauseFuel (loaded r).core
theorem query_exec (r : State) : Exec query r.store (queryFuel r) (queried r).store :=
  Exec.seq (load_exec r)
    (CandidateBits.liftCore_exec _ (loaded r) _ _ (CandidateTruth.clause_exec _))
def truth (r : State) : Bool := ForwardEdge.present (queried r).registers.output

def stop : Block 22 :=
  .seq (.action (.copy 21 20)) (.seq (.action (.push 21 true)) (.action (.clear 19)))
def stopped (r : State) : State := {r with remaining := [], buffer := true::r.counter}
theorem stop_exec (r : State) : Exec stop r.store 3 (stopped r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def decideNext : Block 22 := .branch 8 stop stop CandidateBits.advance
def decided (r : State) : State :=
  if ForwardEdge.present r.registers.output then CandidateBits.advanced r else stopped r
def decisionFuel (r : State) : Nat := 1 + if ForwardEdge.present r.registers.output then 2 else 3
theorem decideNext_exec (r : State) : Exec decideNext r.store (decisionFuel r) (decided r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 22) r.store stop CandidateBits.advance 3 2
    (stopped r).store (CandidateBits.advanced r).store (stop_exec r) (CandidateBits.advance_exec r)
  change Exec decideNext r.store (decisionFuel r)
    (if ForwardEdge.present r.registers.output then (CandidateBits.advanced r).store
      else (stopped r).store) at checked
  cases h : ForwardEdge.present r.registers.output <;>
    simpa only [decided,h,Bool.false_eq_true,ite_false,ite_true] using checked
def body : Block 22 := .seq query decideNext
def bodyResult (r : State) : State := decided (queried r)
def bodyFuel (r : State) : Nat := queryFuel r + decisionFuel (queried r)
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (query_exec r) (decideNext_exec (queried r))
theorem body_continuing (r : State) (ok : truth r = true) :
    bodyResult r = CandidateBits.advanced (queried r) := by
  change (if truth r then _ else _) = _
  rw [ok]
  rfl
theorem body_stopped (r : State) (bad : truth r = false) :
    bodyResult r = stopped (queried r) := by
  change (if truth r then _ else _) = _
  rw [bad]
  rfl
theorem queried_fields (r : State) :
    (queried r).core.core.formula = r.core.core.formula ∧
    (queried r).core.matching = r.core.matching ∧
    (queried r).remaining = r.remaining ∧ (queried r).counter = r.counter ∧
    (queried r).buffer = r.buffer :=
  ⟨(CandidateTruth.clause_fields (loaded r).core).1,
    (CandidateTruth.clause_fields (loaded r).core).2.2,rfl,rfl,rfl⟩
theorem body_fields (r : State) :
    (bodyResult r).core.core.formula = r.core.core.formula ∧
    (bodyResult r).core.matching = r.core.matching := by
  cases h : truth r
  · rw [body_stopped r h]
    exact ⟨(queried_fields r).1,(queried_fields r).2.1⟩
  · rw [body_continuing r h]
    exact ⟨(queried_fields r).1,(queried_fields r).2.1⟩
theorem body_remaining (r : State) :
    (bodyResult r).remaining = if truth r then r.remaining.tail else [] := by
  cases h : truth r
  · rw [body_stopped r h]; rfl
  · rw [body_continuing r h]; rfl
theorem body_counter (r : State) :
    (bodyResult r).counter = if truth r then true::r.counter else r.counter := by
  cases h : truth r
  · rw [body_stopped r h]; rfl
  · rw [body_continuing r h]; rfl
theorem body_buffer (r : State) :
    (bodyResult r).buffer = if truth r then r.buffer else true::r.counter := by
  cases h : truth r
  · rw [body_stopped r h]; rfl
  · rw [body_continuing r h]; rfl

def bodyBound : NatPolynomial := .add CandidateTruth.clauseBound (.constant 5)
theorem bodyFuel_bound (r : State) (n : Nat)
    (formula : r.core.core.formula.length ≤ n) (counter : r.counter.length ≤ n) :
    bodyFuel r ≤ bodyBound.eval n := by
  have cost := CandidateTruth.clauseFuel_bound (loaded r).core n formula counter
  change bodyFuel r ≤ CandidateTruth.clauseBound.eval n + 5
  unfold bodyFuel queryFuel decisionFuel
  cases ForwardEdge.present (queried r).registers.output <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

end PNP.Concrete.NormalizerBlocks.FirstFailure
