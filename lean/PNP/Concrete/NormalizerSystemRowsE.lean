/-
Copyright (c) 2026 PNP Labs.

The complete E-row iteration reads the encoded mode table and excludes the
failed row before emitting an image equation. The filter is executable code,
not a supplied list of eligible rows.
-/
import PNP.Concrete.NormalizerSystemRowsA

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence
attribute [local irreducible] Coefficient.eligibleRow Coefficient.imageTerms

def imagePacket : Coefficient.Routine := Coefficient.packet Coefficient.imageTerms
theorem imagePacket_data (r : Coefficient.State) : (imagePacket.result r).data = r.data :=
  Coefficient.packet_data _ Coefficient.imageTerms_data r
def eBranch : Block 29 := .branch 8 .skip .skip (emit imagePacket)
def eBranchResult (r : State) : State :=
  if r.registers.output.headD false then emitted imagePacket r else r
def eBranchFuel (r : State) : Nat :=
  1 + if r.registers.output.headD false then emitFuel imagePacket r else 1
theorem eBranch_exec (r : State) :
    Exec eBranch r.store (eBranchFuel r) (eBranchResult r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 29) r.store .skip (emit imagePacket)
    1 (emitFuel imagePacket r) r.store (emitted imagePacket r).store
    (Exec.skip r.store) (emit_exec imagePacket r)
  change Exec eBranch r.store
    (1 + if r.registers.output.headD false then emitFuel imagePacket r else 1)
    (if r.registers.output.headD false then (emitted imagePacket r).store else r.store) at checked
  cases h : r.registers.output.headD false <;>
    simpa only [eBranchFuel,eBranchResult,h,Bool.false_eq_true,ite_false,ite_true] using checked
theorem eBranch_shared (r : State) : (eBranchResult r).shared = r.shared := by
  unfold eBranchResult
  split
  · exact emitted_shared imagePacket imagePacket_data r
  · rfl
theorem eBranch_frame (r : State) :
    (eBranchResult r).rows = r.rows ∧ (eBranchResult r).remaining = r.remaining ∧
    (eBranchResult r).counter = r.counter := by
  unfold eBranchResult
  split <;> exact ⟨rfl,rfl,rfl⟩
theorem eBranch_fuel_bound (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    eBranchFuel r ≤ (emitBound imagePacket).eval n + 2 := by
  have work := emit_bound imagePacket r n fixed index
  unfold eBranchFuel
  cases r.registers.output.headD false <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

def eBlock : Block 29 := .seq (run Coefficient.eligibleRow) (.seq eBranch advance)
def eResult (r : State) : State := advanced (eBranchResult (result Coefficient.eligibleRow r))
def eFuel (r : State) : Nat := fuel Coefficient.eligibleRow r +
  (eBranchFuel (result Coefficient.eligibleRow r) + 2)
def eBound : NatPolynomial :=
  .add Coefficient.eligibleRow.bound (.add (emitBound imagePacket) (.constant 23))
theorem e_exec (r : State) : Exec eBlock r.store (eFuel r) (eResult r).store :=
  Exec.seq (run_exec _ r) (Exec.seq (eBranch_exec _) (advance_exec _))
theorem e_shared (r : State) : (eResult r).shared = r.shared :=
  (eBranch_shared _).trans (result_shared _ Coefficient.eligibleRow_data r)
theorem e_frame (r : State) :
    (eResult r).rows = r.rows ∧ (eResult r).remaining = r.remaining.tail ∧
    (eResult r).counter = true::r.counter := by
  have kept := eBranch_frame (result Coefficient.eligibleRow r)
  exact ⟨kept.1,congrArg List.tail kept.2.1,congrArg (List.cons true) kept.2.2⟩
theorem e_fuel_bound (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    eFuel r ≤ eBound.eval n := by
  have test := fuel_bound Coefficient.eligibleRow r n fixed index
  have nextFixed : (result Coefficient.eligibleRow r).shared.Bounded n := by
    rw [result_shared _ Coefficient.eligibleRow_data]
    exact fixed
  have branch := eBranch_fuel_bound (result Coefficient.eligibleRow r) n nextFixed index
  change fuel Coefficient.eligibleRow r +
    (eBranchFuel (result Coefficient.eligibleRow r) + 2) ≤
      Coefficient.eligibleRow.bound.eval n + ((emitBound imagePacket).eval n+23)
  omega
def eIteration : Iteration where
  block := eBlock
  result := eResult
  fuel := eFuel
  bound := eBound
  exec := e_exec
  shared := e_shared
  rows r := (e_frame r).1
  remaining r := (e_frame r).2.1
  counter r := (e_frame r).2.2
  cost := e_fuel_bound
theorem e_whole_exec (r : State) :
    Exec (loop eIteration) r.store (whole eIteration r).fuel (whole eIteration r).state.store :=
  whole_exec eIteration r
theorem e_scan_bound (word : BitString) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (budget : r.counter.length + word.length ≤ n) :
    (scan eIteration word r).fuel ≤ word.length*(1+eBound.eval n)+1 :=
  scan_fuel_bound eIteration word r n fixed budget

end PNP.Concrete.NormalizerBlocks.SystemRows
