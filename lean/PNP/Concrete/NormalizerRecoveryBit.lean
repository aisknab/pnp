/-
Copyright (c) 2026 PNP Labs.

Compute a recovered bit from the selected-variable position, or from the
original matching when the variable was discarded. Position zero and an
absent position are different branches; all protected fields survive.
-/
import PNP.Concrete.NormalizerRecoveryPreferred

namespace PNP.Concrete.NormalizerBlocks.Recovery
open BitRegister Occurrence

theorem frame_fields {r s : State} (same : r.frame = s.frame) :
    r.data = s.data ∧ r.remaining = s.remaining ∧ r.counter = s.counter ∧ r.buffer = s.buffer :=
  ⟨congrArg (fun f : Store 7 => Data.mk (f.get 0) (f.get 1) (f.get 2) (f.get 3)) same,
   congrArg (fun f : Store 7 => f.get 4) same,
   congrArg (fun f : Store 7 => f.get 5) same,
   congrArg (fun f : Store 7 => f.get 6) same⟩
def loadDense : Block 16 :=
  .seq (.action (.copy 1 8)) (.seq (.action (.pop 1)) (.action (.copy 0 12)))
def denseLoaded (r : State) : State :=
  r.withCore {r.core with target := r.core.output.tail,input := r.assignment}
theorem loadDense_exec (r : State) : Exec loadDense r.store 3 (denseLoaded r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def dense : Block 16 := .seq loadDense (lift BitLookup.read)
def denseResult (r : State) : State := r.withCore (BitLookup.result (denseLoaded r).core)
def denseFuel (r : State) : Nat := 3+BitLookup.fuel (denseLoaded r).core
theorem dense_exec (r : State) : Exec dense r.store (denseFuel r) (denseResult r).store :=
  Exec.seq (loadDense_exec r) (lift_exec _ (denseLoaded r) _ _ (BitLookup.read_exec _))
theorem denseFuel_bound (r : State) : denseFuel r ≤ 3*r.core.output.length+7 := by
  have tail := ParentQuery.input_tail_bound r.core.output
  change 3+(3*r.core.output.tail.length+4) ≤ _
  omega
theorem dense_canonical (r : State) (index : Nat)
    (found : r.core.output = TableOwner.answer (some index)) :
    (denseResult r).core.output = [r.assignment[index]?.getD false] := by
  change (BitLookup.result (denseLoaded r).core).output = _
  rw [BitLookup.result_output]
  change [r.assignment[r.core.output.tail.length]?.getD false] = _
  rw [found]
  simp only [TableOwner.answer,List.tail_cons,List.length_replicate]

def chooseBit : Block 16 := .branch 8 preferred preferred dense
def bitChosen (r : State) : State :=
  if r.core.output.headD false then denseResult r else preferredResult r
def chooseBitFuel (r : State) : Nat :=
  1+if r.core.output.headD false then denseFuel r else preferredFuel r
theorem chooseBit_exec (r : State) :
    Exec chooseBit r.store (chooseBitFuel r) (bitChosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 16) r.store preferred dense
    (preferredFuel r) (denseFuel r) (preferredResult r).store (denseResult r).store
    (preferred_exec r) (dense_exec r)
  change Exec chooseBit r.store (chooseBitFuel r)
    (if r.core.output.headD false then (denseResult r).store else (preferredResult r).store) at checked
  cases h : r.core.output.headD false <;>
    simpa only [bitChosen,h,Bool.false_eq_true,ite_false,ite_true] using checked
def bit : Block 16 := .seq (owner .selected) chooseBit
def bitResult (r : State) : State := bitChosen (owned .selected r)
def bitFuel (r : State) : Nat := ownerFuel .selected r+chooseBitFuel (owned .selected r)
theorem bit_exec (r : State) : Exec bit r.store (bitFuel r) (bitResult r).store :=
  Exec.seq (owner_exec .selected r) (chooseBit_exec (owned .selected r))
theorem bit_frame (r : State) : (bitResult r).frame = r.frame := by
  unfold bitResult bitChosen
  split
  · rfl
  · exact preferred_frame (owned .selected r)
theorem bit_fields (r : State) :
    (bitResult r).data = r.data ∧ (bitResult r).remaining = r.remaining ∧
    (bitResult r).counter = r.counter ∧ (bitResult r).buffer = r.buffer :=
  frame_fields (bit_frame r)
def bitBound : NatPolynomial := .linear 600 700
theorem bitFuel_bound (r : State) (n : Nat)
    (formula : r.formula.length ≤ n) (matching : r.matching.length ≤ n)
    (variables : r.variables.length ≤ n) (counter : r.counter.length ≤ n) :
    bitFuel r ≤ bitBound.eval n := by
  have first := ownerFuel_bound .selected r
  have output := owned_output_bound .selected r
  have inside := denseFuel_bound (owned .selected r)
  have outside := preferredFuel_bound (owned .selected r) n formula matching counter
  change ownerFuel .selected r ≤ 12*r.variables.length+24 at first
  change (owned .selected r).core.output.length ≤ r.counter.length+13*r.variables.length+14 at output
  change bitFuel r ≤ 600*n+700
  unfold bitFuel chooseBitFuel
  split <;> omega
def bitValue (formula : List (List CNFLiteral)) (matching : MatchingTable.Entries)
    (variables : List CNFLiteral) (assignment : BitString) (target : Nat) : Bool :=
  match TableOwner.vertexOwner variables target with
  | none => preferredValue formula matching target
  | some index => assignment[index]?.getD false
theorem bit_canonical (r : State) (formula : List (List CNFLiteral))
    (matching : MatchingTable.Entries) (variables : List CNFLiteral) (target : Nat)
    (formulaRead : r.formula = GraphQuery.clauseData formula)
    (matchingRead : r.matching = MatchingTable.encode matching)
    (variablesRead : r.variables = SearchVertices.encodeVertices variables)
    (index : r.counter = List.replicate target true) :
    (bitResult r).core.output = [bitValue formula matching variables r.assignment target] := by
  have found := owned_selected r target variables index variablesRead
  cases h : TableOwner.vertexOwner variables target with
  | none =>
      rw [h] at found
      simp only [bitResult,bitChosen,found,TableOwner.answer,List.headD_cons,
        Bool.false_eq_true,ite_false,bitValue,h]
      exact preferred_canonical (owned .selected r) formula matching target formulaRead matchingRead index
  | some position =>
      rw [h] at found
      simp only [bitResult,bitChosen,found,TableOwner.answer,List.headD_cons,ite_true,bitValue,h]
      exact dense_canonical (owned .selected r) position found

end PNP.Concrete.NormalizerBlocks.Recovery
