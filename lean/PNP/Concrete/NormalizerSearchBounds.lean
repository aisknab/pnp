/-
Copyright (c) 2026 PNP Labs.

Encoded-size bounds for every search phase. Bounds include all registers
and raw malformed inputs, not merely canonical search instances.
-/
import PNP.Concrete.NormalizerSearchExecution

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister

def seenBudget : NatPolynomial :=
  .add (.linear 4 38) (.mul (.constant 5) (.mul (.linear 28 108) (.linear 1 2)))
def selectBudget : NatPolynomial :=
  .add (.linear 4 29) (.mul (.linear 120 724) (.linear 5 29))
def pathBudget : NatPolynomial :=
  .add (.linear 4 50) (.mul (.constant 5) (.mul (.linear 47 360) (.linear 1 6)))
def decideBudget : NatPolynomial := .add (.linear 3 11) pathBudget

theorem seenBudget_eval (size : Nat) :
    seenBudget.eval size = 4 * size + 38 + 5 * ((28 * size + 108) * (size + 2)) := by
  change 4 * size + 38 + 5 * ((28 * size + 108) * (1 * size + 2)) = _
  rw [Nat.one_mul]
theorem selectBudget_eval (size : Nat) :
    selectBudget.eval size = 4 * size + 29 + (120 * size + 724) * (5 * size + 29) := rfl
theorem pathBudget_eval (size : Nat) :
    pathBudget.eval size = 4 * size + 50 + 5 * ((47 * size + 360) * (size + 6)) := by
  change 4 * size + 50 + 5 * ((47 * size + 360) * (1 * size + 6)) = _
  rw [Nat.one_mul]
theorem decideBudget_eval (size : Nat) :
    decideBudget.eval size = 3 * size + 11 + pathBudget.eval size := rfl

theorem deriveSeenFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    deriveSeenFuel r ≤ seenBudget.eval bound := by
  have copied := (copyTrace_exec r).bounded bound checked
  have viewed := path_bounded (traceCopied r) (bound + 1) copied
  have pending : (traceCopied r).path.core.pending.length ≤ bound + 1 :=
    (traceCopied r).path.store.get_length_le 16 viewed
  have phaseBound := SeenTrace.phaseFuel_bound (traceCopied r).path (bound + 1) viewed
  have first : 28 * (traceCopied r).path.core.pending.length + 80 ≤ 28 * bound + 108 := by omega
  have second : (traceCopied r).path.core.pending.length + 1 ≤ bound + 2 := by omega
  have product := Nat.mul_le_mul first second
  rw [seenBudget_eval]
  change 1 + SeenTrace.phaseFuel (traceCopied r).path ≤ _
  omega

theorem selectFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    selectFuel r ≤ selectBudget.eval bound := by
  have original : r.original.length ≤ bound := r.store.get_length_le 28 checked
  have prepare := prepareCandidateFuel_bound r
  have full := (prepareCandidate_exec r).bounded bound checked
  have enlarged : (candidatePrepared r).store.Bounded (5 * bound + 28) :=
    Store.bounded_mono full (by omega)
  have viewed := candidate_bounded (candidatePrepared r) (5 * bound + 28) enlarged
  have matching : (candidatePrepared r).candidate.matching.length ≤ 5 * bound + 28 :=
    (candidatePrepared r).candidate.store.get_length_le 9 viewed
  have seen : (candidatePrepared r).candidate.seen.length ≤ 5 * bound + 28 :=
    (candidatePrepared r).candidate.store.get_length_le 10 viewed
  have remaining : (candidatePrepared r).candidate.remaining.length ≤ 5 * bound + 28 :=
    (candidatePrepared r).candidate.store.get_length_le 11 viewed
  have loopBound := Candidate.whole_fuel_bound (candidatePrepared r).candidate
  have first : 12 * (candidatePrepared r).candidate.matching.length +
      12 * (candidatePrepared r).candidate.seen.length + 52 ≤ 120 * bound + 724 := by omega
  have second : (candidatePrepared r).candidate.remaining.length + 1 ≤ 5 * bound + 29 := by omega
  have product := Nat.mul_le_mul first second
  rw [selectBudget_eval]
  change prepareCandidateFuel r + (Candidate.whole (candidatePrepared r).candidate).fuel ≤ _
  omega

theorem reconstructFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    reconstructFuel r ≤ pathBudget.eval bound := by
  have prepared := (preparePath_exec r).bounded bound checked
  have viewed := path_bounded (pathPrepared r) (bound + 5) prepared
  have pending : (pathPrepared r).path.core.pending.length ≤ bound + 5 :=
    (pathPrepared r).path.store.get_length_le 16 viewed
  have phaseBound := TracePath.phaseFuel_bound (pathPrepared r).path (bound + 5) viewed
  have first : 47 * (pathPrepared r).path.core.pending.length + 125 ≤ 47 * bound + 360 := by omega
  have second : (pathPrepared r).path.core.pending.length + 1 ≤ bound + 6 := by omega
  have product := Nat.mul_le_mul first second
  rw [pathBudget_eval]
  change 5 + TracePath.phaseFuel (pathPrepared r).path ≤ _
  omega

theorem decideFuel_bound (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    decideFuel r ≤ decideBudget.eval bound := by
  have path := reconstructFuel_bound r bound checked
  have matching : r.parent.graph.core.matching.length ≤ bound := r.store.get_length_le 12 checked
  have suffix := ParentQuery.input_tail_bound r.parent.graph.core.matching
  have pack : packAugmentFuel (reconstructed r) ≤ 3 * bound + 8 := by
    unfold packAugmentFuel
    rw [(reconstructed_frame r).2.2]
    omega
  rw [decideBudget_eval]
  cases tag : ForwardEdge.present r.parent.graph.core.matching <;>
    simp only [decideFuel, tag, Bool.false_eq_true, ite_false, ite_true, augmentFuel] <;> omega

end PNP.Concrete.NormalizerBlocks.Search
