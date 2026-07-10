/-
Copyright (c) 2026 PNP Labs.

An exhaustive reference definition of exact direct-wire NAND minimum size.
This module makes no practical-runtime claim: it scans finite exact-size
candidate enumerations from size zero through the supplied target size.
-/

import PNP.NANDTruthTable

namespace PNP
namespace DirectWire

/-- A direct-wire implementation existentially carrying its exact gate count. -/
structure Implementation (inputs outputs : Nat) where
  gateCount : Nat
  candidate : Candidate inputs gateCount outputs

/-- Search one exact-size candidate list for the first semantic match. -/
def firstEquivalentCandidate {inputs outputs targetGates candidateGates : Nat}
    (target : Candidate inputs targetGates outputs) :
    List (Candidate inputs candidateGates outputs) →
      Option (Candidate inputs candidateGates outputs)
  | [] => none
  | candidate :: candidates =>
      if equivalentBool candidate target = true then
        some candidate
      else
        firstEquivalentCandidate target candidates

/-- Any candidate returned by the exact-size search is a listed match. -/
theorem firstEquivalentCandidate_sound
    {inputs outputs targetGates candidateGates : Nat}
    {target : Candidate inputs targetGates outputs}
    {candidates : List (Candidate inputs candidateGates outputs)}
    {found : Candidate inputs candidateGates outputs}
    (foundAt : firstEquivalentCandidate target candidates = some found) :
    found ∈ candidates ∧ equivalentBool found target = true := by
  induction candidates with
  | nil => cases foundAt
  | cons head tail ih =>
      unfold firstEquivalentCandidate at foundAt
      split at foundAt
      next headMatches =>
        cases foundAt
        exact ⟨List.Mem.head _, headMatches⟩
      next _headDoesNotMatch =>
        have tailResult := ih foundAt
        exact ⟨List.Mem.tail head tailResult.1, tailResult.2⟩

/-- A listed semantic match guarantees that the exact-size search succeeds. -/
theorem firstEquivalentCandidate_exists_of_mem
    {inputs outputs targetGates candidateGates : Nat}
    {target : Candidate inputs targetGates outputs}
    {candidate : Candidate inputs candidateGates outputs}
    {candidates : List (Candidate inputs candidateGates outputs)}
    (member : candidate ∈ candidates)
    (matchProof : equivalentBool candidate target = true) :
    ∃ found, firstEquivalentCandidate target candidates = some found := by
  induction member with
  | head =>
      refine ⟨candidate, ?_⟩
      unfold firstEquivalentCandidate
      rw [if_pos matchProof]
  | tail head tailMember ih =>
      if headMatches : equivalentBool head target = true then
        refine ⟨head, ?_⟩
        unfold firstEquivalentCandidate
        rw [if_pos headMatches]
      else
        obtain ⟨found, foundAt⟩ := ih
        refine ⟨found, ?_⟩
        unfold firstEquivalentCandidate
        rw [if_neg headMatches]
        exact foundAt

/-- Search all enumerated candidates at one exact gate count. -/
def firstEquivalentAt {inputs outputs : Nat}
    (target : Implementation inputs outputs) (gateCount : Nat) :
    Option (Candidate inputs gateCount outputs) :=
  firstEquivalentCandidate target.candidate
    (allCandidates inputs gateCount outputs)

theorem firstEquivalentAt_sound {inputs outputs gateCount : Nat}
    {target : Implementation inputs outputs}
    {found : Candidate inputs gateCount outputs}
    (foundAt : firstEquivalentAt target gateCount = some found) :
    found ∈ allCandidates inputs gateCount outputs ∧
      equivalentBool found target.candidate = true :=
  firstEquivalentCandidate_sound foundAt

theorem firstEquivalentAt_exists {inputs outputs gateCount : Nat}
    (target : Implementation inputs outputs)
    (candidate : Candidate inputs gateCount outputs)
    (matchProof : equivalentBool candidate target.candidate = true) :
    ∃ found, firstEquivalentAt target gateCount = some found :=
  firstEquivalentCandidate_exists_of_mem (mem_allCandidates candidate) matchProof

/-- Scan exact gate counts in increasing order through `bound`. -/
def scanEquivalentSizes {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    (bound : Nat) → Option (Implementation inputs outputs)
  | 0 =>
      match firstEquivalentAt target 0 with
      | none => none
      | some candidate => some ⟨0, candidate⟩
  | bound + 1 =>
      match scanEquivalentSizes target bound with
      | some found => some found
      | none =>
          match firstEquivalentAt target (bound + 1) with
          | none => none
          | some candidate => some ⟨bound + 1, candidate⟩

/-- A successful bounded scan returns an equivalent implementation in range. -/
theorem scanEquivalentSizes_sound {inputs outputs bound : Nat}
    {target found : Implementation inputs outputs}
    (foundAt : scanEquivalentSizes target bound = some found) :
    found.gateCount ≤ bound ∧
      equivalentBool found.candidate target.candidate = true := by
  induction bound with
  | zero =>
      unfold scanEquivalentSizes at foundAt
      cases exactResult : firstEquivalentAt target 0 with
      | none =>
          rw [exactResult] at foundAt
          cases foundAt
      | some candidate =>
          rw [exactResult] at foundAt
          cases foundAt
          exact ⟨Nat.le_refl 0, (firstEquivalentAt_sound exactResult).2⟩
  | succ bound ih =>
      unfold scanEquivalentSizes at foundAt
      cases earlierResult : scanEquivalentSizes target bound with
      | some earlier =>
          rw [earlierResult] at foundAt
          cases foundAt
          have earlierSound := ih earlierResult
          exact ⟨Nat.le_trans earlierSound.1 (Nat.le_succ bound),
            earlierSound.2⟩
      | none =>
          rw [earlierResult] at foundAt
          cases exactResult : firstEquivalentAt target (bound + 1) with
          | none =>
              rw [exactResult] at foundAt
              cases foundAt
          | some candidate =>
              rw [exactResult] at foundAt
              cases foundAt
              exact ⟨Nat.le_refl (bound + 1),
                (firstEquivalentAt_sound exactResult).2⟩

/-- Any equivalent candidate in range makes the bounded scan succeed. -/
theorem scanEquivalentSizes_exists_of_candidate
    {inputs outputs bound gateCount : Nat}
    (target : Implementation inputs outputs)
    (candidate : Candidate inputs gateCount outputs)
    (withinBound : gateCount ≤ bound)
    (matchProof : equivalentBool candidate target.candidate = true) :
    ∃ found, scanEquivalentSizes target bound = some found := by
  induction bound with
  | zero =>
      have gateCountZero : gateCount = 0 := Nat.eq_zero_of_le_zero withinBound
      cases gateCountZero
      obtain ⟨found, foundAt⟩ :=
        firstEquivalentAt_exists target candidate matchProof
      refine ⟨⟨0, found⟩, ?_⟩
      unfold scanEquivalentSizes
      rw [foundAt]
  | succ bound ih =>
      cases earlierResult : scanEquivalentSizes target bound with
      | some earlier =>
          refine ⟨earlier, ?_⟩
          unfold scanEquivalentSizes
          rw [earlierResult]
      | none =>
          if withinEarlier : gateCount ≤ bound then
            obtain ⟨earlier, earlierAt⟩ := ih withinEarlier
            rw [earlierResult] at earlierAt
            cases earlierAt
          else
            have boundBeforeGate : bound < gateCount :=
              Nat.lt_of_not_ge withinEarlier
            have boundSuccLeGate : bound + 1 ≤ gateCount :=
              Nat.succ_le_of_lt boundBeforeGate
            have gateCountExact : gateCount = bound + 1 :=
              Nat.le_antisymm withinBound boundSuccLeGate
            cases gateCountExact
            obtain ⟨found, foundAt⟩ :=
              firstEquivalentAt_exists target candidate matchProof
            refine ⟨⟨bound + 1, found⟩, ?_⟩
            unfold scanEquivalentSizes
            rw [earlierResult, foundAt]

/-- The first successful exact-size result is no larger than any in-range
    equivalent candidate. -/
theorem scanEquivalentSizes_minimal
    {inputs outputs bound gateCount : Nat}
    {target found : Implementation inputs outputs}
    (foundAt : scanEquivalentSizes target bound = some found)
    (candidate : Candidate inputs gateCount outputs)
    (withinBound : gateCount ≤ bound)
    (matchProof : equivalentBool candidate target.candidate = true) :
    found.gateCount ≤ gateCount := by
  induction bound with
  | zero =>
      exact Nat.le_trans (scanEquivalentSizes_sound foundAt).1
        (Nat.zero_le gateCount)
  | succ bound ih =>
      unfold scanEquivalentSizes at foundAt
      cases earlierResult : scanEquivalentSizes target bound with
      | some earlier =>
          rw [earlierResult] at foundAt
          cases foundAt
          if withinEarlier : gateCount ≤ bound then
            exact ih earlierResult withinEarlier
          else
            have boundBeforeGate : bound < gateCount :=
              Nat.lt_of_not_ge withinEarlier
            exact Nat.le_trans (scanEquivalentSizes_sound earlierResult).1
              (Nat.le_of_lt boundBeforeGate)
      | none =>
          rw [earlierResult] at foundAt
          cases exactResult : firstEquivalentAt target (bound + 1) with
          | none =>
              rw [exactResult] at foundAt
              cases foundAt
          | some exactCandidate =>
              rw [exactResult] at foundAt
              cases foundAt
              if withinEarlier : gateCount ≤ bound then
                obtain ⟨earlier, earlierAt⟩ :=
                  scanEquivalentSizes_exists_of_candidate target candidate
                    withinEarlier matchProof
                rw [earlierResult] at earlierAt
                cases earlierAt
              else
                exact Nat.succ_le_of_lt (Nat.lt_of_not_ge withinEarlier)

/-- The target itself guarantees that scanning through its size succeeds. -/
theorem scanEquivalentSizes_target_exists {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    ∃ found,
      scanEquivalentSizes target target.gateCount = some found :=
  scanEquivalentSizes_exists_of_candidate target target.candidate
    (Nat.le_refl target.gateCount) (equivalentBool_refl target.candidate)

/-- The total reference minimum implementation.  The fallback branch is made
    unreachable by `scanEquivalentSizes_target_exists`. -/
def referenceMinimumImplementation {inputs outputs : Nat}
    (target : Implementation inputs outputs) : Implementation inputs outputs :=
  match scanEquivalentSizes target target.gateCount with
  | some found => found
  | none => target

/-- The exact reference minimum gate count for the target semantics. -/
def referenceMinimum {inputs outputs : Nat}
    (target : Implementation inputs outputs) : Nat :=
  (referenceMinimumImplementation target).gateCount

/-- A candidate intrinsically indexed by the computed reference minimum. -/
def referenceMinimumWitness {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    Candidate inputs (referenceMinimum target) outputs :=
  (referenceMinimumImplementation target).candidate

theorem scanEquivalentSizes_referenceMinimum {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    scanEquivalentSizes target target.gateCount =
      some (referenceMinimumImplementation target) := by
  obtain ⟨found, foundAt⟩ := scanEquivalentSizes_target_exists target
  unfold referenceMinimumImplementation
  rw [foundAt]

/-- The computed minimum has an exactly indexed equivalent witness. -/
theorem referenceMinimumWitness_equivalent {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    equivalentBool (referenceMinimumWitness target) target.candidate = true :=
  (scanEquivalentSizes_sound
    (scanEquivalentSizes_referenceMinimum target)).2

theorem referenceMinimumWitness_size {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    (referenceMinimumWitness target).program.size = referenceMinimum target :=
  Candidate.program_size_eq_gateCount (referenceMinimumWitness target)

/-- The exhaustive minimum never exceeds the supplied implementation size. -/
theorem referenceMinimum_le_target {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    referenceMinimum target ≤ target.gateCount :=
  (scanEquivalentSizes_sound
    (scanEquivalentSizes_referenceMinimum target)).1

/-- Boolean-equivalent candidates at any gate count respect the lower bound. -/
theorem referenceMinimum_le_of_equivalentBool
    {inputs outputs gateCount : Nat}
    (target : Implementation inputs outputs)
    (candidate : Candidate inputs gateCount outputs)
    (matchProof : equivalentBool candidate target.candidate = true) :
    referenceMinimum target ≤ gateCount := by
  if withinBound : gateCount ≤ target.gateCount then
    exact scanEquivalentSizes_minimal
      (scanEquivalentSizes_referenceMinimum target) candidate withinBound matchProof
  else
    have targetBeforeCandidate : target.gateCount < gateCount :=
      Nat.lt_of_not_ge withinBound
    exact Nat.le_trans (referenceMinimum_le_target target)
      (Nat.le_of_lt targetBeforeCandidate)

/-- Every semantically equivalent implementation, including one larger than
    the scan bound, is at least the computed minimum. -/
theorem referenceMinimum_le_of_equivalent
    {inputs outputs gateCount : Nat}
    (target : Implementation inputs outputs)
    (candidate : Candidate inputs gateCount outputs)
    (equivalent : Equivalent candidate.program candidate.directWireWord
      target.candidate.program target.candidate.directWireWord) :
    referenceMinimum target ≤ gateCount :=
  referenceMinimum_le_of_equivalentBool target candidate
    (equivalentBool_complete equivalent)

/-- Equivalent supplied implementations have the same exhaustive minimum. -/
theorem referenceMinimum_invariant {inputs outputs : Nat}
    (left right : Implementation inputs outputs)
    (equivalent : Equivalent left.candidate.program
      left.candidate.directWireWord right.candidate.program
      right.candidate.directWireWord) :
    referenceMinimum left = referenceMinimum right := by
  apply Nat.le_antisymm
  · apply referenceMinimum_le_of_equivalent left
      (referenceMinimumWitness right)
    exact Equivalent.trans
      (equivalentBool_sound (referenceMinimumWitness_equivalent right))
      (Equivalent.symm equivalent)
  · apply referenceMinimum_le_of_equivalent right
      (referenceMinimumWitness left)
    exact Equivalent.trans
      (equivalentBool_sound (referenceMinimumWitness_equivalent left))
      equivalent

/-- Reference residual slack of the supplied implementation. -/
def residualSlack {inputs outputs : Nat}
    (target : Implementation inputs outputs) : Nat :=
  target.gateCount - referenceMinimum target

/-- Constructive zero-subtraction direction, avoiding propositional rewrites. -/
theorem natSub_eq_zero_of_le (left right : Nat) (within : left ≤ right) :
    left - right = 0 := by
  induction left generalizing right with
  | zero => exact Nat.zero_sub right
  | succ left ih =>
      cases right with
      | zero => exact False.elim (Nat.not_succ_le_zero left within)
      | succ right =>
          exact (Nat.succ_sub_succ_eq_sub left right).trans
            (ih right (Nat.le_of_succ_le_succ within))

/-- Constructive converse: zero subtraction witnesses the corresponding bound. -/
theorem le_of_natSub_eq_zero (left right : Nat) (differenceZero : left - right = 0) :
    left ≤ right := by
  induction left generalizing right with
  | zero => exact Nat.zero_le right
  | succ left ih =>
      cases right with
      | zero =>
          change Nat.succ left = 0 at differenceZero
          exact False.elim (Nat.noConfusion differenceZero)
      | succ right =>
          apply Nat.succ_le_succ
          apply ih
          exact (Nat.succ_sub_succ_eq_sub left right).symm.trans differenceZero

/-- Semantic minimality among candidates of every exact gate count. -/
def IsSemanticallyMinimum {inputs outputs : Nat}
    (target : Implementation inputs outputs) : Prop :=
  ∀ {gateCount : Nat} (candidate : Candidate inputs gateCount outputs),
    Equivalent candidate.program candidate.directWireWord
      target.candidate.program target.candidate.directWireWord →
      target.gateCount ≤ gateCount

/-- Zero residual slack is exactly semantic minimum size. -/
theorem residualSlack_eq_zero_iff_minimum {inputs outputs : Nat}
    (target : Implementation inputs outputs) :
    residualSlack target = 0 ↔ IsSemanticallyMinimum target := by
  constructor
  · intro slackZero
    have targetLeMinimum : target.gateCount ≤ referenceMinimum target :=
      le_of_natSub_eq_zero target.gateCount (referenceMinimum target) slackZero
    have targetEqualsMinimum : target.gateCount = referenceMinimum target :=
      Nat.le_antisymm targetLeMinimum (referenceMinimum_le_target target)
    intro gateCount candidate equivalent
    rw [targetEqualsMinimum]
    exact referenceMinimum_le_of_equivalent target candidate equivalent
  · intro targetMinimum
    have targetLeMinimum : target.gateCount ≤ referenceMinimum target :=
      targetMinimum (referenceMinimumWitness target)
        (equivalentBool_sound (referenceMinimumWitness_equivalent target))
    exact natSub_eq_zero_of_le target.gateCount (referenceMinimum target)
      targetLeMinimum

end DirectWire
end PNP
