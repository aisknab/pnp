/-
Copyright (c) 2026 PNP Labs.

Executable, fail-closed residual-route primitives for explicit finite candidate
lists.  Search failure excludes only a gain present in the supplied list.  It
does not establish global minimality, zero residual slack, route completeness,
or any runtime bound.
-/

import PNP.NANDSlack

namespace PNP
namespace DirectWire

/-- A semantically equivalent implementation with strictly fewer NAND gates. -/
structure StrictEquivalentGain {inputs outputs : Nat}
    (current next : Implementation inputs outputs) : Prop where
  smaller : next.gateCount < current.gateCount
  equivalent : Equivalent next.candidate.program next.candidate.directWireWord
    current.candidate.program current.candidate.directWireWord

/-- Executable check for a strict equivalent gain. -/
def strictEquivalentGainBool {inputs outputs : Nat}
    (current next : Implementation inputs outputs) : Bool :=
  decide (next.gateCount < current.gateCount) &&
    equivalentBool next.candidate current.candidate

/-- A successful executable gain check is sound. -/
theorem strictEquivalentGainBool_sound {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    (checked : strictEquivalentGainBool current next = true) :
    StrictEquivalentGain current next := by
  unfold strictEquivalentGainBool at checked
  cases smallerCheck : decide (next.gateCount < current.gateCount) with
  | false =>
      rw [smallerCheck] at checked
      exact False.elim (Bool.noConfusion checked)
  | true =>
      rw [smallerCheck] at checked
      exact ⟨of_decide_eq_true smallerCheck, equivalentBool_sound checked⟩

/-- Every proof-bearing strict gain makes the executable check succeed. -/
theorem strictEquivalentGainBool_complete {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    (gain : StrictEquivalentGain current next) :
    strictEquivalentGainBool current next = true := by
  unfold strictEquivalentGainBool
  rw [decide_eq_true gain.smaller]
  exact equivalentBool_complete gain.equivalent

/-- The Boolean check exactly recognizes strict equivalent gains. -/
theorem strictEquivalentGainBool_eq_true_iff {inputs outputs : Nat}
    (current next : Implementation inputs outputs) :
    strictEquivalentGainBool current next = true ↔
      StrictEquivalentGain current next :=
  ⟨strictEquivalentGainBool_sound, strictEquivalentGainBool_complete⟩

/-- Return the first strict equivalent gain in an explicit candidate list. -/
def firstListedGain {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    List (Implementation inputs outputs) →
      Option (Implementation inputs outputs)
  | [] => none
  | next :: remaining =>
      if strictEquivalentGainBool current next = true then
        some next
      else
        firstListedGain current remaining

/-- A returned candidate is a member of the supplied list and a genuine gain. -/
theorem firstListedGain_sound {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    {listed : List (Implementation inputs outputs)}
    (found : firstListedGain current listed = some next) :
    next ∈ listed ∧ StrictEquivalentGain current next := by
  induction listed with
  | nil => cases found
  | cons head tail ih =>
      unfold firstListedGain at found
      split at found
      next headGain =>
        cases found
        exact ⟨List.Mem.head _, strictEquivalentGainBool_sound headGain⟩
      next _headNotGain =>
        have tailSound := ih found
        exact ⟨List.Mem.tail head tailSound.1, tailSound.2⟩

/-- Search failure excludes gains only inside the explicitly supplied list. -/
theorem firstListedGain_none_no_listed_gain {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {listed : List (Implementation inputs outputs)}
    (notFound : firstListedGain current listed = none) :
    ∀ next, next ∈ listed → ¬StrictEquivalentGain current next := by
  intro next member
  induction member with
  | head =>
      intro gain
      unfold firstListedGain at notFound
      rw [if_pos (strictEquivalentGainBool_complete gain)] at notFound
      cases notFound
  | tail head _tailMember ih =>
      unfold firstListedGain at notFound
      split at notFound
      next _headGain => cases notFound
      next _headNotGain => exact ih notFound

/-- Proof-bearing result for a gain returned from an explicit list. -/
structure ListedGainResult {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (listed : List (Implementation inputs outputs)) where
  next : Implementation inputs outputs
  member : next ∈ listed
  gain : StrictEquivalentGain current next

/-- Reify scanner soundness as a proof-bearing gain result. -/
def listedGainResultOfScan {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    {listed : List (Implementation inputs outputs)}
    (found : firstListedGain current listed = some next) :
    ListedGainResult current listed :=
  ⟨next, (firstListedGain_sound found).1, (firstListedGain_sound found).2⟩

/-- Constructive strict monotonicity of subtraction above the subtrahend. -/
theorem natSub_lt_natSub_of_le_of_lt
    (minimum smaller larger : Nat)
    (minimumWithin : minimum ≤ smaller)
    (strict : smaller < larger) :
    smaller - minimum < larger - minimum := by
  induction minimum generalizing smaller larger with
  | zero =>
      rw [Nat.sub_zero, Nat.sub_zero]
      exact strict
  | succ minimum ih =>
      cases smaller with
      | zero => exact False.elim (Nat.not_succ_le_zero minimum minimumWithin)
      | succ smaller =>
          cases larger with
          | zero => exact False.elim (Nat.not_lt_zero _ strict)
          | succ larger =>
              rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
              exact ih smaller larger
                (Nat.le_of_succ_le_succ minimumWithin)
                (Nat.lt_of_succ_lt_succ strict)

/-- Equivalent implementations have the same exhaustive reference minimum. -/
theorem StrictEquivalentGain.referenceMinimum_eq {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    (gain : StrictEquivalentGain current next) :
    referenceMinimum next = referenceMinimum current :=
  referenceMinimum_invariant next current gain.equivalent

/-- Every proof-bearing strict gain strictly decreases reference residual slack. -/
theorem StrictEquivalentGain.strictResidualDescent {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    (gain : StrictEquivalentGain current next) :
    residualSlack next < residualSlack current := by
  have minimumWithinNext : referenceMinimum current ≤ next.gateCount := by
    rw [← gain.referenceMinimum_eq]
    exact referenceMinimum_le_target next
  unfold residualSlack
  rw [gain.referenceMinimum_eq]
  exact natSub_lt_natSub_of_le_of_lt
    (referenceMinimum current) next.gateCount current.gateCount
    minimumWithinNext gain.smaller

/-- Scanner result packaged with strict residual-slack descent. -/
theorem ListedGainResult.strictResidualDescent {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {listed : List (Implementation inputs outputs)}
    (result : ListedGainResult current listed) :
    residualSlack result.next < residualSlack current :=
  result.gain.strictResidualDescent

/-- A terminal exact result contains an equivalent globally minimal candidate. -/
structure ExactMinimumResult {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  result : Implementation inputs outputs
  equivalent : Equivalent result.candidate.program result.candidate.directWireWord
    current.candidate.program current.candidate.directWireWord
  minimum : IsSemanticallyMinimum result

/-- The returned exact result has the exhaustive minimum gate count. -/
theorem ExactMinimumResult.gateCount_eq_referenceMinimum
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (exact : ExactMinimumResult current) :
    exact.result.gateCount = referenceMinimum current := by
  apply Nat.le_antisymm
  · apply exact.minimum (referenceMinimumWitness current)
    exact Equivalent.trans
      (equivalentBool_sound (referenceMinimumWitness_equivalent current))
      (Equivalent.symm exact.equivalent)
  · exact referenceMinimum_le_of_equivalent current
      exact.result.candidate exact.equivalent

/-- The proof-bearing exact result itself has zero residual slack. -/
theorem ExactMinimumResult.result_zeroSlack
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (exact : ExactMinimumResult current) :
    residualSlack exact.result = 0 :=
  (residualSlack_eq_zero_iff_minimum exact.result).mpr exact.minimum

/-- A ZeroSlack result is inhabited only by a proof of global semantic minimality. -/
structure ZeroSlackResult {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Prop where
  minimum : IsSemanticallyMinimum current

/-- A proof-bearing ZeroSlack result really has zero reference residual slack. -/
theorem ZeroSlackResult.sound {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (result : ZeroSlackResult current) :
    residualSlack current = 0 :=
  (residualSlack_eq_zero_iff_minimum current).mpr result.minimum

/-- An unresolved scan records only failure to find a gain in one supplied list. -/
structure UnresolvedResult {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (listed : List (Implementation inputs outputs)) : Prop where
  scanNone : firstListedGain current listed = none

/-- Unresolved excludes only gains appearing in the supplied list. -/
theorem UnresolvedResult.noListedGain {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {listed : List (Implementation inputs outputs)}
    (unresolved : UnresolvedResult current listed) :
    ∀ next, next ∈ listed → ¬StrictEquivalentGain current next :=
  firstListedGain_none_no_listed_gain unresolved.scanNone

/-- The executable scanner can return only a gain or a fail-closed unresolved
    result; it cannot manufacture exactness or ZeroSlack from search failure. -/
inductive GainScanOutcome {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (listed : List (Implementation inputs outputs)) where
  | gain : ListedGainResult current listed → GainScanOutcome current listed
  | unresolved : UnresolvedResult current listed → GainScanOutcome current listed

/-- Execute the explicit-list gain scan with its proof-bearing result. -/
def scanListedGains {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (listed : List (Implementation inputs outputs)) :
    GainScanOutcome current listed :=
  match found : firstListedGain current listed with
  | some _next => .gain (listedGainResultOfScan found)
  | none => .unresolved ⟨found⟩

/-- A wider oracle result can report exactness or ZeroSlack only by carrying
    the corresponding Lean proof. -/
inductive ResidualRouteResult {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (listed : List (Implementation inputs outputs)) where
  | gain : ListedGainResult current listed → ResidualRouteResult current listed
  | exact : ExactMinimumResult current → ResidualRouteResult current listed
  | zeroSlack : ZeroSlackResult current → ResidualRouteResult current listed
  | unresolved : UnresolvedResult current listed → ResidualRouteResult current listed

/-- A one-gate implementation whose sole output bypasses its unused gate. -/
def redundantIdentityCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord notProgram
    ⟨fun _ => .input fin1Zero⟩

def redundantIdentityImplementation : Implementation 1 1 :=
  ⟨1, redundantIdentityCandidate⟩

/-- The redundant implementation has the zero-gate identity semantics. -/
theorem identityCandidate_equivalent_redundantIdentity :
    Equivalent
      (Candidate.ofDirectWireWord identityProgram identityWord).program
      (Candidate.ofDirectWireWord identityProgram identityWord).directWireWord
      redundantIdentityCandidate.program
      redundantIdentityCandidate.directWireWord := by
  intro input output
  have outputEqual : output = fin1Zero := by
    apply Fin.ext
    cases output with
    | mk value isLt =>
        cases value with
        | zero => rfl
        | succ earlier =>
            exact False.elim
              (Nat.not_lt_zero earlier (Nat.lt_of_succ_lt_succ isLt))
  rw [outputEqual]
  rfl

/-- Exhaustive reference minimum detects the unused gate. -/
theorem redundantIdentity_referenceMinimum :
    referenceMinimum redundantIdentityImplementation = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact referenceMinimum_le_of_equivalent redundantIdentityImplementation
    (Candidate.ofDirectWireWord identityProgram identityWord)
    identityCandidate_equivalent_redundantIdentity

theorem redundantIdentity_positiveSlack :
    residualSlack redundantIdentityImplementation = 1 := by
  unfold residualSlack
  rw [redundantIdentity_referenceMinimum]
  rfl

/-- Regression witness: an unresolved empty-list scan can have positive slack.
    Therefore unresolved cannot soundly imply global minimality or ZeroSlack. -/
theorem unresolved_positiveSlack_regression :
    ∃ current : Implementation 1 1,
      UnresolvedResult current [] ∧ residualSlack current = 1 :=
  ⟨redundantIdentityImplementation, ⟨rfl⟩,
    redundantIdentity_positiveSlack⟩

end DirectWire
end PNP
