/-
Copyright (c) 2026 PNP Labs.

Executable exhaustive full/quotient terminal-profile minima.  Full matching
retains complete Boolean semantics and every computed profile coordinate;
quotient matching retains the same semantics but checks only coordinates kept
by an explicit projection.  The quotient search is therefore a relaxation of
the full search, so its minimum cannot exceed the full minimum.

This is the direct-wire reconstruction of the pinned manuscript's projection
monotonicity edge.  The scans are finite reference computations through the
current gate count.  No polynomial runtime, proper-support extraction,
saturation, transfer identity, BCELReady, ZeroSlack, or PCCMin claim is made.
-/

import PNP.ResidualTerminalModeFirewall

namespace PNP
namespace DirectWire

/-! ## Generic private finite scan -/

private def firstProfileCandidate
    {inputs outputs candidateGates : Nat}
    (accepts : Implementation inputs outputs → Bool) :
    List (Candidate inputs candidateGates outputs) →
      Option (Candidate inputs candidateGates outputs)
  | [] => none
  | candidate :: candidates =>
      if accepts ⟨candidateGates, candidate⟩ = true then
        some candidate
      else
        firstProfileCandidate accepts candidates

private theorem firstProfileCandidate_sound
    {inputs outputs candidateGates : Nat}
    {accepts : Implementation inputs outputs → Bool}
    {candidates : List (Candidate inputs candidateGates outputs)}
    {found : Candidate inputs candidateGates outputs}
    (foundAt : firstProfileCandidate accepts candidates = some found) :
    found ∈ candidates ∧ accepts ⟨candidateGates, found⟩ = true := by
  induction candidates with
  | nil => cases foundAt
  | cons head tail ih =>
      unfold firstProfileCandidate at foundAt
      split at foundAt
      next headMatches =>
        cases foundAt
        exact ⟨List.Mem.head _, headMatches⟩
      next _headDoesNotMatch =>
        have tailResult := ih foundAt
        exact ⟨List.Mem.tail head tailResult.1, tailResult.2⟩

private theorem firstProfileCandidate_exists_of_mem
    {inputs outputs candidateGates : Nat}
    {accepts : Implementation inputs outputs → Bool}
    {candidate : Candidate inputs candidateGates outputs}
    {candidates : List (Candidate inputs candidateGates outputs)}
    (member : candidate ∈ candidates)
    (matchProof : accepts ⟨candidateGates, candidate⟩ = true) :
    ∃ found, firstProfileCandidate accepts candidates = some found := by
  induction member with
  | head =>
      refine ⟨candidate, ?_⟩
      unfold firstProfileCandidate
      rw [if_pos matchProof]
  | tail head _tailMember ih =>
      if headMatches : accepts ⟨candidateGates, head⟩ = true then
        refine ⟨head, ?_⟩
        unfold firstProfileCandidate
        rw [if_pos headMatches]
      else
        obtain ⟨found, foundAt⟩ := ih
        refine ⟨found, ?_⟩
        unfold firstProfileCandidate
        rw [if_neg headMatches]
        exact foundAt

private def firstProfileAt
    {inputs outputs : Nat}
    (accepts : Implementation inputs outputs → Bool)
    (gateCount : Nat) : Option (Candidate inputs gateCount outputs) :=
  firstProfileCandidate accepts (allCandidates inputs gateCount outputs)

private theorem firstProfileAt_sound
    {inputs outputs gateCount : Nat}
    {accepts : Implementation inputs outputs → Bool}
    {found : Candidate inputs gateCount outputs}
    (foundAt : firstProfileAt accepts gateCount = some found) :
    accepts ⟨gateCount, found⟩ = true :=
  (firstProfileCandidate_sound foundAt).2

private theorem firstProfileAt_exists
    {inputs outputs gateCount : Nat}
    (accepts : Implementation inputs outputs → Bool)
    (candidate : Candidate inputs gateCount outputs)
    (matchProof : accepts ⟨gateCount, candidate⟩ = true) :
    ∃ found, firstProfileAt accepts gateCount = some found :=
  firstProfileCandidate_exists_of_mem (mem_allCandidates candidate) matchProof

private def scanProfileSizes
    {inputs outputs : Nat}
    (accepts : Implementation inputs outputs → Bool) :
    (bound : Nat) → Option (Implementation inputs outputs)
  | 0 =>
      match firstProfileAt accepts 0 with
      | none => none
      | some candidate => some ⟨0, candidate⟩
  | bound + 1 =>
      match scanProfileSizes accepts bound with
      | some found => some found
      | none =>
          match firstProfileAt accepts (bound + 1) with
          | none => none
          | some candidate => some ⟨bound + 1, candidate⟩

private theorem scanProfileSizes_sound
    {inputs outputs bound : Nat}
    {accepts : Implementation inputs outputs → Bool}
    {found : Implementation inputs outputs}
    (foundAt : scanProfileSizes accepts bound = some found) :
    found.gateCount ≤ bound ∧ accepts found = true := by
  induction bound with
  | zero =>
      unfold scanProfileSizes at foundAt
      cases exactResult : firstProfileAt accepts 0 with
      | none =>
          rw [exactResult] at foundAt
          cases foundAt
      | some candidate =>
          rw [exactResult] at foundAt
          cases foundAt
          exact ⟨Nat.le_refl 0, firstProfileAt_sound exactResult⟩
  | succ bound ih =>
      unfold scanProfileSizes at foundAt
      cases earlierResult : scanProfileSizes accepts bound with
      | some earlier =>
          rw [earlierResult] at foundAt
          cases foundAt
          have earlierSound := ih earlierResult
          exact ⟨Nat.le_trans earlierSound.1 (Nat.le_succ bound),
            earlierSound.2⟩
      | none =>
          rw [earlierResult] at foundAt
          cases exactResult : firstProfileAt accepts (bound + 1) with
          | none =>
              rw [exactResult] at foundAt
              cases foundAt
          | some candidate =>
              rw [exactResult] at foundAt
              cases foundAt
              exact ⟨Nat.le_refl (bound + 1),
                firstProfileAt_sound exactResult⟩

private theorem scanProfileSizes_exists_of_candidate
    {inputs outputs bound gateCount : Nat}
    (accepts : Implementation inputs outputs → Bool)
    (candidate : Candidate inputs gateCount outputs)
    (withinBound : gateCount ≤ bound)
    (matchProof : accepts ⟨gateCount, candidate⟩ = true) :
    ∃ found, scanProfileSizes accepts bound = some found := by
  induction bound with
  | zero =>
      have gateCountZero : gateCount = 0 := Nat.eq_zero_of_le_zero withinBound
      cases gateCountZero
      obtain ⟨found, foundAt⟩ :=
        firstProfileAt_exists accepts candidate matchProof
      refine ⟨⟨0, found⟩, ?_⟩
      unfold scanProfileSizes
      rw [foundAt]
  | succ bound ih =>
      cases earlierResult : scanProfileSizes accepts bound with
      | some earlier =>
          refine ⟨earlier, ?_⟩
          unfold scanProfileSizes
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
              firstProfileAt_exists accepts candidate matchProof
            refine ⟨⟨bound + 1, found⟩, ?_⟩
            unfold scanProfileSizes
            rw [earlierResult, foundAt]

private theorem scanProfileSizes_minimal
    {inputs outputs bound gateCount : Nat}
    {accepts : Implementation inputs outputs → Bool}
    {found : Implementation inputs outputs}
    (foundAt : scanProfileSizes accepts bound = some found)
    (candidate : Candidate inputs gateCount outputs)
    (withinBound : gateCount ≤ bound)
    (matchProof : accepts ⟨gateCount, candidate⟩ = true) :
    found.gateCount ≤ gateCount := by
  induction bound with
  | zero =>
      exact Nat.le_trans (scanProfileSizes_sound foundAt).1
        (Nat.zero_le gateCount)
  | succ bound ih =>
      unfold scanProfileSizes at foundAt
      cases earlierResult : scanProfileSizes accepts bound with
      | some earlier =>
          rw [earlierResult] at foundAt
          cases foundAt
          if withinEarlier : gateCount ≤ bound then
            exact ih earlierResult withinEarlier
          else
            have boundBeforeGate : bound < gateCount :=
              Nat.lt_of_not_ge withinEarlier
            exact Nat.le_trans (scanProfileSizes_sound earlierResult).1
              (Nat.le_of_lt boundBeforeGate)
      | none =>
          rw [earlierResult] at foundAt
          cases exactResult : firstProfileAt accepts (bound + 1) with
          | none =>
              rw [exactResult] at foundAt
              cases foundAt
          | some exactCandidate =>
              rw [exactResult] at foundAt
              cases foundAt
              if withinEarlier : gateCount ≤ bound then
                obtain ⟨earlier, earlierAt⟩ :=
                  scanProfileSizes_exists_of_candidate accepts candidate
                    withinEarlier matchProof
                rw [earlierResult] at earlierAt
                cases earlierAt
              else
                exact Nat.succ_le_of_lt (Nat.lt_of_not_ge withinEarlier)

private theorem scanProfileSizes_global_minimal
    {inputs outputs bound gateCount : Nat}
    {accepts : Implementation inputs outputs → Bool}
    {found : Implementation inputs outputs}
    (foundAt : scanProfileSizes accepts bound = some found)
    (candidate : Candidate inputs gateCount outputs)
    (matchProof : accepts ⟨gateCount, candidate⟩ = true) :
    found.gateCount ≤ gateCount := by
  if withinBound : gateCount ≤ bound then
    exact scanProfileSizes_minimal foundAt candidate withinBound matchProof
  else
    exact Nat.le_trans (scanProfileSizes_sound foundAt).1
      (Nat.le_of_lt (Nat.lt_of_not_ge withinBound))

/-! ## Full and quotient match predicates -/

/-- A candidate is semantically equivalent and agrees at every computed full
    profile coordinate. -/
def terminalFullProfileMatchBool
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current candidate : Implementation inputs outputs) : Bool :=
  equivalentBool candidate.candidate current.candidate &&
    allTrue (allFin profileWidth) (fun coordinate =>
      boolEqual (system.observe candidate coordinate)
        (system.observe current coordinate))

/-- A candidate is semantically equivalent and agrees at every profile
    coordinate retained by the quotient projection. -/
def terminalQuotientProfileMatchBool
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current candidate : Implementation inputs outputs) : Bool :=
  equivalentBool candidate.candidate current.candidate &&
    allTrue (allFin profileWidth) (fun coordinate =>
      if projection.keep coordinate = true then
        boolEqual (system.observe candidate coordinate)
          (system.observe current coordinate)
      else
        true)

/-- Successful full-profile matching produces complete full-carrier evidence. -/
def terminalFullProfileMatchBool_sound
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current candidate : Implementation inputs outputs}
    (checked : terminalFullProfileMatchBool system current candidate = true) :
    TerminalFullCarrierRealization system current := by
  simp only [terminalFullProfileMatchBool, Bool.and_eq_true] at checked
  exact
    { realization :=
        { implementation := candidate
          equivalent := equivalentBool_sound checked.1 }
      profileEqual := by
        intro coordinate
        have coordinateCheck :=
          allTrue_sound checked.2 (mem_allFin coordinate)
        exact (boolEqual_eq_true_iff _ _).mp coordinateCheck }

/-- Complete full-carrier evidence makes the Boolean matcher succeed. -/
theorem terminalFullProfileMatchBool_complete
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    terminalFullProfileMatchBool system current
      full.realization.implementation = true := by
  unfold terminalFullProfileMatchBool
  simp only [Bool.and_eq_true]
  constructor
  · exact equivalentBool_complete full.realization.equivalent
  · apply allTrue_complete
    intro coordinate _member
    exact (boolEqual_eq_true_iff _ _).mpr (full.profileEqual coordinate)

/-- Successful quotient matching produces comparison-only quotient evidence. -/
def terminalQuotientProfileMatchBool_sound
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current candidate : Implementation inputs outputs}
    (checked : terminalQuotientProfileMatchBool system projection current candidate = true) :
    TerminalQuotientComparison system projection current := by
  simp only [terminalQuotientProfileMatchBool, Bool.and_eq_true] at checked
  exact
    { realization :=
        { implementation := candidate
          equivalent := equivalentBool_sound checked.1 }
      keptProfileEqual := by
        intro coordinate kept
        have coordinateCheck :=
          allTrue_sound checked.2 (mem_allFin coordinate)
        change projection.keep coordinate = true at kept
        rw [kept] at coordinateCheck
        exact (boolEqual_eq_true_iff _ _).mp coordinateCheck }

/-- Quotient-comparison evidence makes the Boolean matcher succeed. -/
theorem terminalQuotientProfileMatchBool_complete
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) :
    terminalQuotientProfileMatchBool system projection current
      comparison.realization.implementation = true := by
  unfold terminalQuotientProfileMatchBool
  simp only [Bool.and_eq_true]
  constructor
  · exact equivalentBool_complete comparison.realization.equivalent
  · apply allTrue_complete
    intro coordinate _member
    cases kept : projection.keep coordinate with
    | false => rfl
    | true =>
        exact (boolEqual_eq_true_iff _ _).mpr
          (comparison.keptProfileEqual coordinate kept)

/-- The current implementation is a canonical complete full-carrier
    realization of itself for every computed profile system. -/
def terminalCurrentFullCarrierRealization
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    TerminalFullCarrierRealization system current :=
  { realization := terminalize current
    profileEqual := fun _coordinate => rfl }

/-- The current implementation also supplies a canonical quotient comparison. -/
def terminalCurrentQuotientComparison
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    TerminalQuotientComparison system projection current :=
  (terminalCurrentFullCarrierRealization system current).project

/-! ## Total exhaustive profile minima -/

private theorem terminalFullProfileScan_exists
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    ∃ found,
      scanProfileSizes (terminalFullProfileMatchBool system current)
        current.gateCount = some found := by
  apply scanProfileSizes_exists_of_candidate
    (terminalFullProfileMatchBool system current) current.candidate
    (Nat.le_refl current.gateCount)
  change terminalFullProfileMatchBool system current current = true
  exact terminalFullProfileMatchBool_complete
    (terminalCurrentFullCarrierRealization system current)

private theorem terminalQuotientProfileScan_exists
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    ∃ found,
      scanProfileSizes
        (terminalQuotientProfileMatchBool system projection current)
        current.gateCount = some found := by
  apply scanProfileSizes_exists_of_candidate
    (terminalQuotientProfileMatchBool system projection current)
    current.candidate (Nat.le_refl current.gateCount)
  change terminalQuotientProfileMatchBool system projection current current = true
  exact terminalQuotientProfileMatchBool_complete
    (terminalCurrentQuotientComparison system projection current)

/-- The total exhaustive minimum implementation satisfying full-profile
    equality.  The fallback branch is unreachable. -/
def terminalFullProfileMinimumImplementation
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) : Implementation inputs outputs :=
  match scanProfileSizes (terminalFullProfileMatchBool system current)
      current.gateCount with
  | some found => found
  | none => current

/-- The total exhaustive minimum implementation satisfying quotient-profile
    equality.  The fallback branch is unreachable. -/
def terminalQuotientProfileMinimumImplementation
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) : Implementation inputs outputs :=
  match scanProfileSizes
      (terminalQuotientProfileMatchBool system projection current)
      current.gateCount with
  | some found => found
  | none => current

private theorem scan_terminalFullProfileMinimumImplementation
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    scanProfileSizes (terminalFullProfileMatchBool system current)
        current.gateCount =
      some (terminalFullProfileMinimumImplementation system current) := by
  obtain ⟨found, foundAt⟩ := terminalFullProfileScan_exists system current
  unfold terminalFullProfileMinimumImplementation
  rw [foundAt]

private theorem scan_terminalQuotientProfileMinimumImplementation
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    scanProfileSizes
        (terminalQuotientProfileMatchBool system projection current)
        current.gateCount =
      some (terminalQuotientProfileMinimumImplementation
        system projection current) := by
  obtain ⟨found, foundAt⟩ :=
    terminalQuotientProfileScan_exists system projection current
  unfold terminalQuotientProfileMinimumImplementation
  rw [foundAt]

/-- Full-mode profile-constrained minimum NAND-gate count. -/
def terminalFullProfileMinimum
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) : Nat :=
  (terminalFullProfileMinimumImplementation system current).gateCount

/-- Quotient-mode profile-constrained minimum NAND-gate count. -/
def terminalQuotientProfileMinimum
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) : Nat :=
  (terminalQuotientProfileMinimumImplementation system projection current).gateCount

/-- The computed full minimum is attained by complete full-carrier evidence. -/
def terminalFullProfileMinimumRealization
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    TerminalFullCarrierRealization system current :=
  terminalFullProfileMatchBool_sound
    (scanProfileSizes_sound
      (scan_terminalFullProfileMinimumImplementation system current)).2

/-- The computed quotient minimum is attained by quotient-comparison evidence. -/
def terminalQuotientProfileMinimumComparison
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    TerminalQuotientComparison system projection current :=
  terminalQuotientProfileMatchBool_sound
    (scanProfileSizes_sound
      (scan_terminalQuotientProfileMinimumImplementation
        system projection current)).2

@[simp] theorem terminalFullProfileMinimumRealization_gateCount
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (terminalFullProfileMinimumRealization system current).realization.implementation.gateCount =
      terminalFullProfileMinimum system current := rfl

@[simp] theorem terminalQuotientProfileMinimumComparison_gateCount
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    (terminalQuotientProfileMinimumComparison system projection current).realization.implementation.gateCount =
      terminalQuotientProfileMinimum system projection current := rfl

/-- The full-profile minimum lower-bounds every complete full-carrier
    realization, at every exact gate count. -/
theorem terminalFullProfileMinimum_le
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    terminalFullProfileMinimum system current ≤
      full.realization.implementation.gateCount := by
  change (terminalFullProfileMinimumImplementation system current).gateCount ≤
    full.realization.implementation.gateCount
  exact scanProfileSizes_global_minimal
    (scan_terminalFullProfileMinimumImplementation system current)
    full.realization.implementation.candidate
    (terminalFullProfileMatchBool_complete full)

/-- The quotient-profile minimum lower-bounds every quotient comparison, at
    every exact gate count. -/
theorem terminalQuotientProfileMinimum_le
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) :
    terminalQuotientProfileMinimum system projection current ≤
      comparison.realization.implementation.gateCount := by
  change (terminalQuotientProfileMinimumImplementation
      system projection current).gateCount ≤
    comparison.realization.implementation.gateCount
  exact scanProfileSizes_global_minimal
    (scan_terminalQuotientProfileMinimumImplementation
      system projection current)
    comparison.realization.implementation.candidate
    (terminalQuotientProfileMatchBool_complete comparison)

/-- Attainment and universal lower bound for the full-profile minimum. -/
theorem terminalFullProfileMinimum_spec
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (terminalFullProfileMinimumRealization system current).realization.implementation.gateCount =
        terminalFullProfileMinimum system current ∧
      ∀ full : TerminalFullCarrierRealization system current,
        terminalFullProfileMinimum system current ≤
          full.realization.implementation.gateCount :=
  ⟨terminalFullProfileMinimumRealization_gateCount system current,
    fun full => terminalFullProfileMinimum_le full⟩

/-- Attainment and universal lower bound for the quotient-profile minimum. -/
theorem terminalQuotientProfileMinimum_spec
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    (terminalQuotientProfileMinimumComparison system projection current).realization.implementation.gateCount =
        terminalQuotientProfileMinimum system projection current ∧
      ∀ comparison : TerminalQuotientComparison system projection current,
        terminalQuotientProfileMinimum system projection current ≤
          comparison.realization.implementation.gateCount :=
  ⟨terminalQuotientProfileMinimumComparison_gateCount
      system projection current,
    fun comparison => terminalQuotientProfileMinimum_le comparison⟩

/-! ## Projection monotonicity and the checked-lift boundary -/

/-- Legacy projection monotonicity: forgetting finite profile coordinates can
    only weakly decrease the exhaustive comparison minimum. -/
theorem terminalProjectionMinimum_mono
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    terminalQuotientProfileMinimum system projection current ≤
      terminalFullProfileMinimum system current := by
  have lower := terminalQuotientProfileMinimum_le
    ((terminalFullProfileMinimumRealization system current).project
      (projection := projection))
  rw [TerminalFullCarrierRealization.project_gateCount] at lower
  rw [terminalFullProfileMinimumRealization_gateCount] at lower
  exact lower

/-- The nonnegative information-loss gap between the full and quotient
    profile-constrained minima. -/
def terminalProjectionDefect
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) : Nat :=
  terminalFullProfileMinimum system current -
    terminalQuotientProfileMinimum system projection current

/-- Exact additive decomposition of the full minimum into quotient minimum
    plus projection defect. -/
theorem terminalQuotientMinimum_add_projectionDefect
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    terminalQuotientProfileMinimum system projection current +
        terminalProjectionDefect system projection current =
      terminalFullProfileMinimum system current := by
  unfold terminalProjectionDefect
  exact natAdd_sub_of_le
    (terminalProjectionMinimum_mono system projection current)

/-- Zero projection defect is exactly equality of the two exhaustive minima. -/
theorem terminalProjectionDefect_eq_zero_iff_minima_eq
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    terminalProjectionDefect system projection current = 0 ↔
      terminalQuotientProfileMinimum system projection current =
        terminalFullProfileMinimum system current := by
  constructor
  · intro defectZero
    have fullWithinQuotient :
        terminalFullProfileMinimum system current ≤
          terminalQuotientProfileMinimum system projection current := by
      exact le_of_natSub_eq_zero
        (terminalFullProfileMinimum system current)
        (terminalQuotientProfileMinimum system projection current)
        defectZero
    exact Nat.le_antisymm
      (terminalProjectionMinimum_mono system projection current)
      fullWithinQuotient
  · intro minimaEqual
    unfold terminalProjectionDefect
    rw [minimaEqual]
    exact Nat.sub_self _

/-- The two minima agree exactly when some quotient-minimum comparison carries
    the checked full lift required by the mode firewall. -/
theorem terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    terminalProjectionDefect system projection current = 0 ↔
      ∃ comparison : TerminalQuotientComparison system projection current,
        comparison.realization.implementation.gateCount =
            terminalQuotientProfileMinimum system projection current ∧
          TerminalCheckedFullLift comparison := by
  constructor
  · intro defectZero
    have minimaEqual :=
      (terminalProjectionDefect_eq_zero_iff_minima_eq
        system projection current).mp defectZero
    let full := terminalFullProfileMinimumRealization system current
    refine ⟨full.project (projection := projection), ?_,
      full.checkedFullLift⟩
    rw [full.project_gateCount]
    rw [terminalFullProfileMinimumRealization_gateCount]
    exact minimaEqual.symm
  · rintro ⟨comparison, atMinimum, lift⟩
    have fullWithinComparison := terminalFullProfileMinimum_le
      lift.fullRealization
    rw [lift.fullRealization_realization, atMinimum] at fullWithinComparison
    have minimaEqual :
        terminalQuotientProfileMinimum system projection current =
          terminalFullProfileMinimum system current :=
      Nat.le_antisymm
        (terminalProjectionMinimum_mono system projection current)
        fullWithinComparison
    exact (terminalProjectionDefect_eq_zero_iff_minima_eq
      system projection current).mpr minimaEqual

/-- A lossless projection makes the full and quotient minima equal. -/
theorem terminalProfileMinima_eq_of_keepsAll
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs)
    (keepsAll : projection.KeepsAll) :
    terminalQuotientProfileMinimum system projection current =
      terminalFullProfileMinimum system current := by
  let comparison :=
    terminalQuotientProfileMinimumComparison system projection current
  have lift := comparison.checkedFullLift_of_keepsAll keepsAll
  have defectZero :=
    (terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum
      system projection current).mpr
      ⟨comparison,
        terminalQuotientProfileMinimumComparison_gateCount
          system projection current,
        lift⟩
  exact (terminalProjectionDefect_eq_zero_iff_minima_eq
    system projection current).mp defectZero

/-- Positive defect rules out constructive full lifting at every attained
    quotient minimum, not merely at one chosen comparison. -/
theorem terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs)
    (positive : 0 < terminalProjectionDefect system projection current)
    (comparison : TerminalQuotientComparison system projection current)
    (atMinimum : comparison.realization.implementation.gateCount =
      terminalQuotientProfileMinimum system projection current) :
    ¬TerminalCheckedFullLift comparison := by
  intro lift
  have defectZero :=
    (terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum
      system projection current).mpr ⟨comparison, atMinimum, lift⟩
  exact (Nat.ne_of_gt positive) defectZero

end DirectWire
end PNP
