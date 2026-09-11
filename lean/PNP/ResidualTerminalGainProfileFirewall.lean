/-
Copyright (c) 2026 PNP Labs.

Computed full-profile acceptance for the actual production physical gain.
The supplied model is not derived manuscript carrier data. Search and minima
remain exhaustive, and a rejected profile is not a completed global route.
-/

import PNP.ResidualTerminalPhysicalGain

namespace PNP
namespace DirectWire

private theorem gainProfile_not_mismatch (left right : Bool) :
    (¬ (!boolEqual left right) = true) ↔ left = right := by
  cases left <;> cases right <;> decide

private theorem gainProfile_mismatch (left right : Bool) :
    (!boolEqual left right) = true ↔ left ≠ right := by
  cases left <;> cases right <;> decide

private theorem gainProfile_before_mismatch (left right : Bool) :
    (!(!boolEqual left right)) = true ↔ left = right := by
  cases left <;> cases right <;> decide

/-- Scan all full-profile coordinates in their canonical order. Boolean
    equivalence is not recomputed here: the production gain already proves it. -/
def firstTerminalGainProfileMismatch
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current replacement : Implementation inputs outputs) :
    Option (Fin profileWidth) :=
  (allFin profileWidth).find? fun coordinate =>
    !boolEqual (system.observe replacement coordinate)
      (system.observe current coordinate)

/-- No reported mismatch is exactly complete profile equality, not merely
    agreement on the coordinates retained by a quotient projection. -/
theorem firstTerminalGainProfileMismatch_eq_none_iff
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current replacement : Implementation inputs outputs) :
    firstTerminalGainProfileMismatch system current replacement = none ↔
      ∀ coordinate, system.observe replacement coordinate =
        system.observe current coordinate := by
  unfold firstTerminalGainProfileMismatch
  constructor
  · intro stopped coordinate
    have absent := (List.find?_eq_none.mp stopped) coordinate (mem_allFin coordinate)
    exact (gainProfile_not_mismatch _ _).mp absent
  · intro equal
    apply List.find?_eq_none.mpr
    intro coordinate _member
    exact (gainProfile_not_mismatch _ _).mpr (equal coordinate)

/-- A reported mismatch includes the complete agreeing canonical prefix.
    The coordinate's role and both values are read from the actual system. -/
theorem firstTerminalGainProfileMismatch_spec
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current replacement : Implementation inputs outputs)
    (coordinate : Fin profileWidth)
    (foundAt : firstTerminalGainProfileMismatch system current replacement =
      some coordinate) :
    system.observe replacement coordinate ≠ system.observe current coordinate ∧
      ∃ before after : List (Fin profileWidth),
        allFin profileWidth = before ++ coordinate :: after ∧
        ∀ earlier, earlier ∈ before →
          system.observe replacement earlier = system.observe current earlier := by
  obtain ⟨different, before, after, partition, agrees⟩ :=
    List.find?_eq_some_iff_append.mp foundAt
  refine ⟨(gainProfile_mismatch _ _).mp different,
    before, after, partition, ?_⟩
  intro earlier member
  exact (gainProfile_before_mismatch _ _).mp (agrees earlier member)

/-- Complete full-carrier realizations have the same exhaustive full-profile
    minimum. This does not equate it with the unconstrained Boolean minimum. -/
theorem terminalFullProfileMinimum_eq_of_fullRealization
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    terminalFullProfileMinimum system full.realization.implementation =
      terminalFullProfileMinimum system current := by
  let replacement := full.realization.implementation
  let currentMinimum := terminalFullProfileMinimumRealization system current
  let replacementMinimum := terminalFullProfileMinimumRealization system replacement
  let toCurrent : TerminalFullCarrierRealization system current :=
    { realization :=
        { implementation := replacementMinimum.realization.implementation
          equivalent := replacementMinimum.realization.equivalent.trans
            full.realization.equivalent }
      profileEqual := fun coordinate =>
        (replacementMinimum.profileEqual coordinate).trans (full.profileEqual coordinate) }
  let toReplacement : TerminalFullCarrierRealization system replacement :=
    { realization :=
        { implementation := currentMinimum.realization.implementation
          equivalent := currentMinimum.realization.equivalent.trans
            full.realization.equivalent.symm }
      profileEqual := fun coordinate =>
        (currentMinimum.profileEqual coordinate).trans (full.profileEqual coordinate).symm }
  have forward := terminalFullProfileMinimum_le toCurrent
  have backward := terminalFullProfileMinimum_le toReplacement
  change terminalFullProfileMinimum system current ≤
    terminalFullProfileMinimum system replacement at forward
  change terminalFullProfileMinimum system replacement ≤
    terminalFullProfileMinimum system current at backward
  exact Nat.le_antisymm backward forward

/-- The actual production result with complete checked profile agreement.
    This is an output of the classifier, not an input correctness certificate. -/
structure TerminalCandidateFullProfileGain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) where
  implementation : Implementation inputs outputs
  physicalFoundAt :
    findTerminalCandidatePhysicalGain candidate model = some implementation
  profileEqual : ∀ coordinate,
    model.profileSystem.observe implementation coordinate =
      model.profileSystem.observe candidate.toImplementation coordinate

/-- Reuse the already proved physical semantics and the computed full-profile
    check to construct the existing full-carrier interface. -/
def TerminalCandidateFullProfileGain.fullRealization
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (gain : TerminalCandidateFullProfileGain candidate model) :
    TerminalFullCarrierRealization model.profileSystem candidate.toImplementation :=
  { realization :=
      { implementation := gain.implementation
        equivalent := by
          obtain ⟨found, foundAt, governed, proper, positive, same,
            equivalent, size, slack, smaller, descent⟩ :=
            findTerminalCandidatePhysicalGain_sound candidate model
              gain.implementation gain.physicalFoundAt
          exact equivalent }
    profileEqual := gain.profileEqual }

/-- The three distinct observable outcomes of the full-mode gain boundary. -/
inductive TerminalGainProfileTag where
  | noPhysicalGain
  | profileMismatch
  | accepted
  deriving Repr, DecidableEq

/-- Every outcome retains its provenance in the actual physical search.
    A profile failure is data to route, not an already proved global route. -/
inductive TerminalCandidateGainProfileOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) where
  | noPhysicalGain
      (noneAt : findTerminalCandidatePhysicalGain candidate model = none)
  | profileMismatch (replacement : Implementation inputs outputs)
      (foundAt : findTerminalCandidatePhysicalGain candidate model = some replacement)
      (coordinate : Fin profileWidth)
      (mismatchAt : firstTerminalGainProfileMismatch model.profileSystem
        candidate.toImplementation replacement = some coordinate)
  | accepted (gain : TerminalCandidateFullProfileGain candidate model)

/-- Read the outcome tag without erasing its proof-bearing payload. -/
def TerminalCandidateGainProfileOutcome.tag
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate} :
    TerminalCandidateGainProfileOutcome candidate model → TerminalGainProfileTag
  | .noPhysicalGain _ => .noPhysicalGain
  | .profileMismatch _ _ _ _ => .profileMismatch
  | .accepted _ => .accepted

/-- Classify the exact existing physical result, checking every full-profile
    coordinate once and accepting no supplied result or correctness premise. -/
def classifyTerminalCandidateGainProfile
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    TerminalCandidateGainProfileOutcome candidate model :=
  match foundAt : findTerminalCandidatePhysicalGain candidate model with
  | none => .noPhysicalGain foundAt
  | some replacement =>
      match mismatchAt : firstTerminalGainProfileMismatch model.profileSystem
          candidate.toImplementation replacement with
      | some coordinate => .profileMismatch replacement foundAt coordinate mismatchAt
      | none => .accepted
          { implementation := replacement
            physicalFoundAt := foundAt
            profileEqual :=
              (firstTerminalGainProfileMismatch_eq_none_iff
                model.profileSystem candidate.toImplementation replacement).mp mismatchAt }


private theorem classifyTerminalCandidateGainProfile_tag_eq
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag =
      match findTerminalCandidatePhysicalGain candidate model with
      | none => TerminalGainProfileTag.noPhysicalGain
      | some replacement =>
          match firstTerminalGainProfileMismatch model.profileSystem
              candidate.toImplementation replacement with
          | none => TerminalGainProfileTag.accepted
          | some _ => TerminalGainProfileTag.profileMismatch := by
  unfold classifyTerminalCandidateGainProfile
  split
  next noneAt =>
    simp only [TerminalCandidateGainProfileOutcome.tag, noneAt]
  next replacement foundAt =>
    split
    next coordinate mismatchAt =>
      simp only [TerminalCandidateGainProfileOutcome.tag, foundAt, mismatchAt]
    next mismatchAt =>
      simp only [TerminalCandidateGainProfileOutcome.tag, foundAt, mismatchAt]

/-- Full-mode acceptance is exactly an actual physical gain whose complete
    profile agrees. Quotient projection plays no role in the acceptance test. -/
theorem classifyTerminalCandidateGainProfile_accepted_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag = .accepted ↔
      ∃ replacement : Implementation inputs outputs,
        findTerminalCandidatePhysicalGain candidate model = some replacement ∧
        ∀ coordinate, model.profileSystem.observe replacement coordinate =
          model.profileSystem.observe candidate.toImplementation coordinate := by
  rw [classifyTerminalCandidateGainProfile_tag_eq]
  cases foundAt : findTerminalCandidatePhysicalGain candidate model with
  | none =>
      constructor
      · intro accepted
        cases accepted
      · rintro ⟨replacement, impossible, _⟩
        cases impossible
  | some replacement =>
      dsimp only
      cases mismatchAt : firstTerminalGainProfileMismatch model.profileSystem
          candidate.toImplementation replacement with
      | none =>
          constructor
          · intro _accepted
            exact ⟨replacement, rfl,
              (firstTerminalGainProfileMismatch_eq_none_iff
                model.profileSystem candidate.toImplementation replacement).mp mismatchAt⟩
          · intro _matching
            rfl
      | some coordinate =>
          constructor
          · intro accepted
            cases accepted
          · rintro ⟨other, same, equal⟩
            have sameResult := Option.some.inj same
            subst other
            have stopped := (firstTerminalGainProfileMismatch_eq_none_iff
              model.profileSystem candidate.toImplementation replacement).mpr equal
            rw [mismatchAt] at stopped
            cases stopped

/-- No-gain is precisely failure of the unchanged production search. It does
    not mean that every whole-circuit or full-profile gain is absent. -/
theorem classifyTerminalCandidateGainProfile_noGain_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag = .noPhysicalGain ↔
      findTerminalCandidatePhysicalGain candidate model = none := by
  rw [classifyTerminalCandidateGainProfile_tag_eq]
  cases foundAt : findTerminalCandidatePhysicalGain candidate model with
  | none =>
      constructor
      · intro _tag
        rfl
      · intro _none
        rfl
  | some replacement =>
      dsimp only
      constructor
      · intro tag
        cases mismatchAt : firstTerminalGainProfileMismatch model.profileSystem
            candidate.toImplementation replacement with
        | none =>
            rw [mismatchAt] at tag
            cases tag
        | some coordinate =>
            rw [mismatchAt] at tag
            cases tag
      · intro impossible
        cases impossible

/-- Profile rejection is exactly a mismatch in the actual returned physical
    result. The separate scan theorem supplies the complete agreeing prefix. -/
theorem classifyTerminalCandidateGainProfile_mismatch_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag = .profileMismatch ↔
      ∃ (replacement : Implementation inputs outputs) (coordinate : Fin profileWidth),
        findTerminalCandidatePhysicalGain candidate model = some replacement ∧
        firstTerminalGainProfileMismatch model.profileSystem
          candidate.toImplementation replacement = some coordinate := by
  rw [classifyTerminalCandidateGainProfile_tag_eq]
  cases foundAt : findTerminalCandidatePhysicalGain candidate model with
  | none =>
      constructor
      · intro tag
        cases tag
      · rintro ⟨replacement, coordinate, impossible, _⟩
        cases impossible
  | some replacement =>
      dsimp only
      cases mismatchAt : firstTerminalGainProfileMismatch model.profileSystem
          candidate.toImplementation replacement with
      | none =>
          constructor
          · intro tag
            cases tag
          · rintro ⟨other, coordinate, same, mismatched⟩
            have sameResult := Option.some.inj same
            subst other
            rw [mismatchAt] at mismatched
            cases mismatched
      | some coordinate =>
          constructor
          · intro _tag
            exact ⟨replacement, coordinate, rfl, mismatchAt⟩
          · intro _mismatched
            rfl

private theorem gainProfile_slack_balance (remaining whole minimum gain : Nat)
    (within : minimum ≤ remaining) (size : remaining + gain = whole) :
    (remaining - minimum) + gain = whole - minimum := by
  have wholeWithin : minimum ≤ whole :=
    Nat.le_trans within (Nat.le.intro size)
  have balanced : ((remaining - minimum) + gain) + minimum =
      (whole - minimum) + minimum := by
    calc
      ((remaining - minimum) + gain) + minimum =
          ((remaining - minimum) + minimum) + gain := Nat.add_right_comm _ _ _
      _ = remaining + gain := by rw [Nat.sub_add_cancel within]
      _ = whole := size
      _ = (whole - minimum) + minimum := (Nat.sub_add_cancel wholeWithin).symm
  exact Nat.add_right_cancel balanced

/-- Every accepted computed result decreases the full-profile slack by the
    exact gain of its actually selected proper positive support. Full-profile
    minima are transported, not equated with Boolean-only minima. -/
theorem TerminalCandidateFullProfileGain.fullSlack_gain
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (gain : TerminalCandidateFullProfileGain candidate model) :
    ∃ found : TerminalCandidateProperPositiveSupport candidate model,
      findTerminalCandidateProperPositiveSupport candidate model = some found ∧
      (gain.implementation.gateCount -
          terminalFullProfileMinimum model.profileSystem gain.implementation) +
          terminalSupportLocalGain candidate
            (terminalCandidateSaturationSystem candidate model) found.seed =
        gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation ∧
      gain.implementation.gateCount -
          terminalFullProfileMinimum model.profileSystem gain.implementation <
        gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation := by
  obtain ⟨found, foundAt, governed, proper, positive, same,
    equivalent, size, slack, smaller, descent⟩ :=
    findTerminalCandidatePhysicalGain_sound candidate model
      gain.implementation gain.physicalFoundAt
  have minima := terminalFullProfileMinimum_eq_of_fullRealization gain.fullRealization
  change terminalFullProfileMinimum model.profileSystem gain.implementation =
    terminalFullProfileMinimum model.profileSystem candidate.toImplementation at minima
  have within := terminalFullProfileMinimum_le
    (terminalCurrentFullCarrierRealization model.profileSystem gain.implementation)
  change terminalFullProfileMinimum model.profileSystem gain.implementation ≤
    gain.implementation.gateCount at within
  rw [minima] at within
  have balanced :
      (gain.implementation.gateCount -
          terminalFullProfileMinimum model.profileSystem gain.implementation) +
          terminalSupportLocalGain candidate
            (terminalCandidateSaturationSystem candidate model) found.seed =
        gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation := by
    rw [minima]
    exact gainProfile_slack_balance _ _ _ _ within size
  refine ⟨found, foundAt, balanced, ?_⟩
  have grows := Nat.add_lt_add_left positive
    (gain.implementation.gateCount -
      terminalFullProfileMinimum model.profileSystem gain.implementation)
  simpa only [Nat.add_zero, balanced] using grows

end DirectWire
end PNP
