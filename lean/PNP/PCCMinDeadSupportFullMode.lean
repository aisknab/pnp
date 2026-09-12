/-
Copyright (c) 2026 PNP Labs.

Full finite-profile and obligation checks for the computed proper dead support.
The profile observation system remains input data, not a derived manuscript
carrier or a supplied correctness assertion. No global or runtime claim.
-/

import PNP.PCCMinDeadSupportContext
import PNP.ResidualTerminalGainProfileFirewall

namespace PNP
namespace DirectWire

private def terminalObligationOpen {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) (coordinate : Fin profileWidth) : Bool :=
  decide (system.role coordinate = .obligation) && system.observe current coordinate

private theorem terminalObligationOpen_iff {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) (coordinate : Fin profileWidth) :
    terminalObligationOpen system current coordinate = true ↔
      system.role coordinate = .obligation ∧ system.observe current coordinate = true := by
  unfold terminalObligationOpen
  rw [Bool.and_eq_true]
  constructor
  · intro checked
    exact ⟨of_decide_eq_true checked.1, checked.2⟩
  · intro opened
    exact ⟨decide_eq_true opened.1, opened.2⟩

private theorem terminalObligationClosed_of_not_open {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) (coordinate : Fin profileWidth)
    (notOpen : ¬ terminalObligationOpen system current coordinate = true)
    (role : system.role coordinate = .obligation) :
    system.observe current coordinate = false := by
  cases observed : system.observe current coordinate with
  | false => rfl
  | true =>
      exact False.elim (notOpen
        ((terminalObligationOpen_iff system current coordinate).mpr ⟨role, observed⟩))

/-- Scan every actual obligation-role coordinate in canonical order. True means
open, while non-obligation true coordinates are not rejected by this scan. -/
def firstTerminalOpenObligation {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) : Option (Fin profileWidth) :=
  (allFin profileWidth).find? (terminalObligationOpen system current)

/-- No reported obligation is exactly discharge of all observed obligation bits. -/
theorem firstTerminalOpenObligation_eq_none_iff {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    firstTerminalOpenObligation system current = none ↔ system.ObligationsDischarged current := by
  unfold firstTerminalOpenObligation
  constructor
  · intro stopped coordinate role
    exact terminalObligationClosed_of_not_open system current coordinate
      ((List.find?_eq_none.mp stopped) coordinate (mem_allFin coordinate)) role
  · intro discharged
    apply List.find?_eq_none.mpr
    intro coordinate _member opened
    obtain ⟨role, on⟩ := (terminalObligationOpen_iff system current coordinate).mp opened
    have off := discharged coordinate role
    rw [off] at on
    exact Bool.noConfusion on

/-- A reported open obligation comes with the complete preceding closed-obligation
prefix. The role and value are read from the actual supplied observation system. -/
theorem firstTerminalOpenObligation_spec {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) (coordinate : Fin profileWidth)
    (foundAt : firstTerminalOpenObligation system current = some coordinate) :
    system.role coordinate = .obligation ∧ system.observe current coordinate = true ∧
      ∃ before after : List (Fin profileWidth),
        allFin profileWidth = before ++ coordinate :: after ∧
        ∀ earlier, earlier ∈ before → system.role earlier = .obligation →
          system.observe current earlier = false := by
  obtain ⟨opened, before, after, partition, closedPrefix⟩ :=
    List.find?_eq_some_iff_append.mp foundAt
  obtain ⟨role, on⟩ := (terminalObligationOpen_iff system current coordinate).mp opened
  refine ⟨role, on, before, after, partition, ?_⟩
  intro earlier member earlierRole
  apply terminalObligationClosed_of_not_open system current earlier _ earlierRole
  intro openEarlier
  have prior := closedPrefix earlier member
  rw [openEarlier] at prior
  exact Bool.noConfusion prior

/-- Checked finite full-mode data for this computed physical replacement.
The classifier constructs these proof fields; none is a caller input. -/
structure DeadSupportFullModeGain {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) : Type where
  physical : DeadSupportPhysicalGain current
  physicalFoundAt : deadSupportProperGain current = some physical
  profileEqual : ∀ coordinate,
    system.observe (deadSupportReplacementImplementation current) coordinate =
      system.observe current coordinate
  obligationsDischarged : system.ObligationsDischarged (deadSupportReplacementImplementation current)

/-- Reuse the existing full-carrier interface without repeating a semantic search. -/
def DeadSupportFullModeGain.fullRealization {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (gain : DeadSupportFullModeGain system current) : TerminalFullCarrierRealization system current :=
  { realization :=
      { implementation := deadSupportReplacementImplementation current
        equivalent := deadSupportReplacement_equivalent current }
    profileEqual := gain.profileEqual }

/-- Profile equality and checked replacement discharge also discharge the current
implementation's observed obligations; open bits are not silently erased. -/
theorem DeadSupportFullModeGain.currentObligationsDischarged {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (gain : DeadSupportFullModeGain system current) : system.ObligationsDischarged current := by
  intro coordinate role
  rw [← gain.profileEqual coordinate]
  exact gain.obligationsDischarged coordinate role

/-- Distinct physical, full-profile, obligation and accepted outcomes. -/
inductive DeadSupportFullModeTag where
  | noProperSupport
  | profileMismatch
  | openObligation
  | accepted
  deriving Repr, DecidableEq

/-- Rejections retain the exact computed cause, not an invented completed route. -/
inductive DeadSupportFullModeOutcome {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) where
  | noProperSupport (noneAt : deadSupportProperGain current = none)
  | profileMismatch (physical : DeadSupportPhysicalGain current)
      (physicalAt : deadSupportProperGain current = some physical)
      (coordinate : Fin profileWidth)
      (mismatchAt : firstTerminalGainProfileMismatch system current
        (deadSupportReplacementImplementation current) = some coordinate)
  | openObligation (physical : DeadSupportPhysicalGain current)
      (physicalAt : deadSupportProperGain current = some physical)
      (profileAt : firstTerminalGainProfileMismatch system current
        (deadSupportReplacementImplementation current) = none)
      (coordinate : Fin profileWidth)
      (openAt : firstTerminalOpenObligation system
        (deadSupportReplacementImplementation current) = some coordinate)
  | accepted (gain : DeadSupportFullModeGain system current)

/-- Read the outcome without losing the proof-bearing payload at its origin. -/
def DeadSupportFullModeOutcome.tag {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs} :
    DeadSupportFullModeOutcome system current → DeadSupportFullModeTag
  | .noProperSupport _ => .noProperSupport
  | .profileMismatch _ _ _ _ => .profileMismatch
  | .openObligation _ _ _ _ _ => .openObligation
  | .accepted _ => .accepted

/-- Classify only the actual M245 replacement. Every full-profile coordinate is
checked, followed by all obligation roles. No projection, minimum or supplied
correctness certificate participates in execution. -/
def classifyDeadSupportFullMode {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) : DeadSupportFullModeOutcome system current :=
  match physicalAt : deadSupportProperGain current with
  | none => .noProperSupport physicalAt
  | some physical =>
      match profileAt : firstTerminalGainProfileMismatch system current
          (deadSupportReplacementImplementation current) with
      | some coordinate => .profileMismatch physical physicalAt coordinate profileAt
      | none =>
          match openAt : firstTerminalOpenObligation system
              (deadSupportReplacementImplementation current) with
          | some coordinate => .openObligation physical physicalAt profileAt coordinate openAt
          | none => .accepted
              { physical := physical
                physicalFoundAt := physicalAt
                profileEqual := (firstTerminalGainProfileMismatch_eq_none_iff system current
                  (deadSupportReplacementImplementation current)).mp profileAt
                obligationsDischarged := (firstTerminalOpenObligation_eq_none_iff system
                  (deadSupportReplacementImplementation current)).mp openAt }

private theorem classifyDeadSupportFullMode_tag_eq {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (classifyDeadSupportFullMode system current).tag =
      match deadSupportProperGain current with
      | none => DeadSupportFullModeTag.noProperSupport
      | some _ =>
          match firstTerminalGainProfileMismatch system current
              (deadSupportReplacementImplementation current) with
          | some _ => DeadSupportFullModeTag.profileMismatch
          | none =>
              match firstTerminalOpenObligation system
                  (deadSupportReplacementImplementation current) with
              | some _ => DeadSupportFullModeTag.openObligation
              | none => DeadSupportFullModeTag.accepted := by
  unfold classifyDeadSupportFullMode
  split
  next physicalAt =>
    simp only [DeadSupportFullModeOutcome.tag, physicalAt]
  next physical physicalAt =>
    split
    next coordinate profileAt =>
      simp only [DeadSupportFullModeOutcome.tag, physicalAt, profileAt]
    next profileAt =>
      split
      next coordinate openAt =>
        simp only [DeadSupportFullModeOutcome.tag, physicalAt, profileAt, openAt]
      next openAt =>
        simp only [DeadSupportFullModeOutcome.tag, physicalAt, profileAt, openAt]

/-- Acceptance is exactly computed properness, complete profile equality and
discharge of all observed obligation bits. None is replaced by a quotient check. -/
theorem classifyDeadSupportFullMode_accepted_iff {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (classifyDeadSupportFullMode system current).tag = .accepted ↔
      (deadSupportProperGain current).isSome = true ∧
      (∀ coordinate, system.observe (deadSupportReplacementImplementation current) coordinate =
        system.observe current coordinate) ∧
      system.ObligationsDischarged (deadSupportReplacementImplementation current) := by
  rw [classifyDeadSupportFullMode_tag_eq]
  cases physicalAt : deadSupportProperGain current with
  | none =>
      constructor
      · intro impossible
        cases impossible
      · intro success
        exact Bool.noConfusion success.1
  | some physical =>
      cases profileAt : firstTerminalGainProfileMismatch system current
          (deadSupportReplacementImplementation current) with
      | some coordinate =>
          constructor
          · intro impossible
            cases impossible
          · intro success
            have noMismatch := (firstTerminalGainProfileMismatch_eq_none_iff system current
              (deadSupportReplacementImplementation current)).mpr success.2.1
            rw [profileAt] at noMismatch
            cases noMismatch
      | none =>
          cases openAt : firstTerminalOpenObligation system
              (deadSupportReplacementImplementation current) with
          | some coordinate =>
              constructor
              · intro impossible
                cases impossible
              · intro success
                have noOpen := (firstTerminalOpenObligation_eq_none_iff system
                  (deadSupportReplacementImplementation current)).mpr success.2.2
                rw [openAt] at noOpen
                cases noOpen
          | none =>
              constructor
              · intro _accepted
                exact ⟨rfl,
                  (firstTerminalGainProfileMismatch_eq_none_iff system current
                    (deadSupportReplacementImplementation current)).mp profileAt,
                  (firstTerminalOpenObligation_eq_none_iff system
                    (deadSupportReplacementImplementation current)).mp openAt⟩
              · intro _success
                rfl

/-- No-proper-support means exactly rejection by the computed M245 recognizer,
not absence of every physical or semantic gain. -/
theorem classifyDeadSupportFullMode_noProperSupport_iff {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    (classifyDeadSupportFullMode system current).tag = .noProperSupport ↔
      deadSupportProperGain current = none := by
  rw [classifyDeadSupportFullMode_tag_eq]
  cases physicalAt : deadSupportProperGain current with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some physical =>
      cases profileAt : firstTerminalGainProfileMismatch system current
          (deadSupportReplacementImplementation current) with
      | some coordinate => constructor <;> intro impossible <;> cases impossible
      | none =>
          cases openAt : firstTerminalOpenObligation system
              (deadSupportReplacementImplementation current) with
          | some coordinate => constructor <;> intro impossible <;> cases impossible
          | none => constructor <;> intro impossible <;> cases impossible

/-- Accepted full-mode data preserve the full-profile reference minimum.
This is a specification theorem, not an executed minimization procedure. -/
theorem DeadSupportFullModeGain.fullProfileMinimum {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) :
    terminalFullProfileMinimum system (deadSupportReplacementImplementation current) =
      terminalFullProfileMinimum system current :=
  terminalFullProfileMinimum_eq_of_fullRealization gain.fullRealization

/-- Every accepted record carries proper physical support, complete semantics,
full-profile equality, closed observed obligations and exact positive savings. -/
theorem DeadSupportFullModeGain.checked {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) :
    0 < deadSupportGateCount current ∧
      deadSupportGateCount current < current.gateCount ∧
      Equivalent (deadSupportReplacementImplementation current).candidate.program
        (deadSupportReplacementImplementation current).candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      (∀ coordinate, system.observe (deadSupportReplacementImplementation current) coordinate =
        system.observe current coordinate) ∧
      system.ObligationsDischarged current ∧
      system.ObligationsDischarged (deadSupportReplacementImplementation current) ∧
      (deadSupportReplacementImplementation current).gateCount + deadSupportGateCount current =
        current.gateCount ∧
      residualSlack current = residualSlack (deadSupportReplacementImplementation current) +
        deadSupportGateCount current ∧
      StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧
      residualSlack (deadSupportReplacementImplementation current) < residualSlack current :=
  ⟨gain.physical.supportNonempty, gain.physical.supportProper,
    deadSupportReplacement_equivalent current, gain.profileEqual,
    gain.currentObligationsDischarged, gain.obligationsDischarged,
    deadSupportReplacement_accounting current, deadSupportReplacement_residualSlack current,
    gain.physical.gain, gain.physical.gain.strictResidualDescent⟩

/-- Every classifier branch reports its actual checked boundary, with the first
failure's canonical prefix. Rejection never becomes a fabricated completed route. -/
theorem classifyDeadSupportFullMode_checked {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current : Implementation inputs outputs) :
    match classifyDeadSupportFullMode system current with
    | .noProperSupport _ => deadSupportProperGain current = none
    | .profileMismatch _ _ coordinate _ =>
        system.observe (deadSupportReplacementImplementation current) coordinate ≠
          system.observe current coordinate ∧
        ∃ before after : List (Fin profileWidth),
          allFin profileWidth = before ++ coordinate :: after ∧
          ∀ earlier, earlier ∈ before →
            system.observe (deadSupportReplacementImplementation current) earlier =
              system.observe current earlier
    | .openObligation _ _ _ coordinate _ =>
        (∀ index, system.observe (deadSupportReplacementImplementation current) index =
          system.observe current index) ∧
        system.role coordinate = .obligation ∧
        system.observe (deadSupportReplacementImplementation current) coordinate = true ∧
        ∃ before after : List (Fin profileWidth),
          allFin profileWidth = before ++ coordinate :: after ∧
          ∀ earlier, earlier ∈ before → system.role earlier = .obligation →
            system.observe (deadSupportReplacementImplementation current) earlier = false
    | .accepted _ =>
        system.ObligationsDischarged current ∧
        system.ObligationsDischarged (deadSupportReplacementImplementation current) ∧
        StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧
        residualSlack (deadSupportReplacementImplementation current) < residualSlack current := by
  cases outcome : classifyDeadSupportFullMode system current with
  | noProperSupport noneAt => exact noneAt
  | profileMismatch physical physicalAt coordinate mismatchAt =>
      exact firstTerminalGainProfileMismatch_spec system current
        (deadSupportReplacementImplementation current) coordinate mismatchAt
  | openObligation physical physicalAt profileAt coordinate openAt =>
      exact ⟨(firstTerminalGainProfileMismatch_eq_none_iff system current
          (deadSupportReplacementImplementation current)).mp profileAt,
        firstTerminalOpenObligation_spec system
          (deadSupportReplacementImplementation current) coordinate openAt⟩
  | accepted gain =>
      exact ⟨gain.currentObligationsDischarged, gain.obligationsDischarged,
        gain.physical.gain, gain.physical.gain.strictResidualDescent⟩

end DirectWire
end PNP
