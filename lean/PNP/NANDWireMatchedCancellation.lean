/-
Copyright (c) 2026 PNP Labs.

Compute retained representatives of forgotten computational wires from actual
original source identity. Full values come from the precise local quotient
agreement, never from masked padding or a supplied global witness.

This is a computational R6 cancellation component, not the complete manuscript
carrier, arbitrary cancellation calculus, Package E, ZeroSlack or polynomial
PCCMin.
-/

import PNP.NANDWireQuotientLift

namespace PNP.DirectWire.WireMatchedCancellation

variable {inputs outputs fields : Nat}

/-- Ordinary observations and kept fields are visible; forgotten padding is not. -/
def visibility (keep : Fin fields → Bool) : Fin (outputs + fields) → Bool :=
  splitFin (fun _ : Fin outputs => true) keep

/-- A literal original-source match at an actually retained observation. -/
structure Representative (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) : Type where
  observation : Fin (outputs + fields)
  visible : visibility keep observation = true
  sourceExact : carrier.exposed.candidate.directWireWord.source observation =
    carrier.source field

/-- Canonical first-match scan of actual original sources, without a semantic oracle. -/
def scan (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    List (Fin (outputs + fields)) → Option (Representative carrier keep field)
  | [] => none
  | observation :: remaining =>
      if eligible : visibility keep observation = true ∧
          carrier.exposed.candidate.directWireWord.source observation = carrier.source field then
        some ⟨observation, eligible.1, eligible.2⟩
      else scan carrier keep field remaining

/-- Compute the representative from all actual observations, not an input list. -/
def representative (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    Option (Representative carrier keep field) :=
  scan carrier keep field (allFin (outputs + fields))

private theorem scan_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields)
    (observations : List (Fin (outputs + fields))) :
    (scan carrier keep field observations).isSome = true ↔
      ∃ observation, observation ∈ observations ∧
        visibility keep observation = true ∧
        carrier.exposed.candidate.directWireWord.source observation = carrier.source field := by
  induction observations with
  | nil =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨observation, member, _visible, _same⟩
        exact (List.not_mem_nil member).elim
  | cons observation remaining ih =>
      unfold scan
      split
      next eligible =>
        exact ⟨fun _accepted =>
          ⟨observation, List.mem_cons_self, eligible.1, eligible.2⟩, fun _found => rfl⟩
      next notEligible =>
        constructor
        · intro accepted
          obtain ⟨other, member, retained, same⟩ := ih.1 accepted
          exact ⟨other, List.mem_cons_of_mem observation member, retained, same⟩
        · rintro ⟨other, member, retained, same⟩
          rcases List.mem_cons.mp member with atHead | inTail
          · subst other
            exact (notEligible ⟨retained, same⟩).elim
          · exact ih.2 ⟨other, inTail, retained, same⟩

theorem representative_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    (representative carrier keep field).isSome = true ↔
      ∃ observation, visibility keep observation = true ∧
        carrier.exposed.candidate.directWireWord.source observation = carrier.source field := by
  constructor
  · intro accepted
    obtain ⟨observation, _member, retained, same⟩ :=
      (scan_isSome_iff carrier keep field _).1 accepted
    exact ⟨observation, retained, same⟩
  · rintro ⟨observation, retained, same⟩
    exact (scan_isSome_iff carrier keep field _).2
      ⟨observation, mem_allFin observation, retained, same⟩

/-- Local quotient agreement gives the full value of a genuinely retained observation. -/
theorem observation_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (observation : Fin (outputs + fields))
    (retained : visibility keep observation = true) (valuation : Valuation inputs) :
    replacement.exposed.candidate.semantics valuation observation =
      carrier.exposed.candidate.semantics valuation observation := by
  rcases finSum_decompose observation with ⟨output, rfl⟩ | ⟨field, rfl⟩
  · rw [replacement.exposed_output, carrier.exposed_output]
    exact (same.output valuation output).trans
      (WireObligationRestoration.projected_output carrier keep valuation output)
  · have kept : keep field = true := by
      change splitFin (fun _ : Fin outputs => true) keep (Fin.natAdd outputs field) = true
        at retained
      rw [splitFin_right] at retained
      exact retained
    rw [replacement.exposed_field, carrier.exposed_field]
    exact (same.keptField valuation field kept).trans
      (WireObligationRestoration.projected_kept_field carrier keep valuation field kept)

/-- Source identity upgrades the retained observation to the forgotten full value. -/
theorem Representative.full_value {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {field : Fin fields}
    (alias : Representative carrier keep field)
    (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) :
    replacement.exposed.candidate.semantics valuation alias.observation =
      carrier.fieldValue valuation field := by
  apply (observation_value carrier keep replacement same alias.observation
    alias.visible valuation).trans
  change (carrier.exposed.candidate.directWireWord.source alias.observation).eval
    valuation (carrier.implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation field
  rw [alias.sourceExact]
  rfl

/-- Kept fields and source-matched forgotten fields need no separate materializer. -/
def resolved (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) : Bool :=
  keep field || (representative carrier keep field).isSome

def allResolved (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Bool :=
  (allFin fields).all (resolved carrier keep)

theorem allResolved_sound (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (complete : allResolved carrier keep = true)
    (field : Fin fields) : resolved carrier keep field = true :=
  (List.all_eq_true.mp complete) field (mem_allFin field)

/-- No hidden program is needed when every field is already represented. -/
def zeroMissing (inputs fields : Nat) : WireCarrier inputs 0 fields :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program inputs 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant false }

/-- Materialize unresolved original wires once, with an explicit empty case. -/
def missing (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs 0 fields :=
  if allResolved carrier keep then zeroMissing inputs fields
  else WireObligationRestoration.materializer carrier (resolved carrier keep)

def charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  (missing carrier keep).implementation.gateCount

theorem charge_allResolved (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (complete : allResolved carrier keep = true) :
    charge carrier keep = 0 := by
  unfold charge missing
  rw [complete]
  rfl

theorem missing_unresolved_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields)
    (unresolved : resolved carrier keep field = false) (valuation : Valuation inputs) :
    (missing carrier keep).fieldValue valuation field = carrier.fieldValue valuation field := by
  have incomplete : allResolved carrier keep = false := by
    cases state : allResolved carrier keep with
    | false => rfl
    | true =>
        have impossible := allResolved_sound carrier keep state field
        rw [unresolved] at impossible
        cases impossible
  unfold missing
  rw [incomplete]
  exact WireObligationRestoration.materializer_forgotten_field
    carrier (resolved carrier keep) valuation field unresolved

/-- A gate-count bound only; it is not an encoded-size execution theorem. -/
theorem charge_bound (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    charge carrier keep ≤ carrier.implementation.gateCount := by
  cases complete : allResolved carrier keep with
  | true =>
      rw [charge_allResolved carrier keep complete]
      exact Nat.zero_le _
  | false =>
      unfold charge missing
      rw [complete]
      exact Nat.le.intro
        ((WireObligationRestoration.hidden carrier (resolved carrier keep)).normalize_exact_accounting)

/-- Reuse actual replacement observations; unresolved padding is not a witness. -/
def visibleReplacement (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) :
    WireCarrier inputs outputs fields :=
  { implementation := replacement.implementation
    source := fun field =>
      if keep field then replacement.source field
      else match representative carrier keep field with
        | none => .constant false
        | some alias => replacement.exposed.candidate.directWireWord.source alias.observation }

private theorem visibleReplacement_source (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (field : Fin fields) :
    (visibleReplacement carrier keep replacement).source field =
      if keep field then replacement.source field
      else match representative carrier keep field with
        | none => .constant false
        | some alias => replacement.exposed.candidate.directWireWord.source alias.observation := rfl

theorem visible_resolved_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (field : Fin fields) (represented : resolved carrier keep field = true)
    (valuation : Valuation inputs) :
    (visibleReplacement carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  cases kept : keep field with
  | true =>
      change ((visibleReplacement carrier keep replacement).source field).eval valuation
        (replacement.implementation.candidate.program.eval valuation) = _
      rw [visibleReplacement_source, kept]
      exact (same.keptField valuation field kept).trans
        (WireObligationRestoration.projected_kept_field carrier keep valuation field kept)
  | false =>
      cases found : representative carrier keep field with
      | none =>
          unfold resolved at represented
          rw [kept, found] at represented
          cases represented
      | some alias =>
          change ((visibleReplacement carrier keep replacement).source field).eval valuation
            (replacement.implementation.candidate.program.eval valuation) = _
          rw [visibleReplacement_source, kept, found]
          exact alias.full_value replacement same valuation

/-- Complete the replacement with just the computed unresolved materializer. -/
def expanded (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) :
    WireCarrier inputs outputs fields :=
  WireObligationRestoration.join (visibleReplacement carrier keep replacement)
    (missing carrier keep) (resolved carrier keep)

theorem expanded_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) :
    (expanded carrier keep replacement).implementation.gateCount =
      replacement.implementation.gateCount + charge carrier keep := rfl

theorem expanded_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (expanded carrier keep replacement).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  (WireObligationRestoration.join_output (visibleReplacement carrier keep replacement)
    (missing carrier keep) (resolved carrier keep) valuation output).trans
      ((same.output valuation output).trans
        (WireObligationRestoration.projected_output carrier keep valuation output))

theorem expanded_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  cases represented : resolved carrier keep field with
  | true =>
      exact (WireObligationRestoration.join_kept_field
        (visibleReplacement carrier keep replacement) (missing carrier keep)
        (resolved carrier keep) valuation field represented).trans
          (visible_resolved_field carrier keep replacement same field represented valuation)
  | false =>
      exact (WireObligationRestoration.join_forgotten_field
        (visibleReplacement carrier keep replacement) (missing carrier keep)
        (resolved carrier keep) valuation field represented).trans
          (missing_unresolved_field carrier keep field represented valuation)

theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    Equivalent (expanded carrier keep replacement).implementation.candidate.program
      (expanded carrier keep replacement).implementation.candidate.directWireWord
      carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord :=
  expanded_output carrier keep replacement same

/-- A computed original-source match and the actual expanded full-value witness. -/
structure R6Discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep) where
  alias : Representative carrier keep creation.coordinate
  aliasExact : representative carrier keep creation.coordinate = some alias
  actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount
  sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate
  fullWitness : ∀ valuation,
    actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

/-- Unmatched lost wires retain their actual materializer and full-value witness. -/
structure R8Discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep) where
  unrepresented : representative carrier keep creation.coordinate = none
  unresolved : resolved carrier keep creation.coordinate = false
  actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount
  sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate
  fullWitness : ∀ valuation,
    actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

inductive Discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep)
  | r6 (witness : R6Discharge carrier keep replacement creation)
  | r8 (witness : R8Discharge carrier keep replacement creation)

private theorem constructed_full_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    ((expanded carrier keep replacement).source creation.coordinate).eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation) := by
  rw [creation.sourceExact]
  exact expanded_field carrier keep replacement same valuation creation.coordinate

/-- Select R6 only from the computed full source match; otherwise pay R8. -/
def discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    Discharge carrier keep replacement creation :=
  match found : representative carrier keep creation.coordinate with
  | some alias =>
      .r6 { alias := alias, aliasExact := found
            actualSource := (expanded carrier keep replacement).source creation.coordinate
            sourceExact := rfl
            fullWitness := constructed_full_value carrier keep replacement same creation }
  | none =>
      .r8 { unrepresented := found
            unresolved := by
              unfold resolved
              rw [creation.forgotten, found]
              rfl
            actualSource := (expanded carrier keep replacement).source creation.coordinate
            sourceExact := rfl
            fullWitness := constructed_full_value carrier keep replacement same creation }

def Discharge.actualSource {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    {creation : WireObligationRestoration.R5Creation carrier keep} :
    Discharge carrier keep replacement creation →
      Source inputs (expanded carrier keep replacement).implementation.gateCount
  | .r6 witness => witness.actualSource
  | .r8 witness => witness.actualSource

def Discharge.isR6 {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    {creation : WireObligationRestoration.R5Creation carrier keep} :
    Discharge carrier keep replacement creation → Bool
  | .r6 _ => true
  | .r8 _ => false

theorem Discharge.full_value {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    {creation : WireObligationRestoration.R5Creation carrier keep}
    (witness : Discharge carrier keep replacement creation) (valuation : Valuation inputs) :
    witness.actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate := by
  cases witness with
  | r6 witness =>
      have value := witness.fullWitness valuation
      rw [creation.sourceExact] at value
      exact value
  | r8 witness =>
      have value := witness.fullWitness valuation
      rw [creation.sourceExact] at value
      exact value

theorem discharge_source_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (discharge carrier keep replacement same creation).actualSource =
      (expanded carrier keep replacement).source creation.coordinate := by
  unfold discharge
  split <;> rfl

theorem discharge_isR6_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (discharge carrier keep replacement same creation).isR6 = true ↔
      (representative carrier keep creation.coordinate).isSome = true := by
  unfold discharge
  split
  next alias found =>
    change true = true ↔ (representative carrier keep creation.coordinate).isSome = true
    rw [found]
    rfl
  next found =>
    change false = true ↔ (representative carrier keep creation.coordinate).isSome = true
    rw [found]
    rfl

theorem discharge_full_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (discharge carrier keep replacement same creation).actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  (discharge carrier keep replacement same creation).full_value valuation

/-- This is a fully paid whole-word gain, not a proper-support certificate. -/
structure CheckedGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : Type where
  agreement : WireQuotientLift.QuotientAgreement carrier keep replacement
  smaller : (expanded carrier keep replacement).implementation.gateCount <
    carrier.implementation.gateCount

def checkedGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    Option (CheckedGain carrier keep replacement) :=
  if smaller : (expanded carrier keep replacement).implementation.gateCount <
      carrier.implementation.gateCount then some ⟨same, smaller⟩ else none

theorem checkedGain_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    (checkedGain carrier keep replacement same).isSome = true ↔
      replacement.implementation.gateCount + charge carrier keep <
        carrier.implementation.gateCount := by
  unfold checkedGain
  split
  next smaller =>
    constructor
    · intro _accepted
      exact (expanded_charge carrier keep replacement) ▸ smaller
    · intro _paid
      rfl
  next notSmaller =>
    constructor
    · intro impossible
      cases impossible
    · intro paid
      exact (notSmaller ((expanded_charge carrier keep replacement).symm ▸ paid)).elim

def CheckedGain.strictGain {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (gain : CheckedGain carrier keep replacement) :
    StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation where
  smaller := gain.smaller
  equivalent := expanded_equivalent carrier keep replacement gain.agreement

theorem CheckedGain.checked {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (gain : CheckedGain carrier keep replacement) :
    StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation ∧
      (∀ valuation field,
        (expanded carrier keep replacement).fieldValue valuation field =
          carrier.fieldValue valuation field) ∧
      (expanded carrier keep replacement).implementation.gateCount =
        replacement.implementation.gateCount + charge carrier keep :=
  ⟨gain.strictGain, expanded_field carrier keep replacement gain.agreement,
    expanded_charge carrier keep replacement⟩

/-- Only R5 creates identities; discharges carry either full R6 or full R8 evidence. -/
inductive Event (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
  | createR5 (creation : WireObligationRestoration.R5Creation carrier keep)
  | discharge (creation : WireObligationRestoration.R5Creation carrier keep)
      (witness : Discharge carrier keep replacement creation)

def eventsFor (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    List (Fin fields) → List (Event carrier keep replacement)
  | [] => []
  | field :: remaining =>
      if forgotten : keep field = false then
        let creation := WireObligationRestoration.createR5 carrier keep field forgotten
        .createR5 creation :: .discharge creation (discharge carrier keep replacement same creation) ::
          eventsFor carrier keep replacement same remaining
      else eventsFor carrier keep replacement same remaining

def events (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    List (Event carrier keep replacement) :=
  eventsFor carrier keep replacement same (List.finRange fields)

def createdCoordinates {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields} :
    List (Event carrier keep replacement) → List (Fin fields)
  | [] => []
  | .createR5 creation :: remaining => creation.coordinate :: createdCoordinates remaining
  | .discharge _ _ :: remaining => createdCoordinates remaining

def dischargedCoordinates {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields} :
    List (Event carrier keep replacement) → List (Fin fields)
  | [] => []
  | .createR5 _ :: remaining => dischargedCoordinates remaining
  | .discharge creation _ :: remaining => creation.coordinate :: dischargedCoordinates remaining

private def replayPending {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (pending : List (Fin fields)) :
    List (Event carrier keep replacement) → Option (List (Fin fields))
  | [] => some pending
  | .createR5 creation :: remaining =>
      if creation.coordinate ∈ pending then none
      else replayPending (creation.coordinate :: pending) remaining
  | .discharge creation _ :: remaining =>
      match pending with
      | [] => none
      | first :: rest =>
          if first = creation.coordinate then replayPending rest remaining else none

/-- A closed identity cannot be created again later. Validate the whole trace. -/
def replay {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (pending : List (Fin fields)) (transcript : List (Event carrier keep replacement)) :
    Option (List (Fin fields)) :=
  if (pending ++ createdCoordinates transcript).Nodup then
    replayPending pending transcript
  else none

private theorem createdCoordinates_eventsFor (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (coordinates : List (Fin fields)) :
    createdCoordinates (eventsFor carrier keep replacement same coordinates) =
      coordinates.filter (fun field => !(keep field)) := by
  induction coordinates with
  | nil => rfl
  | cons field remaining ih =>
      cases kept : keep field <;>
        simp [eventsFor, kept, createdCoordinates, WireObligationRestoration.createR5, ih]

private theorem dischargedCoordinates_eventsFor (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (coordinates : List (Fin fields)) :
    dischargedCoordinates (eventsFor carrier keep replacement same coordinates) =
      coordinates.filter (fun field => !(keep field)) := by
  induction coordinates with
  | nil => rfl
  | cons field remaining ih =>
      cases kept : keep field <;>
        simp [eventsFor, kept, dischargedCoordinates, WireObligationRestoration.createR5, ih]

theorem created_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    createdCoordinates (events carrier keep replacement same) =
      WireObligationRestoration.forgottenCoordinates keep :=
  createdCoordinates_eventsFor carrier keep replacement same (List.finRange fields)

theorem discharged_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    dischargedCoordinates (events carrier keep replacement same) =
      WireObligationRestoration.forgottenCoordinates keep :=
  dischargedCoordinates_eventsFor carrier keep replacement same (List.finRange fields)

theorem creation_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (field : Fin fields) :
    field ∈ createdCoordinates (events carrier keep replacement same) ↔ keep field = false := by
  rw [created_exact]
  exact WireObligationRestoration.mem_forgottenCoordinates_iff keep field

theorem discharge_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (field : Fin fields) :
    field ∈ dischargedCoordinates (events carrier keep replacement same) ↔ keep field = false := by
  rw [discharged_exact]
  exact WireObligationRestoration.mem_forgottenCoordinates_iff keep field

theorem created_nodup (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    (createdCoordinates (events carrier keep replacement same)).Nodup := by
  rw [created_exact]
  have unique := WireObligationRestoration.created_nodup carrier keep
  rw [WireObligationRestoration.created_exact] at unique
  exact unique

theorem discharged_nodup (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    (dischargedCoordinates (events carrier keep replacement same)).Nodup := by
  rw [discharged_exact]
  have unique := created_nodup carrier keep replacement same
  rw [created_exact] at unique
  exact unique

private theorem replayPending_eventsFor (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (coordinates : List (Fin fields)) :
    replayPending [] (eventsFor carrier keep replacement same coordinates) = some [] := by
  induction coordinates with
  | nil => rfl
  | cons field remaining ih =>
      cases kept : keep field <;>
        simp [eventsFor, kept, replayPending, WireObligationRestoration.createR5, ih]

theorem replay_closed (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    replay [] (events carrier keep replacement same) = some [] := by
  unfold replay
  have unique : ([] ++ createdCoordinates (events carrier keep replacement same)).Nodup :=
    created_nodup carrier keep replacement same
  rw [if_pos unique]
  exact replayPending_eventsFor carrier keep replacement same (List.finRange fields)

theorem replay_rejects_duplicate_ids {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (pending : List (Fin fields)) (transcript : List (Event carrier keep replacement))
    (duplicate : ¬(pending ++ createdCoordinates transcript).Nodup) :
    replay pending transcript = none := by
  unfold replay
  rw [if_neg duplicate]

end PNP.DirectWire.WireMatchedCancellation
