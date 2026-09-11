/-
Copyright (c) 2026 PNP Labs.

Structural support normalization and retained ambient-profile locality for the
candidate-derived terminal saturation model. The executable observer remains
supplied model data, and influence still enumerates every canonical subset.
No unconditional saturation, global route or polynomial-runtime claim is made.
-/

import PNP.ResidualTerminalCandidateSaturation

namespace PNP
namespace DirectWire

/-- The ambient implementation depends on the selected gates, not on the
    order, multiplicity or non-gate metadata of the record representation. -/
theorem terminalAmbientSupportImplementation_eq_of_gateSelected_eq
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (selectedEqual : terminalGateSelected left = terminalGateSelected right) :
    terminalAmbientSupportImplementation candidate left =
      terminalAmbientSupportImplementation candidate right := by
  have extractedEqual :=
    extractTerminalSupport_eq_of_gateSelected_eq candidate left right selectedEqual
  let embed
      (support : TerminalExtractedSupport (profileWidth := profileWidth) candidate) :
      Implementation (inputs + gates) gates :=
    let renamed := support.extractedCandidate.renameInputs fun index =>
      (support.boundary.get index).ambientIndex
    let word : DirectWireWord (inputs + gates) support.gateCount gates :=
      ⟨fun producer =>
        match support.interfaceIndex? producer with
        | some index => renamed.directWireWord.source index
        | none => .constant false⟩
    (Candidate.ofDirectWireWord renamed.program word).toImplementation
  have interfaceRecordsIgnored
      (support : TerminalExtractedSupport (profileWidth := profileWidth) candidate)
      (producer : Fin gates) :
      ({ support with records := right } :
        TerminalExtractedSupport (profileWidth := profileWidth) candidate).interfaceIndex?
          producer = support.interfaceIndex? producer := by
    cases support
    simp only [TerminalExtractedSupport.interfaceIndex?]
  have recordsIgnored
      (support : TerminalExtractedSupport (profileWidth := profileWidth) candidate) :
      embed support = embed { support with records := right } := by
    dsimp only [embed]
    apply congrArg (fun source : Fin gates → Source (inputs + gates) support.gateCount =>
      (Candidate.ofDirectWireWord
        (support.extractedCandidate.renameInputs fun index =>
          (support.boundary.get index).ambientIndex).program
        (⟨source⟩ : DirectWireWord (inputs + gates) support.gateCount gates)).toImplementation)
    funext producer
    rw [interfaceRecordsIgnored support producer]
    cases lookup : support.interfaceIndex? producer <;> rfl
  change embed (extractTerminalSupport candidate left) =
    embed (extractTerminalSupport candidate right)
  exact (recordsIgnored (extractTerminalSupport candidate left)).trans
    (congrArg embed extractedEqual)

private theorem profileGateRecord_mem_iff
    {inputs gates outputs profileWidth : Nat}
    (gate : Fin gates) (context : List (Fin gates)) :
    (TerminalPrimitiveRecord.gate gate :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) ∈
        context.map (fun found => TerminalPrimitiveRecord.gate found) ↔
      gate ∈ context := by
  constructor
  · intro member
    obtain ⟨found, foundMember, equal⟩ := List.mem_map.mp member
    have gateEqual : found = gate := TerminalPrimitiveRecord.gate.inj equal
    exact gateEqual ▸ foundMember
  · intro member
    exact List.mem_map.mpr ⟨gate, member, rfl⟩

/-- Equal gate membership gives equal actual observations, even for arbitrary
    reordered or duplicated gate lists. No observer-congruence premise is used. -/
theorem terminalCandidateProfileObservation_eq_of_gateMembership_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (left right : List (Fin gates)) (coordinate : Fin profileWidth)
    (sameGates : ∀ gate, gate ∈ left ↔ gate ∈ right) :
    terminalCandidateProfileObservation candidate model left coordinate =
      terminalCandidateProfileObservation candidate model right coordinate := by
  unfold terminalCandidateProfileObservation
  apply congrArg (fun implementation => model.observe implementation coordinate)
  apply terminalAmbientSupportImplementation_eq_of_gateSelected_eq candidate
  funext gate
  simp only [terminalGateSelected, profileGateRecord_mem_iff, sameGates]

private theorem profileCanonicalGate_mem_iff
    {inputs gates outputs profileWidth : Nat}
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    gate ∈ (allFin gates).filter (terminalGateSelected records) ↔
      TerminalPrimitiveRecord.gate gate ∈ records := by
  constructor
  · intro member
    exact (terminalGateSelected_eq_true_iff records gate).mp
      (List.mem_filter.mp member).2
  · intro member
    exact List.mem_filter.mpr
      ⟨mem_allFin gate, (terminalGateSelected_eq_true_iff records gate).mpr member⟩

private theorem profileObservation_records_canonical
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) :
    model.observe (terminalAmbientSupportImplementation candidate records) coordinate =
      terminalCandidateProfileObservation candidate model
        ((allFin gates).filter (terminalGateSelected records)) coordinate := by
  unfold terminalCandidateProfileObservation
  apply congrArg (fun implementation => model.observe implementation coordinate)
  apply terminalAmbientSupportImplementation_eq_of_gateSelected_eq candidate
  funext gate
  simp only [terminalGateSelected, profileGateRecord_mem_iff,
    profileCanonicalGate_mem_iff]

private theorem profileObservation_any_context
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) (gate : Fin gates) (context : List (Fin gates))
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (gateAbsent : TerminalPrimitiveRecord.gate gate ∉
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) :
    terminalCandidateProfileObservation candidate model (gate :: context) coordinate =
      terminalCandidateProfileObservation candidate model context coordinate := by
  by_cases gatePresent : gate ∈ context
  · apply terminalCandidateProfileObservation_eq_of_gateMembership_iff
      candidate model (gate :: context) context coordinate
    intro other
    constructor
    · intro member
      cases List.mem_cons.mp member with
      | inl equal => exact equal.symm ▸ gatePresent
      | inr present => exact present
    · intro member
      exact List.Mem.tail gate member
  · let canonical :=
      ((allFin gates).filter (fun other => decide (other ≠ gate))).filter
        (fun other => decide (other ∈ context))
    have sameGates : ∀ other, other ∈ canonical ↔ other ∈ context := by
      intro other
      constructor
      · intro member
        exact of_decide_eq_true (List.mem_filter.mp member).2
      · intro member
        have different : other ≠ gate := by
          intro equal
          exact gatePresent (equal ▸ member)
        exact List.mem_filter.mpr
          ⟨List.mem_filter.mpr ⟨mem_allFin other, decide_eq_true different⟩,
            decide_eq_true member⟩
    have canonicalMember : canonical ∈ terminalListSubsets
        ((allFin gates).filter (fun other => decide (other ≠ gate))) :=
      filter_mem_terminalListSubsets _ _
    have normalize :
        terminalCandidateProfileObservation candidate model canonical coordinate =
          terminalCandidateProfileObservation candidate model context coordinate :=
      terminalCandidateProfileObservation_eq_of_gateMembership_iff
        candidate model canonical context coordinate sameGates
    have normalizeWithGate :
        terminalCandidateProfileObservation candidate model (gate :: canonical) coordinate =
          terminalCandidateProfileObservation candidate model (gate :: context) coordinate := by
      apply terminalCandidateProfileObservation_eq_of_gateMembership_iff
        candidate model (gate :: canonical) (gate :: context) coordinate
      intro other
      simp only [List.mem_cons, sameGates]
    exact normalizeWithGate.symm.trans
      ((terminalCandidateSaturate_profile_noninterference candidate model seed
        coordinate gate canonical profileMember gateAbsent canonicalMember).trans normalize)


private theorem profileObservation_remove_absent_prefix
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) (omitted remaining : List (Fin gates))
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (allAbsent : ∀ gate, gate ∈ omitted → TerminalPrimitiveRecord.gate gate ∉
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) :
    terminalCandidateProfileObservation candidate model (omitted ++ remaining) coordinate =
      terminalCandidateProfileObservation candidate model remaining coordinate := by
  revert allAbsent
  induction omitted with
  | nil => intro _; rfl
  | cons gate tail inductionHypothesis =>
      intro allAbsent
      have gateAbsent := allAbsent gate (List.Mem.head tail)
      have tailAbsent : ∀ other, other ∈ tail → TerminalPrimitiveRecord.gate other ∉
          terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed :=
        fun other member => allAbsent other (List.Mem.tail gate member)
      exact (profileObservation_any_context candidate model seed coordinate gate
        (tail ++ remaining) profileMember gateAbsent).trans (inductionHypothesis tailAbsent)

private theorem profileObservation_restrict_to_saturated
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) (context : List (Fin gates))
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) :
    terminalCandidateProfileObservation candidate model context coordinate =
      terminalCandidateProfileObservation candidate model
        (context.filter (terminalGateSelected
          (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)))
        coordinate := by
  let saturated :=
    terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed
  let selected := terminalGateSelected saturated
  let omitted := context.filter (fun gate => Bool.not (selected gate))
  let kept := context.filter selected
  have sameGates : ∀ gate, gate ∈ context ↔ gate ∈ omitted ++ kept := by
    intro gate
    constructor
    · intro member
      cases selectedValue : selected gate with
      | false =>
          apply List.mem_append.mpr
          apply Or.inl
          exact List.mem_filter.mpr ⟨member, by
            change Bool.not (selected gate) = true
            rw [selectedValue]
            rfl⟩
      | true =>
          exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨member, selectedValue⟩))
    · intro member
      cases List.mem_append.mp member with
      | inl omittedMember => exact (List.mem_filter.mp omittedMember).1
      | inr keptMember => exact (List.mem_filter.mp keptMember).1
  have allAbsent : ∀ gate, gate ∈ omitted → TerminalPrimitiveRecord.gate gate ∉ saturated := by
    intro gate member retained
    have selectedTrue : selected gate = true :=
      (terminalGateSelected_eq_true_iff saturated gate).mpr retained
    have omittedTrue : Bool.not (selected gate) = true := (List.mem_filter.mp member).2
    rw [selectedTrue] at omittedTrue
    cases omittedTrue
  exact (terminalCandidateProfileObservation_eq_of_gateMembership_iff
    candidate model context (omitted ++ kept) coordinate sameGates).trans
      (profileObservation_remove_absent_prefix candidate model seed coordinate
        omitted kept profileMember allAbsent)

/-- For every retained profile coordinate, the actual ambient observation of
    arbitrary primitive-record supports depends only on their retained gates.
    The dependency closure is computed from the candidate and executable model. -/
theorem terminalCandidateSaturate_profile_locality
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth)
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (recordAgreement : ∀ gate,
      TerminalPrimitiveRecord.gate gate ∈
        terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed →
      (TerminalPrimitiveRecord.gate gate ∈ left ↔
        TerminalPrimitiveRecord.gate gate ∈ right)) :
    model.observe (terminalAmbientSupportImplementation candidate left) coordinate =
      model.observe (terminalAmbientSupportImplementation candidate right) coordinate := by
  let saturated :=
    terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed
  let selected := terminalGateSelected saturated
  let leftGates := (allFin gates).filter (terminalGateSelected left)
  let rightGates := (allFin gates).filter (terminalGateSelected right)
  have restrictedAgreement :
      ∀ gate, gate ∈ leftGates.filter selected ↔ gate ∈ rightGates.filter selected := by
    intro gate
    constructor
    · intro member
      obtain ⟨leftMember, retained⟩ := List.mem_filter.mp member
      have retainedRecord := (terminalGateSelected_eq_true_iff saturated gate).mp retained
      have leftRecord := (profileCanonicalGate_mem_iff left gate).mp leftMember
      have rightRecord := (recordAgreement gate retainedRecord).mp leftRecord
      exact List.mem_filter.mpr
        ⟨(profileCanonicalGate_mem_iff right gate).mpr rightRecord, retained⟩
    · intro member
      obtain ⟨rightMember, retained⟩ := List.mem_filter.mp member
      have retainedRecord := (terminalGateSelected_eq_true_iff saturated gate).mp retained
      have rightRecord := (profileCanonicalGate_mem_iff right gate).mp rightMember
      have leftRecord := (recordAgreement gate retainedRecord).mpr rightRecord
      exact List.mem_filter.mpr
        ⟨(profileCanonicalGate_mem_iff left gate).mpr leftRecord, retained⟩
  calc
    model.observe (terminalAmbientSupportImplementation candidate left) coordinate =
        terminalCandidateProfileObservation candidate model leftGates coordinate :=
      profileObservation_records_canonical candidate model left coordinate
    _ = terminalCandidateProfileObservation candidate model
        (leftGates.filter selected) coordinate :=
      profileObservation_restrict_to_saturated candidate model seed coordinate leftGates profileMember
    _ = terminalCandidateProfileObservation candidate model
        (rightGates.filter selected) coordinate :=
      terminalCandidateProfileObservation_eq_of_gateMembership_iff
        candidate model (leftGates.filter selected) (rightGates.filter selected)
        coordinate restrictedAgreement
    _ = terminalCandidateProfileObservation candidate model rightGates coordinate :=
      (profileObservation_restrict_to_saturated candidate model seed coordinate
        rightGates profileMember).symm
    _ = model.observe (terminalAmbientSupportImplementation candidate right) coordinate :=
      (profileObservation_records_canonical candidate model right coordinate).symm

/-- The actual computed saturation preserves every retained ambient-profile
    observation of the complete gate universe. This does not claim profile
    derivation, cost transparency, unconditional ZeroSlack or polynomial runtime. -/
theorem terminalCandidateSaturate_profile_preserved
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth)
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) :
    model.observe
      (terminalAmbientSupportImplementation candidate
        (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed))
      coordinate =
    model.observe
      (terminalAmbientSupportImplementation candidate
        (allTerminalPrimitiveRecords inputs gates outputs profileWidth))
      coordinate := by
  apply terminalCandidateSaturate_profile_locality candidate model seed
    (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth) coordinate profileMember
  intro gate retained
  exact ⟨fun _ => mem_allTerminalPrimitiveRecords (.gate gate), fun _ => retained⟩
end DirectWire
end PNP
