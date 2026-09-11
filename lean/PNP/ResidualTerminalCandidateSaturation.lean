/-
Copyright (c) 2026 PNP Labs.

Candidate-derived saturation governance for the finite direct-wire terminal
model.  Physical dependencies are read from the actual program and output
word.  Profile dependencies are the exact finite Boolean influence relation of
the supplied executable ambient observer over every selected-gate context.

The resulting `TerminalSaturationSystem` is computed; callers do not supply a
`requires` relation or a proof that one was extracted correctly.  The generic
explicit-system closure remains available as a low-level theorem boundary.
This module does not assert that every derived saturation step is transparent,
route a nontransparent step, prove full `SaturatePositive` or `BCELReady`, or
claim polynomial runtime, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalSaturationPositivityFirewall

namespace PNP
namespace DirectWire

/-! ## Common ambient support implementation -/

private def candidateLocateMember {alpha : Type} [DecidableEq alpha]
    (item : alpha) :
    (items : List alpha) → item ∈ items →
      {index : Fin items.length // items.get index = item}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : item = head then
        ⟨⟨0, by simp only [List.length_cons]; exact Nat.zero_lt_succ _⟩,
          by change head = item; exact equal.symm⟩
      else
        let tailMember : item ∈ tail :=
          (List.mem_cons.mp member).resolve_left equal
        let located := candidateLocateMember item tail tailMember
        ⟨located.1.succ, by
          change tail.get located.1 = item
          exact located.2⟩

private def candidateMemberIndex {alpha : Type} [DecidableEq alpha]
    {item : alpha} {items : List alpha} (member : item ∈ items) :
    Fin items.length :=
  (candidateLocateMember item items member).1

/-- Locate one original gate in the ordered interface of an extracted support. -/
def TerminalExtractedSupport.interfaceIndex?
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    (support : TerminalExtractedSupport (profileWidth := profileWidth) candidate)
    (producer : Fin gates) : Option (Fin support.interface.length) :=
  if member : producer ∈ support.interface then
    some (candidateMemberIndex member)
  else
    none

/-- Embed one arbitrary extracted support in the fixed physical universe whose
    inputs are all original inputs followed by all original gate outputs, and
    whose outputs are all original gate coordinates. -/
def terminalAmbientSupportCandidate
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Candidate (inputs + gates)
      (extractTerminalSupport candidate records).gateCount gates :=
  let support := extractTerminalSupport candidate records
  let renamed := support.extractedCandidate.renameInputs fun index =>
    (support.boundary.get index).ambientIndex
  let word : DirectWireWord (inputs + gates) support.gateCount gates :=
    ⟨fun producer =>
      match support.interfaceIndex? producer with
      | some index => renamed.directWireWord.source index
      | none => .constant false⟩
  Candidate.ofDirectWireWord renamed.program word

/-- Type-erased gate-count form of the canonical ambient support. -/
def terminalAmbientSupportImplementation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Implementation (inputs + gates) gates :=
  (terminalAmbientSupportCandidate candidate records).toImplementation

/-! ## Candidate model and profile influence -/

/-- Executable data needed by the production terminal saturation path.  There
    is deliberately no dependency relation and no correctness certificate in
    this structure. -/
structure TerminalCandidateSaturationModel
    {inputs gates outputs profileWidth : Nat}
    (_candidate : Candidate inputs gates outputs) where
  profileSystem : TerminalProfileSystem inputs outputs profileWidth
  projection : TerminalProfileProjection profileWidth
  observe : Implementation (inputs + gates) gates →
    TerminalProfile profileWidth

/-- The shared ambient profile system used for every support state. -/
def TerminalCandidateSaturationModel.ambientProfileSystem
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    TerminalProfileSystem (inputs + gates) gates profileWidth :=
  { role := model.profileSystem.role
    observe := model.observe }

/-- The exact correspondence between the ten profile roles and the ten
    manuscript-labelled closure mechanisms. -/
def terminalSaturationRuleOfProfileRole :
    TerminalProfileRole → TerminalSaturationRuleKind
  | .carrier => .gateSource
  | .origin => .origin
  | .kernel => .kernel
  | .obligation => .obligation
  | .prefix => .prefixTail
  | .direction => .direction
  | .saturation => .saturation
  | .budget => .budget
  | .charge => .charge
  | .frontier => .interfaceConsumer

private def candidateTerminalAny {alpha : Type} :
    List alpha → (alpha → Bool) → Bool
  | [], _predicate => false
  | item :: items, predicate =>
      predicate item || candidateTerminalAny items predicate

private def terminalGateRecordList
    {inputs gates outputs profileWidth : Nat}
    (selected : List (Fin gates)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  selected.map fun gate => TerminalPrimitiveRecord.gate gate

/-- A gate influences a profile coordinate exactly when adding it changes that
    coordinate in at least one canonical context containing every possible
    subset of the other gates.  This finite reference computation detects
    interaction effects rather than testing only singleton supports. -/
def terminalGateInfluencesProfile
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (gate : Fin gates) (coordinate : Fin profileWidth) : Bool :=
  let otherGates := (allFin gates).filter fun other => decide (other ≠ gate)
  candidateTerminalAny (terminalListSubsets otherGates) fun selected =>
    let before : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
      terminalGateRecordList selected
    let after := TerminalPrimitiveRecord.gate gate :: before
    decide (model.observe
        (terminalAmbientSupportImplementation candidate after) coordinate ≠
      model.observe
        (terminalAmbientSupportImplementation candidate before) coordinate)

/-! ## Exact derived dependency relation -/

private def terminalPrimitiveRecordOfSource?
    {inputs gates outputs profileWidth : Nat} :
    Source inputs gates →
      Option (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  | .input index => some (.boundary index)
  | .constant _value => none
  | .gate index => some (.gate index)

private def sourceRequiresTerminalRecord
    {inputs gates outputs profileWidth : Nat}
    (source : Source inputs gates)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) : Bool :=
  decide (terminalPrimitiveRecordOfSource? source = some record)

private def terminalCandidateGateSourceRequires
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) : Bool :=
  match dependent with
  | .gate consumer =>
      let sources := candidate.program.terminalGateSources consumer
      sourceRequiresTerminalRecord sources.1 required ||
        sourceRequiresTerminalRecord sources.2 required
  | _ => false

private def terminalCandidateInterfaceRequires
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) : Bool :=
  match dependent, required with
  | .interface output, record =>
      sourceRequiresTerminalRecord
        (candidate.directWireWord.source output) record
  | record, .interface output =>
      sourceRequiresTerminalRecord
        (candidate.directWireWord.source output) record
  | _, _ => false

private def terminalCandidateProfileRequires
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (kind : TerminalSaturationRuleKind)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) : Bool :=
  match dependent, required with
  | .gate gate, .profile coordinate =>
      decide (kind = terminalSaturationRuleOfProfileRole
        (model.profileSystem.role coordinate)) &&
        terminalGateInfluencesProfile candidate model gate coordinate
  | .profile coordinate, .gate gate =>
      decide (kind = terminalSaturationRuleOfProfileRole
        (model.profileSystem.role coordinate)) &&
        terminalGateInfluencesProfile candidate model gate coordinate
  | _, _ => false

/-- The complete candidate-derived dependency test.  Physical incidence is
    read directly from the candidate; profile incidence is read from exact
    finite observer influence. -/
def terminalCandidateRequires
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (kind : TerminalSaturationRuleKind)
    (dependent required :
      TerminalPrimitiveRecord inputs gates outputs profileWidth) : Bool :=
  let profile := terminalCandidateProfileRequires
    candidate model kind dependent required
  match kind with
  | .gateSource =>
      terminalCandidateGateSourceRequires candidate dependent required || profile
  | .interfaceConsumer =>
      terminalCandidateInterfaceRequires candidate dependent required || profile
  | _ => profile

/-- Construct the production saturation system from the actual candidate and
    executable profile model. -/
def terminalCandidateSaturationSystem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    TerminalSaturationSystem inputs gates outputs profileWidth :=
  { profileSystem := model.profileSystem
    requires := terminalCandidateRequires candidate model }

@[simp] theorem terminalCandidateSaturationSystem_profileSystem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (terminalCandidateSaturationSystem candidate model).profileSystem =
      model.profileSystem := rfl

/-! ## Production-path wrappers -/

/-- Proper-positive support evidence whose dependency system is fixed by the
    candidate model rather than supplied separately. -/
abbrev TerminalCandidateProperPositiveSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :=
  TerminalProperPositiveSupport candidate
    (terminalCandidateSaturationSystem candidate model)

/-- Search the candidate-derived system without exposing an arbitrary system
    parameter. -/
def findTerminalCandidateProperPositiveSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    Option (TerminalCandidateProperPositiveSupport candidate model) :=
  findTerminalProperPositiveSupport candidate
    (terminalCandidateSaturationSystem candidate model)

/-- Candidate-derived source data for the BCEL boundary. -/
structure TerminalCandidateBCELAnchorProblem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) where
  support : TerminalCandidateProperPositiveSupport candidate model

/-- Forget only the candidate-derived wrapper and recover the existing audited
    BCEL problem. -/
def TerminalCandidateBCELAnchorProblem.toProblem
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalCandidateBCELAnchorProblem candidate model) :
    TerminalBCELAnchorProblem candidate
      (terminalCandidateSaturationSystem candidate model) :=
  { support := problem.support
    projection := model.projection
    observe := model.observe }

/-- Run the existing projection-loss/BCEL firewall through the
    candidate-derived production boundary. -/
def classifyTerminalCandidateSaturationPositivity
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalCandidateBCELAnchorProblem candidate model) :
    TerminalSaturationPositivityOutcome problem.toProblem :=
  classifyTerminalSaturationPositivity problem.toProblem

/-! ## Semantic reflection of candidate-derived profile dependencies -/

/-- Observe the actual ambient implementation of one gate context.  This
    notation adds no oracle, profile input or correctness certificate. -/
def terminalCandidateProfileObservation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (context : List (Fin gates)) (coordinate : Fin profileWidth) : Bool :=
  model.observe (terminalAmbientSupportImplementation candidate
    (context.map (fun gate =>
      (TerminalPrimitiveRecord.gate gate :
        TerminalPrimitiveRecord inputs gates outputs profileWidth)))) coordinate

private theorem candidateTerminalAny_true_iff {alpha : Type}
    (items : List alpha) (predicate : alpha → Bool) :
    candidateTerminalAny items predicate = true ↔
      ∃ item, item ∈ items ∧ predicate item = true := by
  induction items with
  | nil =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · rintro ⟨item, member, _checked⟩
        cases member
  | cons head tail ih =>
      change (predicate head || candidateTerminalAny tail predicate) = true ↔ _
      rw [Bool.or_eq_true, ih]
      constructor
      · rintro (checked | ⟨item, member, checked⟩)
        · exact ⟨head, List.Mem.head tail, checked⟩
        · exact ⟨item, List.Mem.tail head member, checked⟩
      · rintro ⟨item, member, checked⟩
        cases List.mem_cons.mp member with
        | inl equal =>
            subst item
            exact Or.inl checked
        | inr member =>
            exact Or.inr ⟨item, member, checked⟩

/-- The computed influence bit is true exactly when an actual observation
    changes in a canonical context, including nonsingleton interactions. -/
theorem terminalGateInfluencesProfile_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (gate : Fin gates) (coordinate : Fin profileWidth) :
    terminalGateInfluencesProfile candidate model gate coordinate = true ↔
      ∃ context,
        context ∈ terminalListSubsets
          ((allFin gates).filter (fun other => decide (other ≠ gate))) ∧
        terminalCandidateProfileObservation candidate model
            (gate :: context) coordinate ≠
          terminalCandidateProfileObservation candidate model context coordinate := by
  unfold terminalGateInfluencesProfile
  rw [candidateTerminalAny_true_iff]
  constructor
  · rintro ⟨context, member, changed⟩
    exact ⟨context, member, of_decide_eq_true changed⟩
  · rintro ⟨context, member, changed⟩
    exact ⟨context, member, decide_eq_true changed⟩

/-- Every profile-to-gate edge has exactly the coordinate's rule role and
    the computed semantic influence bit.  Other physical edge rules cannot
    introduce a spurious profile-to-gate dependency. -/
theorem terminalCandidateProfileRequires_eq_influence
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (kind : TerminalSaturationRuleKind)
    (coordinate : Fin profileWidth) (gate : Fin gates) :
    (terminalCandidateSaturationSystem candidate model).requires kind
        (.profile coordinate) (.gate gate) =
      (decide (kind = terminalSaturationRuleOfProfileRole
        (model.profileSystem.role coordinate)) &&
        terminalGateInfluencesProfile candidate model gate coordinate) := by
  cases kind <;> rfl

/-- A gate absent from the actual computed saturation cannot change a retained
    profile coordinate in any canonical gate context.  The executable observer
    remains model data; no polynomial construction or global route is claimed. -/
theorem terminalCandidateSaturate_profile_noninterference
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) (gate : Fin gates)
    (context : List (Fin gates))
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (gateAbsent : TerminalPrimitiveRecord.gate gate ∉
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (canonicalContext : context ∈ terminalListSubsets
      ((allFin gates).filter (fun other => decide (other ≠ gate)))) :
    terminalCandidateProfileObservation candidate model (gate :: context) coordinate =
      terminalCandidateProfileObservation candidate model context coordinate := by
  by_cases same :
      terminalCandidateProfileObservation candidate model (gate :: context) coordinate =
        terminalCandidateProfileObservation candidate model context coordinate
  · exact same
  · have influence : terminalGateInfluencesProfile candidate model gate coordinate = true :=
      (terminalGateInfluencesProfile_eq_true_iff candidate model gate coordinate).mpr
        ⟨context, canonicalContext, same⟩
    let kind := terminalSaturationRuleOfProfileRole
      (model.profileSystem.role coordinate)
    have edge :
        (terminalCandidateSaturationSystem candidate model).requires kind
          (.profile coordinate) (.gate gate) = true := by
      rw [terminalCandidateProfileRequires_eq_influence]
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true rfl, influence⟩
    exact False.elim (gateAbsent
      (terminalSaturateRecords_closed
        (terminalCandidateSaturationSystem candidate model) seed
        kind (.profile coordinate) (.gate gate) profileMember edge))

end DirectWire
end PNP
