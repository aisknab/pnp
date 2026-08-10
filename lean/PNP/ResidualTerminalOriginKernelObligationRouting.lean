/-
Copyright (c) 2026 PNP Labs.

Proof-bearing finite routing for the origin, kernel, and obligation profile
closures in candidate-derived terminal saturation.  Recognition is tied to the
exact rule label, profile role, gate/profile orientation, and recomputed
candidate-derived dependency edge.  A recognized closure is safe only when its
cost step is transparent, obligation coordinates remain discharged, and a
coordinate hidden by the quotient projection does not change.

This closes only the finite local form of
`originKernelObligationClosureRouted`.  Returned coordinates are local route
evidence, not one of the manuscript's complete global outcomes or a Package E
acceptance.  Full `SaturatePositive`, global route completeness, RankWF,
polynomial runtime, SAT in P, and P = NP remain open.
-/

import PNP.ResidualTerminalInterfaceExposureRouting

namespace PNP
namespace DirectWire

/-! ## Exact closure coordinates -/

/-- The three profile roles named by the remaining finite saturation-closure
    obligation. -/
inductive TerminalOriginKernelObligationRole where
  | origin
  | kernel
  | obligation
  deriving Repr, DecidableEq

/-- Embed the local role in the complete terminal profile-role universe. -/
def TerminalOriginKernelObligationRole.profileRole :
    TerminalOriginKernelObligationRole → TerminalProfileRole
  | .origin => .origin
  | .kernel => .kernel
  | .obligation => .obligation

/-- Exact saturation rule corresponding to the local profile role. -/
def TerminalOriginKernelObligationRole.ruleKind :
    TerminalOriginKernelObligationRole → TerminalSaturationRuleKind
  | .origin => .origin
  | .kernel => .kernel
  | .obligation => .obligation

/-- Candidate-derived profile influence can generate a profile record from a
    gate or a gate record from a profile coordinate. -/
inductive TerminalOriginKernelObligationOrientation where
  | profileRequiresGate
  | gateRequiresProfile
  deriving Repr, DecidableEq

/-- One exact origin, kernel, or obligation closure coordinate. -/
structure TerminalOriginKernelObligationCoordinate
    (gates profileWidth : Nat) where
  role : TerminalOriginKernelObligationRole
  coordinate : Fin profileWidth
  gate : Fin gates
  orientation : TerminalOriginKernelObligationOrientation
  deriving Repr, DecidableEq

/-- Semantic shape of one exact closure coordinate. -/
def TerminalOriginKernelObligationCoordinate.Matches
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (coordinate : TerminalOriginKernelObligationCoordinate gates profileWidth)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Prop :=
  model.profileSystem.role coordinate.coordinate = coordinate.role.profileRole ∧
    event.kind? = some coordinate.role.ruleKind ∧
    match coordinate.orientation with
    | .profileRequiresGate =>
        event.dependent = .profile coordinate.coordinate ∧
          event.required = .gate coordinate.gate
    | .gateRequiresProfile =>
        event.dependent = .gate coordinate.gate ∧
          event.required = .profile coordinate.coordinate

/-- Read the exact event shape and verify that its rule agrees with the
    executable profile role. -/
def terminalOriginKernelObligationCoordinate?
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    Option (TerminalOriginKernelObligationCoordinate gates profileWidth) :=
  match event.kind?, event.dependent, event.required with
  | some .origin, .profile coordinate, .gate gate =>
      if model.profileSystem.role coordinate = .origin then
        some
          { role := .origin
            coordinate := coordinate
            gate := gate
            orientation := .profileRequiresGate }
      else none
  | some .origin, .gate gate, .profile coordinate =>
      if model.profileSystem.role coordinate = .origin then
        some
          { role := .origin
            coordinate := coordinate
            gate := gate
            orientation := .gateRequiresProfile }
      else none
  | some .kernel, .profile coordinate, .gate gate =>
      if model.profileSystem.role coordinate = .kernel then
        some
          { role := .kernel
            coordinate := coordinate
            gate := gate
            orientation := .profileRequiresGate }
      else none
  | some .kernel, .gate gate, .profile coordinate =>
      if model.profileSystem.role coordinate = .kernel then
        some
          { role := .kernel
            coordinate := coordinate
            gate := gate
            orientation := .gateRequiresProfile }
      else none
  | some .obligation, .profile coordinate, .gate gate =>
      if model.profileSystem.role coordinate = .obligation then
        some
          { role := .obligation
            coordinate := coordinate
            gate := gate
            orientation := .profileRequiresGate }
      else none
  | some .obligation, .gate gate, .profile coordinate =>
      if model.profileSystem.role coordinate = .obligation then
        some
          { role := .obligation
            coordinate := coordinate
            gate := gate
            orientation := .gateRequiresProfile }
      else none
  | _, _, _ => none

/-- The shape query cannot manufacture a role, rule, or orientation. -/
theorem terminalOriginKernelObligationCoordinate?_sound
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalOriginKernelObligationCoordinate gates profileWidth)
    (found : terminalOriginKernelObligationCoordinate?
      candidate model event = some coordinate) :
    coordinate.Matches model event := by
  cases kindAt : event.kind? with
  | none =>
      simp [terminalOriginKernelObligationCoordinate?, kindAt] at found
  | some kind =>
      cases kind <;>
        cases dependentAt : event.dependent <;>
        cases requiredAt : event.required <;>
        simp [terminalOriginKernelObligationCoordinate?,
          TerminalOriginKernelObligationCoordinate.Matches,
          TerminalOriginKernelObligationRole.profileRole,
          TerminalOriginKernelObligationRole.ruleKind,
          kindAt, dependentAt, requiredAt] at found ⊢ <;>
        try simp_all
      all_goals
        obtain ⟨roleAt, rfl⟩ := found
        exact ⟨roleAt, rfl, rfl, rfl⟩

/-- Recompute the candidate-derived edge before accepting the coordinate. -/
def terminalCandidateOriginKernelObligationCoordinate?
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    Option (TerminalOriginKernelObligationCoordinate gates profileWidth) :=
  match terminalOriginKernelObligationCoordinate? candidate model event with
  | none => none
  | some coordinate =>
      if (terminalCandidateSaturationSystem candidate model).requires
          coordinate.role.ruleKind event.dependent event.required = true then
        some coordinate
      else
        none

/-- A production coordinate retains the exact checked event shape. -/
theorem terminalCandidateOriginKernelObligationCoordinate?_shape
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalOriginKernelObligationCoordinate gates profileWidth)
    (found : terminalCandidateOriginKernelObligationCoordinate?
      candidate model event = some coordinate) :
    terminalOriginKernelObligationCoordinate? candidate model event =
      some coordinate := by
  unfold terminalCandidateOriginKernelObligationCoordinate? at found
  cases shapeAt : terminalOriginKernelObligationCoordinate?
      candidate model event with
  | none => simp [shapeAt] at found
  | some shaped =>
      simp only [shapeAt] at found
      split at found
      next _edge => exact found
      next _noEdge => cases found

/-- A production coordinate is backed by the recomputed candidate edge. -/
theorem terminalCandidateOriginKernelObligationCoordinate?_edge
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalOriginKernelObligationCoordinate gates profileWidth)
    (found : terminalCandidateOriginKernelObligationCoordinate?
      candidate model event = some coordinate) :
    (terminalCandidateSaturationSystem candidate model).requires
      coordinate.role.ruleKind event.dependent event.required = true := by
  unfold terminalCandidateOriginKernelObligationCoordinate? at found
  cases shapeAt : terminalOriginKernelObligationCoordinate?
      candidate model event with
  | none => simp [shapeAt] at found
  | some shaped =>
      simp only [shapeAt] at found
      split at found
      next edge =>
        cases found
        exact edge
      next _noEdge => cases found

/-! ## Closure safety and local routes -/

/-- The exact profile value at one support snapshot. -/
def terminalOriginKernelObligationProfileValue
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) : Bool :=
  model.observe (terminalAmbientSupportImplementation candidate records)
    coordinate

/-- A safe closure is cost-transparent, does not leave an obligation open, and
    does not change a profile coordinate hidden by the quotient projection. -/
structure TerminalOriginKernelObligationClosureSafe
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalOriginKernelObligationCoordinate
      gates profileWidth) where
  transparent : TerminalTransparentSaturationStep candidate model event
  obligationDischarged : coordinate.role = .obligation →
    terminalOriginKernelObligationProfileValue candidate model
      event.afterRecords coordinate.coordinate = false
  forgottenStable : model.projection.Forgets coordinate.coordinate →
    terminalOriginKernelObligationProfileValue candidate model
        event.beforeRecords coordinate.coordinate =
      terminalOriginKernelObligationProfileValue candidate model
        event.afterRecords coordinate.coordinate

/-- Exact local reason why a recognized closure is unsafe. -/
inductive TerminalOriginKernelObligationClosureFailureReason where
  | nontransparent (reason : TerminalNontransparentSaturationReason)
  | openObligation
  | forgottenProfileMismatch
  deriving Repr, DecidableEq

/-- Semantic content of one local closure failure. -/
def TerminalOriginKernelObligationClosureFailureReason.Sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    {coordinate : TerminalOriginKernelObligationCoordinate
      gates profileWidth}
    (reason : TerminalOriginKernelObligationClosureFailureReason) : Prop :=
  match reason with
  | .nontransparent balanceReason =>
      terminalSaturationStepFailureReason? candidate model event =
          some balanceReason ∧
        ¬TerminalTransparentSaturationStep candidate model event
  | .openObligation =>
      coordinate.role = .obligation ∧
        terminalOriginKernelObligationProfileValue candidate model
          event.afterRecords coordinate.coordinate = true
  | .forgottenProfileMismatch =>
      model.projection.Forgets coordinate.coordinate ∧
        terminalOriginKernelObligationProfileValue candidate model
            event.beforeRecords coordinate.coordinate ≠
          terminalOriginKernelObligationProfileValue candidate model
            event.afterRecords coordinate.coordinate

/-- Proof-bearing local route for one exact unsafe closure. -/
structure TerminalOriginKernelObligationClosureRoute
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  coordinate : TerminalOriginKernelObligationCoordinate gates profileWidth
  selected : terminalCandidateOriginKernelObligationCoordinate?
    candidate model event = some coordinate
  reason : TerminalOriginKernelObligationClosureFailureReason
  failure : reason.Sound
    (candidate := candidate) (model := model) (event := event)
    (coordinate := coordinate)

/-- Exact route soundness: shape, candidate edge, and failure are all checked. -/
def TerminalOriginKernelObligationClosureRoute.Sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (route : TerminalOriginKernelObligationClosureRoute
      candidate model event) : Prop :=
  route.coordinate.Matches model event ∧
    (terminalCandidateSaturationSystem candidate model).requires
      route.coordinate.role.ruleKind event.dependent event.required = true ∧
    route.reason.Sound
      (candidate := candidate) (model := model) (event := event)
      (coordinate := route.coordinate)

theorem TerminalOriginKernelObligationClosureRoute.sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (route : TerminalOriginKernelObligationClosureRoute
      candidate model event) : route.Sound :=
  ⟨terminalOriginKernelObligationCoordinate?_sound
      candidate model event route.coordinate
      (terminalCandidateOriginKernelObligationCoordinate?_shape
        candidate model event route.coordinate route.selected),
    terminalCandidateOriginKernelObligationCoordinate?_edge
      candidate model event route.coordinate route.selected,
    route.failure⟩

/-- Total classification at one possible origin/kernel/obligation closure. -/
inductive TerminalOriginKernelObligationStepOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  | notClosure
      (notSelected : terminalCandidateOriginKernelObligationCoordinate?
        candidate model event = none)
  | safe
      (coordinate : TerminalOriginKernelObligationCoordinate
        gates profileWidth)
      (selected : terminalCandidateOriginKernelObligationCoordinate?
        candidate model event = some coordinate)
      (evidence : TerminalOriginKernelObligationClosureSafe
        candidate model event coordinate)
  | route (evidence : TerminalOriginKernelObligationClosureRoute
      candidate model event)

/-- Recompute closure incidence, cost balance, obligation discharge, and mode
    safety in one deterministic order. -/
def classifyTerminalOriginKernelObligationStep
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    TerminalOriginKernelObligationStepOutcome candidate model event :=
  match selected : terminalCandidateOriginKernelObligationCoordinate?
      candidate model event with
  | none => .notClosure selected
  | some coordinate =>
      match classified : classifyTerminalSaturationStepBalance
          candidate model event with
      | .nontransparent reason failure =>
          .route
            { coordinate := coordinate
              selected := selected
              reason := .nontransparent reason
              failure := by
                exact ⟨by
                  simp [terminalSaturationStepFailureReason?, classified],
                  failure⟩ }
      | .transparent transparent =>
          if obligationOpen : coordinate.role = .obligation ∧
              terminalOriginKernelObligationProfileValue candidate model
                event.afterRecords coordinate.coordinate = true then
            .route
              { coordinate := coordinate
                selected := selected
                reason := .openObligation
                failure := obligationOpen }
          else if hidden : model.projection.keep coordinate.coordinate = false ∧
              terminalOriginKernelObligationProfileValue candidate model
                  event.beforeRecords coordinate.coordinate ≠
                terminalOriginKernelObligationProfileValue candidate model
                  event.afterRecords coordinate.coordinate then
            .route
              { coordinate := coordinate
                selected := selected
                reason := .forgottenProfileMismatch
                failure := hidden }
          else
            .safe coordinate selected
              { transparent := transparent
                obligationDischarged := by
                  intro roleAt
                  cases valueAt :
                      terminalOriginKernelObligationProfileValue candidate model
                        event.afterRecords coordinate.coordinate with
                  | false => rfl
                  | true => exact (obligationOpen ⟨roleAt, valueAt⟩).elim
                forgottenStable := by
                  intro forgotten
                  by_cases stable :
                      terminalOriginKernelObligationProfileValue candidate model
                          event.beforeRecords coordinate.coordinate =
                        terminalOriginKernelObligationProfileValue candidate model
                          event.afterRecords coordinate.coordinate
                  · exact stable
                  · exact (hidden ⟨forgotten, stable⟩).elim }

/-- A recognized closure is either safe or carries a proof-bearing route. -/
theorem terminalOriginKernelObligation_safe_or_route
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalOriginKernelObligationCoordinate gates profileWidth)
    (selected : terminalCandidateOriginKernelObligationCoordinate?
      candidate model event = some coordinate) :
    Nonempty (TerminalOriginKernelObligationClosureSafe
      candidate model event coordinate) ∨
      Nonempty (TerminalOriginKernelObligationClosureRoute
        candidate model event) := by
  cases outcomeAt : classifyTerminalOriginKernelObligationStep
      candidate model event with
  | notClosure notSelected =>
      rw [selected] at notSelected
      cases notSelected
  | safe foundCoordinate selectedAt evidence =>
      rw [selected] at selectedAt
      cases selectedAt
      exact Or.inl ⟨evidence⟩
  | route evidence => exact Or.inr ⟨evidence⟩

/-! ## Exact-first combined trace routing -/

/-- Evidence that one event is safe for the finite composed saturation path. -/
inductive TerminalSaturationClosureSafeStep
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Prop where
  | interface
      (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
      (selected : terminalCandidateInterfaceExposureCoordinate?
        candidate model event = some coordinate)
      (transparent : TerminalTransparentSaturationStep candidate model event)
  | closure
      (coordinate : TerminalOriginKernelObligationCoordinate
        gates profileWidth)
      (selected : terminalCandidateOriginKernelObligationCoordinate?
        candidate model event = some coordinate)
      (safe : TerminalOriginKernelObligationClosureSafe
        candidate model event coordinate)
  | ordinary
      (notInterface : terminalCandidateInterfaceExposureCoordinate?
        candidate model event = none)
      (notClosure : terminalCandidateOriginKernelObligationCoordinate?
        candidate model event = none)
      (transparent : TerminalTransparentSaturationStep candidate model event)

/-- Every composed-safe event is cost-transparent. -/
theorem TerminalSaturationClosureSafeStep.transparent
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (safe : TerminalSaturationClosureSafeStep candidate model event) :
    TerminalTransparentSaturationStep candidate model event := by
  cases safe with
  | interface _coordinate _selected transparent => exact transparent
  | closure _coordinate _selected evidence => exact evidence.transparent
  | ordinary _notInterface _notClosure transparent => exact transparent

/-- Exact unclassified first balance failure after both local route queries
    have failed closed. -/
structure TerminalOtherNontransparentSaturationFailure
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  reason : TerminalNontransparentSaturationReason
  reasonSelected : terminalSaturationStepFailureReason?
    candidate model event = some reason
  failure : ¬TerminalTransparentSaturationStep candidate model event
  notInterface : terminalCandidateInterfaceExposureCoordinate?
    candidate model event = none
  notClosure : terminalCandidateOriginKernelObligationCoordinate?
    candidate model event = none

/-- One total step in the composed finite route dispatcher. -/
inductive TerminalSaturationClosureStepOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  | safe (evidence : TerminalSaturationClosureSafeStep candidate model event)
  | interfaceExposure (route : TerminalInterfaceExposureERoute
      candidate model event)
  | originKernelObligation (route :
      TerminalOriginKernelObligationClosureRoute candidate model event)
  | otherNontransparent (failure :
      TerminalOtherNontransparentSaturationFailure candidate model event)

/-- Interface routing has first priority, followed by the exact closure query;
    every remaining nontransparent event stays fail-closed. -/
def classifyTerminalSaturationClosureStep
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    TerminalSaturationClosureStepOutcome candidate model event :=
  match classifyTerminalInterfaceExposureStep candidate model event with
  | .eRoute route => .interfaceExposure route
  | .transparent coordinate selected transparent =>
      .safe (.interface coordinate selected transparent)
  | .notInterface notInterface =>
      match classifyTerminalOriginKernelObligationStep candidate model event with
      | .route route => .originKernelObligation route
      | .safe coordinate selected safe =>
          .safe (.closure coordinate selected safe)
      | .notClosure notClosure =>
          match classified : classifyTerminalSaturationStepBalance
              candidate model event with
          | .transparent transparent =>
              .safe (.ordinary notInterface notClosure transparent)
          | .nontransparent reason failure =>
              .otherNontransparent
                { reason := reason
                  reasonSelected := by
                    simp [terminalSaturationStepFailureReason?, classified]
                  failure := failure
                  notInterface := notInterface
                  notClosure := notClosure }

/-- Exact split around the first event rejected by the composed dispatcher. -/
structure TerminalFirstSaturationClosureEvent
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)) where
  prior : List (TerminalSaturationTraceEvent
    inputs gates outputs profileWidth)
  event : TerminalSaturationTraceEvent inputs gates outputs profileWidth
  remaining : List (TerminalSaturationTraceEvent
    inputs gates outputs profileWidth)
  split : events = prior ++ event :: remaining
  priorSafe : ∀ priorEvent, priorEvent ∈ prior →
    TerminalSaturationClosureSafeStep candidate model priorEvent

private def TerminalFirstSaturationClosureEvent.prepend
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {head : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    {tail : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)}
    (safe : TerminalSaturationClosureSafeStep candidate model head)
    (first : TerminalFirstSaturationClosureEvent candidate model tail) :
    TerminalFirstSaturationClosureEvent candidate model (head :: tail) :=
  { prior := head :: first.prior
    event := first.event
    remaining := first.remaining
    split := by
      calc
        head :: tail = head ::
            (first.prior ++ first.event :: first.remaining) :=
          congrArg (fun events => head :: events) first.split
        _ = (head :: first.prior) ++ first.event :: first.remaining := rfl
    priorSafe := by
      intro priorEvent member
      cases List.mem_cons.mp member with
      | inl equal => simpa [equal] using safe
      | inr tailMember => exact first.priorSafe priorEvent tailMember }

/-- Total exact-first result for an arbitrary event list. -/
inductive TerminalSaturationClosureRoutingOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)) where
  | balanced (allSafe : ∀ event, event ∈ events →
      TerminalSaturationClosureSafeStep candidate model event)
  | interfaceExposure
      (first : TerminalFirstSaturationClosureEvent candidate model events)
      (route : TerminalInterfaceExposureERoute
        candidate model first.event)
  | originKernelObligation
      (first : TerminalFirstSaturationClosureEvent candidate model events)
      (route : TerminalOriginKernelObligationClosureRoute
        candidate model first.event)
  | otherNontransparent
      (first : TerminalFirstSaturationClosureEvent candidate model events)
      (failure : TerminalOtherNontransparentSaturationFailure
        candidate model first.event)

private def classifyTerminalSaturationClosureRoutingEvents
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)) →
      TerminalSaturationClosureRoutingOutcome candidate model events
  | [] => .balanced (by intro event member; cases member)
  | event :: remaining =>
      match classifyTerminalSaturationClosureStep candidate model event with
      | .interfaceExposure route =>
          .interfaceExposure
            { prior := []
              event := event
              remaining := remaining
              split := rfl
              priorSafe := by intro priorEvent member; cases member }
            route
      | .originKernelObligation route =>
          .originKernelObligation
            { prior := []
              event := event
              remaining := remaining
              split := rfl
              priorSafe := by intro priorEvent member; cases member }
            route
      | .otherNontransparent failure =>
          .otherNontransparent
            { prior := []
              event := event
              remaining := remaining
              split := rfl
              priorSafe := by intro priorEvent member; cases member }
            failure
      | .safe safe =>
          match classifyTerminalSaturationClosureRoutingEvents
              candidate model remaining with
          | .balanced allRemaining =>
              .balanced (by
                intro found member
                cases List.mem_cons.mp member with
                | inl equal => simpa [equal] using safe
                | inr tailMember => exact allRemaining found tailMember)
          | .interfaceExposure first route =>
              .interfaceExposure (first.prepend safe) route
          | .originKernelObligation first route =>
              .originKernelObligation (first.prepend safe) route
          | .otherNontransparent first failure =>
              .otherNontransparent (first.prepend safe) failure

/-- Run the exact-first composed router over the production saturation trace. -/
def classifyTerminalSaturationClosureRouting
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationClosureRoutingOutcome candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events :=
  classifyTerminalSaturationClosureRoutingEvents candidate model
    (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events

/-- Every finite candidate-derived trace has one exact composed outcome. -/
theorem classifyTerminalSaturationClosureRouting_exhaustive
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Nonempty (TerminalSaturationClosureRoutingOutcome candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events) :=
  ⟨classifyTerminalSaturationClosureRouting candidate model seed⟩

end DirectWire
end PNP
