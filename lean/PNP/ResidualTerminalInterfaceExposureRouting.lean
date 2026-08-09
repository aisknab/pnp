/-
Copyright (c) 2026 PNP Labs.

Proof-bearing local routing for candidate-derived terminal interface exposure.
The exact candidate-derived interface-consumer edge is recomputed from the
event; a caller cannot select an output, materializer, failure reason, or route.
Every recognized event is either transparently cost-balanced or returns a
local E-route containing the exact nontransparent evidence.  At trace level,
the route is additionally tied to the production classifier's deterministic
first nontransparent event and its complete transparent prefix.

This closes only the finite terminal form of `interfaceExposureRoutesToE`.
The E-route is an exposure-obligation coordinate, not a full Package E
`VerifyDW` acceptance or a verified global gain.  Origin, kernel, and
obligation closure routing, full `SaturatePositive`, `BCELReady`, global route
completeness, polynomial runtime, SAT in P, and P = NP remain open.
-/

import PNP.ResidualTerminalSaturationCostBalance

namespace PNP
namespace DirectWire

/-! ## Exact interface-exposure coordinates -/

/-- The three physical orientations of a candidate-derived interface edge.
    `outgoingCoordinate` adds the declared outgoing coordinate itself;
    `gateMaterializer` and `boundaryMaterializer` add the source required by an
    already present outgoing coordinate. -/
inductive TerminalInterfaceExposureCoordinate
    (inputs gates outputs : Nat) where
  | outgoingCoordinate (output : Fin outputs)
  | gateMaterializer (output : Fin outputs) (gate : Fin gates)
  | boundaryMaterializer (output : Fin outputs) (input : Fin inputs)
  deriving Repr, DecidableEq

/-- Read only the exact interface-event shape and its physical coordinate.
    Candidate-derived incidence is checked separately below. -/
def terminalInterfaceExposureCoordinate?
    {inputs gates outputs profileWidth : Nat}
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    Option (TerminalInterfaceExposureCoordinate inputs gates outputs) :=
  match event.kind?, event.dependent, event.required with
  | some .interfaceConsumer, _dependent, .interface output =>
      some (.outgoingCoordinate output)
  | some .interfaceConsumer, .interface output, .gate gate =>
      some (.gateMaterializer output gate)
  | some .interfaceConsumer, .interface output, .boundary input =>
      some (.boundaryMaterializer output input)
  | _, _, _ => none

/-- Semantic meaning of one exact interface-exposure coordinate. -/
def TerminalInterfaceExposureCoordinate.Matches
    {inputs gates outputs profileWidth : Nat}
    (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Prop :=
  event.kind? = some .interfaceConsumer ∧
    match coordinate with
    | .outgoingCoordinate output =>
        event.required = .interface output
    | .gateMaterializer output gate =>
        event.dependent = .interface output ∧ event.required = .gate gate
    | .boundaryMaterializer output input =>
        event.dependent = .interface output ∧ event.required = .boundary input

/-- The shape query cannot manufacture an interface coordinate. -/
theorem terminalInterfaceExposureCoordinate?_sound
    {inputs gates outputs profileWidth : Nat}
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
    (found : terminalInterfaceExposureCoordinate? event = some coordinate) :
    coordinate.Matches event := by
  cases kindAt : event.kind? with
  | none =>
      simp [terminalInterfaceExposureCoordinate?, kindAt] at found
  | some kind =>
      cases kind <;>
        cases dependentAt : event.dependent <;>
        cases requiredAt : event.required <;>
        simp [terminalInterfaceExposureCoordinate?,
          TerminalInterfaceExposureCoordinate.Matches,
          kindAt, dependentAt, requiredAt] at found ⊢ <;>
        cases found <;> simp

/-- Recompute the candidate-derived edge before recognizing an exposure.  A
    shape with no actual interface-consumer dependency fails closed to `none`. -/
def terminalCandidateInterfaceExposureCoordinate?
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    Option (TerminalInterfaceExposureCoordinate inputs gates outputs) :=
  match terminalInterfaceExposureCoordinate? event with
  | none => none
  | some coordinate =>
      if (terminalCandidateSaturationSystem candidate model).requires
          .interfaceConsumer event.dependent event.required = true then
        some coordinate
      else
        none

/-- A returned production coordinate has the exact interface-event shape. -/
theorem terminalCandidateInterfaceExposureCoordinate?_shape
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
    (found : terminalCandidateInterfaceExposureCoordinate?
      candidate model event = some coordinate) :
    terminalInterfaceExposureCoordinate? event = some coordinate := by
  unfold terminalCandidateInterfaceExposureCoordinate? at found
  cases shapeAt : terminalInterfaceExposureCoordinate? event with
  | none => simp [shapeAt] at found
  | some shaped =>
      simp only [shapeAt] at found
      split at found
      next _edge =>
        exact found
      next _noEdge => cases found

/-- A returned production coordinate is backed by the recomputed
    candidate-derived interface-consumer edge. -/
theorem terminalCandidateInterfaceExposureCoordinate?_edge
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
    (found : terminalCandidateInterfaceExposureCoordinate?
      candidate model event = some coordinate) :
    (terminalCandidateSaturationSystem candidate model).requires
      .interfaceConsumer event.dependent event.required = true := by
  unfold terminalCandidateInterfaceExposureCoordinate? at found
  cases shapeAt : terminalInterfaceExposureCoordinate? event with
  | none => simp [shapeAt] at found
  | some shaped =>
      simp only [shapeAt] at found
      split at found
      next edge => exact edge
      next _noEdge => cases found

/-- Adding an outgoing-coordinate record itself has zero physical event cost. -/
theorem terminalInterfaceOutgoingCoordinate_eventCost_zero
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (output : Fin outputs)
    (found : terminalCandidateInterfaceExposureCoordinate?
      candidate model event = some (.outgoingCoordinate output)) :
    terminalSaturationEventCost event = 0 := by
  have shape := terminalInterfaceExposureCoordinate?_sound event
    (.outgoingCoordinate output)
    (terminalCandidateInterfaceExposureCoordinate?_shape
      candidate model event (.outgoingCoordinate output) found)
  unfold terminalSaturationEventCost
  rw [shape.2]

/-! ## Step-level transparent-or-E routing -/

/-- A proof-bearing local E-route for one exact interface exposure.  The route
    contains both the candidate-derived coordinate query and the exact reason
    returned by the pre-existing balance classifier. -/
structure TerminalInterfaceExposureERoute
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs
  selected : terminalCandidateInterfaceExposureCoordinate?
    candidate model event = some coordinate
  reason : TerminalNontransparentSaturationReason
  reasonSelected : terminalSaturationStepFailureReason?
    candidate model event = some reason
  failure : ¬TerminalTransparentSaturationStep candidate model event

/-- Exact soundness proposition of a local interface E-route. -/
def TerminalInterfaceExposureERoute.Sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (route : TerminalInterfaceExposureERoute candidate model event) : Prop :=
  route.coordinate.Matches event ∧
    (terminalCandidateSaturationSystem candidate model).requires
      .interfaceConsumer event.dependent event.required = true ∧
    terminalSaturationStepFailureReason? candidate model event =
      some route.reason ∧
    ¬TerminalTransparentSaturationStep candidate model event

/-- Every local E-route contains a genuine candidate-derived interface edge
    and the exact nontransparent result. -/
theorem TerminalInterfaceExposureERoute.sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (route : TerminalInterfaceExposureERoute candidate model event) :
    route.Sound :=
  ⟨terminalInterfaceExposureCoordinate?_sound event route.coordinate
      (terminalCandidateInterfaceExposureCoordinate?_shape
        candidate model event route.coordinate route.selected),
    terminalCandidateInterfaceExposureCoordinate?_edge
      candidate model event route.coordinate route.selected,
    route.reasonSelected,
    route.failure⟩

/-- A transparent outgoing-coordinate exposure is the manuscript's finite
    zero-cost retract branch. -/
structure TerminalInterfaceExposureZeroCostRetract
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  output : Fin outputs
  selected : terminalCandidateInterfaceExposureCoordinate?
    candidate model event = some (.outgoingCoordinate output)
  transparent : TerminalTransparentSaturationStep candidate model event

theorem TerminalInterfaceExposureZeroCostRetract.eventCost_zero
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (retract : TerminalInterfaceExposureZeroCostRetract
      candidate model event) :
    terminalSaturationEventCost event = 0 :=
  terminalInterfaceOutgoingCoordinate_eventCost_zero
    candidate model event retract.output retract.selected

theorem TerminalInterfaceExposureZeroCostRetract.fullSlack_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (retract : TerminalInterfaceExposureZeroCostRetract
      candidate model event) :
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).fullSlack =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullSlack :=
  retract.transparent.fullSlack_preserved

/-- Total fail-closed classification at one possible interface-exposure step. -/
inductive TerminalInterfaceExposureStepOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  | notInterface
      (notSelected : terminalCandidateInterfaceExposureCoordinate?
        candidate model event = none)
  | transparent
      (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
      (selected : terminalCandidateInterfaceExposureCoordinate?
        candidate model event = some coordinate)
      (evidence : TerminalTransparentSaturationStep candidate model event)
  | eRoute (route : TerminalInterfaceExposureERoute candidate model event)

/-- Recompute interface incidence and the existing balance classifier. -/
def classifyTerminalInterfaceExposureStep
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    TerminalInterfaceExposureStepOutcome candidate model event :=
  match selected : terminalCandidateInterfaceExposureCoordinate?
      candidate model event with
  | none => .notInterface selected
  | some coordinate =>
      match classified : classifyTerminalSaturationStepBalance
          candidate model event with
      | .transparent evidence => .transparent coordinate selected evidence
      | .nontransparent reason failure =>
          .eRoute
            { coordinate := coordinate
              selected := selected
              reason := reason
              reasonSelected := by
                simp [terminalSaturationStepFailureReason?, classified]
              failure := failure }

/-- Boolean projection used by executable regression and downstream dispatch. -/
def terminalInterfaceExposureStepRoutedBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Bool :=
  match classifyTerminalInterfaceExposureStep candidate model event with
  | .eRoute _route => true
  | _ => false

/-- Every recognized interface exposure is transparently balanced or produces
    a proof-bearing local E-route; there is no caller-selected third branch. -/
theorem terminalInterfaceExposure_transparent_or_eRoute
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs)
    (selected : terminalCandidateInterfaceExposureCoordinate?
      candidate model event = some coordinate) :
    TerminalTransparentSaturationStep candidate model event ∨
      Nonempty (TerminalInterfaceExposureERoute candidate model event) := by
  cases outcomeAt : classifyTerminalInterfaceExposureStep
      candidate model event with
  | notInterface notSelected =>
      rw [selected] at notSelected
      cases notSelected
  | transparent _coordinate _selected evidence => exact Or.inl evidence
  | eRoute route => exact Or.inr ⟨route⟩

/-! ## Deterministic trace-level first route -/

/-- Exact first nontransparent interface route from the production trace. -/
structure TerminalFirstInterfaceExposureRoute
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  failure : TerminalFirstNontransparentSaturationStep candidate model
    (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events
  coordinate : TerminalInterfaceExposureCoordinate inputs gates outputs
  selected : terminalCandidateInterfaceExposureCoordinate?
    candidate model failure.event = some coordinate
  first : classifyTerminalSaturationBalance candidate model seed =
    .firstNontransparent failure

/-- Soundness includes exact trace split, transparent prefix, candidate-derived
    interface incidence, and the genuine nontransparent step. -/
def TerminalFirstInterfaceExposureRoute.Sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (route : TerminalFirstInterfaceExposureRoute candidate model seed) : Prop :=
  (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events =
      route.failure.prior ++ route.failure.event :: route.failure.remaining ∧
    route.coordinate.Matches route.failure.event ∧
    (terminalCandidateSaturationSystem candidate model).requires
      .interfaceConsumer route.failure.event.dependent
        route.failure.event.required = true ∧
    (∀ event, event ∈ route.failure.prior →
      TerminalTransparentSaturationStep candidate model event) ∧
    ¬TerminalTransparentSaturationStep candidate model route.failure.event ∧
    classifyTerminalSaturationBalance candidate model seed =
      .firstNontransparent route.failure

/-- Every trace-level E-route is tied to the exact production first failure. -/
theorem TerminalFirstInterfaceExposureRoute.sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (route : TerminalFirstInterfaceExposureRoute candidate model seed) :
    route.Sound :=
  ⟨route.failure.split,
    terminalInterfaceExposureCoordinate?_sound
      route.failure.event route.coordinate
      (terminalCandidateInterfaceExposureCoordinate?_shape
        candidate model route.failure.event route.coordinate route.selected),
    terminalCandidateInterfaceExposureCoordinate?_edge
      candidate model route.failure.event route.coordinate route.selected,
    route.failure.priorTransparent,
    route.failure.failure,
    route.first⟩

/-- A non-interface first failure is retained exactly rather than being
    mislabeled as an E-route. -/
structure TerminalFirstNoninterfaceSaturationFailure
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  failure : TerminalFirstNontransparentSaturationStep candidate model
    (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events
  first : classifyTerminalSaturationBalance candidate model seed =
    .firstNontransparent failure
  notInterface : terminalCandidateInterfaceExposureCoordinate?
    candidate model failure.event = none

/-- Total production-trace interface-routing outcome. -/
inductive TerminalSaturationInterfaceRoutingOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  | balanced
      (allTransparent : ∀ event,
        event ∈ (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).events →
        TerminalTransparentSaturationStep candidate model event)
  | interfaceExposure
      (route : TerminalFirstInterfaceExposureRoute candidate model seed)
  | otherNontransparent
      (failure : TerminalFirstNoninterfaceSaturationFailure
        candidate model seed)

/-- Route only the exact first production failure, preserving fail-closed
    fallback for every non-interface failure. -/
def classifyTerminalSaturationInterfaceRouting
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationInterfaceRoutingOutcome candidate model seed :=
  match classified : classifyTerminalSaturationBalance candidate model seed with
  | .balanced allTransparent => .balanced allTransparent
  | .firstNontransparent failure =>
      match selected : terminalCandidateInterfaceExposureCoordinate?
          candidate model failure.event with
      | some coordinate =>
          .interfaceExposure
            { failure := failure
              coordinate := coordinate
              selected := selected
              first := classified }
      | none =>
          .otherNontransparent
            { failure := failure
              first := classified
              notInterface := selected }

/-- Boolean projection of the exact trace-level E-route branch. -/
def terminalSaturationInterfaceERoutedBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  match classifyTerminalSaturationInterfaceRouting candidate model seed with
  | .interfaceExposure _route => true
  | _ => false

/-- Boolean projection of the balanced branch. -/
def terminalSaturationInterfaceBalancedBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  match classifyTerminalSaturationInterfaceRouting candidate model seed with
  | .balanced _allTransparent => true
  | _ => false

/-- Boolean projection of the fail-closed non-interface branch. -/
def terminalSaturationInterfaceOtherNontransparentBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  match classifyTerminalSaturationInterfaceRouting candidate model seed with
  | .otherNontransparent _failure => true
  | _ => false

/-- Every finite candidate-derived trace has one exact routing outcome. -/
theorem classifyTerminalSaturationInterfaceRouting_exhaustive
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Nonempty (TerminalSaturationInterfaceRoutingOutcome candidate model seed) :=
  ⟨classifyTerminalSaturationInterfaceRouting candidate model seed⟩

end DirectWire
end PNP
