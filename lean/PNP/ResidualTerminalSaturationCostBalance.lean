/-
Copyright (c) 2026 PNP Labs.

Computed transparent-cost accounting for candidate-derived terminal
saturation.  Every rule-labelled event is measured in one common ambient
carrier using the existing exhaustive full and quotient profile minima.
Metadata-only completion is zero-cost.  A physical gate is transparent only
when it has one active derived owner, adds exactly one support gate and one
forced full-mode minimum gate, and adds no more than one quotient gate.

The classifier accepts no caller balance proof or branch selector.  It returns
proof-bearing transparent evidence or records the exact first nontransparent
event and the complete transparent prefix.  This closes the finite terminal
forms of `transparentSaturationCostBalanced` and
`firstNontransparentStepRecorded`.  It does not route interface, origin,
kernel, or obligation failures, prove full `SaturatePositive` or `BCELReady`,
or claim polynomial runtime, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalCandidateSaturation

namespace PNP
namespace DirectWire

/-! ## Exact support and minimum snapshots -/

/-- Exact cost data for one finite terminal record family. -/
structure TerminalSaturationCostSnapshot
    (inputs gates outputs profileWidth : Nat) where
  records : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  supportSize : Nat
  fullMinimum : Nat
  quotientMinimum : Nat
  fullSlack : Nat
  projectionDefect : Nat
  deriving Repr, DecidableEq

/-- Recompute every cost coordinate from the candidate, observer, and
    projection. -/
def terminalSaturationCostSnapshot
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (records : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationCostSnapshot inputs gates outputs profileWidth :=
  let current := terminalAmbientSupportImplementation candidate records
  let system := model.ambientProfileSystem
  let supportSize := current.gateCount
  let fullMinimum := terminalFullProfileMinimum system current
  let quotientMinimum :=
    terminalQuotientProfileMinimum system model.projection current
  { records := records
    supportSize := supportSize
    fullMinimum := fullMinimum
    quotientMinimum := quotientMinimum
    fullSlack := supportSize - fullMinimum
    projectionDefect := fullMinimum - quotientMinimum }

/-- A newly processed gate carries unit physical cost; every other primitive
    record is metadata-only in the direct-wire support extractor. -/
def terminalSaturationEventCost
    {inputs gates outputs profileWidth : Nat}
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Nat :=
  match event.required with
  | .gate _index => 1
  | _ => 0

/-! ## Derived ownership and transparent events -/

/-- Every active rule/dependent pair that could have generated one required
    record from the event's before-support. -/
def terminalSaturationEventOwners
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    List (TerminalSaturationRuleKind ×
      TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  event.beforeRecords.flatMap fun dependent =>
    allTerminalSaturationRuleKinds.filterMap fun kind =>
      if system.requires kind dependent event.required = true then
        some (kind, dependent)
      else
        none

/-- Proof-bearing exact transparent-step contract.  The evidence is produced
    by the total classifier below; it is never accepted as an input to the
    production saturation path. -/
def TerminalTransparentSaturationStep
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Prop :=
  event.kind? ≠ none ∧
    (match event.required with
    | .gate _index =>
        (terminalSaturationEventOwners
          (terminalCandidateSaturationSystem candidate model) event).length = 1
    | _ => True) ∧
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).supportSize =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).supportSize + terminalSaturationEventCost event ∧
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).fullMinimum =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullMinimum + terminalSaturationEventCost event ∧
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).quotientMinimum ≤
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).quotientMinimum + terminalSaturationEventCost event

theorem TerminalTransparentSaturationStep.rulePresent
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    event.kind? ≠ none :=
  transparent.1

theorem TerminalTransparentSaturationStep.uniqueMaterializerOwner
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    match event.required with
    | .gate _index =>
        (terminalSaturationEventOwners
          (terminalCandidateSaturationSystem candidate model) event).length = 1
    | _ => True :=
  transparent.2.1

theorem TerminalTransparentSaturationStep.supportCostBalanced
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).supportSize =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).supportSize + terminalSaturationEventCost event :=
  transparent.2.2.1

theorem TerminalTransparentSaturationStep.fullCostBalanced
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).fullMinimum =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullMinimum + terminalSaturationEventCost event :=
  transparent.2.2.2.1

theorem TerminalTransparentSaturationStep.quotientCostBounded
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).quotientMinimum ≤
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).quotientMinimum + terminalSaturationEventCost event :=
  transparent.2.2.2.2

private def terminalTransparentSaturationStepDecidable
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    Decidable (TerminalTransparentSaturationStep candidate model event) := by
  unfold TerminalTransparentSaturationStep
  split <;> infer_instance

/-- Equal support and full-mode charges preserve the exact full slack. -/
theorem TerminalTransparentSaturationStep.fullSlack_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).fullSlack =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullSlack := by
  change
    (terminalSaturationCostSnapshot candidate model
        event.afterRecords).supportSize -
        (terminalSaturationCostSnapshot candidate model
          event.afterRecords).fullMinimum =
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).supportSize -
        (terminalSaturationCostSnapshot candidate model
          event.beforeRecords).fullMinimum
  rw [transparent.supportCostBalanced, transparent.fullCostBalanced]
  exact Nat.add_sub_add_right _ _ _

/-- Quotient cost growing no faster than the balanced full charge makes the
    projection defect nondecreasing. -/
theorem TerminalTransparentSaturationStep.projectionDefect_mono
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).projectionDefect ≤
      (terminalSaturationCostSnapshot candidate model
        event.afterRecords).projectionDefect := by
  change
    (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullMinimum -
        (terminalSaturationCostSnapshot candidate model
          event.beforeRecords).quotientMinimum ≤
      (terminalSaturationCostSnapshot candidate model
        event.afterRecords).fullMinimum -
      (terminalSaturationCostSnapshot candidate model
          event.afterRecords).quotientMinimum
  calc
    (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullMinimum -
        (terminalSaturationCostSnapshot candidate model
          event.beforeRecords).quotientMinimum =
      ((terminalSaturationCostSnapshot candidate model
          event.beforeRecords).fullMinimum + terminalSaturationEventCost event) -
        ((terminalSaturationCostSnapshot candidate model
          event.beforeRecords).quotientMinimum + terminalSaturationEventCost event) :=
      (Nat.add_sub_add_right _ _ _).symm
    _ ≤ ((terminalSaturationCostSnapshot candidate model
          event.beforeRecords).fullMinimum + terminalSaturationEventCost event) -
        (terminalSaturationCostSnapshot candidate model
          event.afterRecords).quotientMinimum :=
      Nat.sub_le_sub_left transparent.quotientCostBounded _
    _ = (terminalSaturationCostSnapshot candidate model
          event.afterRecords).fullMinimum -
        (terminalSaturationCostSnapshot candidate model
          event.afterRecords).quotientMinimum := by
      rw [transparent.fullCostBalanced]

/-- In particular, positive full slack cannot disappear across a transparent
    event. -/
theorem TerminalTransparentSaturationStep.fullPositive_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth}
    (transparent : TerminalTransparentSaturationStep candidate model event)
    (positive : 0 < (terminalSaturationCostSnapshot candidate model
      event.beforeRecords).fullSlack) :
    0 < (terminalSaturationCostSnapshot candidate model
      event.afterRecords).fullSlack := by
  rw [transparent.fullSlack_preserved]
  exact positive

/-! ## Aggregate transparent histories -/

/-- A linked history of transparent events preserves the initial full slack
    exactly at its replayed final support. -/
theorem TerminalSaturationEventsLinked.fullSlack_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {initial final : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)}
    (linked : TerminalSaturationEventsLinked initial events final)
    (allTransparent : ∀ event, event ∈ events →
      TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model final).fullSlack =
      (terminalSaturationCostSnapshot candidate model initial).fullSlack := by
  induction linked with
  | nil => rfl
  | @snoc events event linked ih =>
      have eventTransparent :
          TerminalTransparentSaturationStep candidate model event :=
        allTransparent event (List.mem_append_right events (List.Mem.head []))
      have priorTransparent : ∀ priorEvent, priorEvent ∈ events →
          TerminalTransparentSaturationStep candidate model priorEvent := by
        intro priorEvent member
        exact allTransparent priorEvent (List.mem_append_left [event] member)
      calc
        (terminalSaturationCostSnapshot candidate model
            event.afterRecords).fullSlack =
            (terminalSaturationCostSnapshot candidate model
              event.beforeRecords).fullSlack :=
          eventTransparent.fullSlack_preserved
        _ = (terminalSaturationCostSnapshot candidate model
              initial).fullSlack := ih priorTransparent

/-- Along a linked transparent history, quotient savings relative to the full
    minimum can only grow. -/
theorem TerminalSaturationEventsLinked.projectionDefect_mono
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {initial final : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)}
    (linked : TerminalSaturationEventsLinked initial events final)
    (allTransparent : ∀ event, event ∈ events →
      TerminalTransparentSaturationStep candidate model event) :
    (terminalSaturationCostSnapshot candidate model initial).projectionDefect ≤
      (terminalSaturationCostSnapshot candidate model final).projectionDefect := by
  induction linked with
  | nil => exact Nat.le_refl _
  | @snoc events event linked ih =>
      have eventTransparent :
          TerminalTransparentSaturationStep candidate model event :=
        allTransparent event (List.mem_append_right events (List.Mem.head []))
      have priorTransparent : ∀ priorEvent, priorEvent ∈ events →
          TerminalTransparentSaturationStep candidate model priorEvent := by
        intro priorEvent member
        exact allTransparent priorEvent (List.mem_append_left [event] member)
      exact Nat.le_trans (ih priorTransparent)
        eventTransparent.projectionDefect_mono

/-- Positive full slack at the normalized seed survives an entirely
    transparent linked history. -/
theorem TerminalSaturationEventsLinked.fullPositive_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {initial final : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)}
    (linked : TerminalSaturationEventsLinked initial events final)
    (allTransparent : ∀ event, event ∈ events →
      TerminalTransparentSaturationStep candidate model event)
    (positive : 0 < (terminalSaturationCostSnapshot candidate model
      initial).fullSlack) :
    0 < (terminalSaturationCostSnapshot candidate model final).fullSlack := by
  rw [linked.fullSlack_preserved allTransparent]
  exact positive

/-! ## Total step classifier -/

/-- Exact fail-closed reason for a step that is not transparent. -/
inductive TerminalNontransparentSaturationReason where
  | missingRule
  | nonuniqueMaterializerOwner
  | supportCostMismatch
  | fullCostMismatch
  | quotientCostExceeded
  deriving Repr, DecidableEq

private def terminalNontransparentSaturationReason
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    TerminalNontransparentSaturationReason :=
  if event.kind? = none then
    .missingRule
  else if !(match event.required with
      | .gate _index => decide
          ((terminalSaturationEventOwners
            (terminalCandidateSaturationSystem candidate model) event).length = 1)
      | _ => true) then
    .nonuniqueMaterializerOwner
  else if (terminalSaturationCostSnapshot candidate model
      event.afterRecords).supportSize ≠
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).supportSize + terminalSaturationEventCost event then
    .supportCostMismatch
  else if (terminalSaturationCostSnapshot candidate model
      event.afterRecords).fullMinimum ≠
      (terminalSaturationCostSnapshot candidate model
        event.beforeRecords).fullMinimum + terminalSaturationEventCost event then
    .fullCostMismatch
  else
    .quotientCostExceeded

/-- Total proof-bearing classification of one rule-labelled event. -/
inductive TerminalSaturationStepBalanceOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) where
  | transparent
      (evidence : TerminalTransparentSaturationStep candidate model event)
  | nontransparent
      (reason : TerminalNontransparentSaturationReason)
      (failure : ¬TerminalTransparentSaturationStep candidate model event)

/-- Compute every transparency premise; a failed premise returns a typed
    reason rather than being accepted silently. -/
def classifyTerminalSaturationStepBalance
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    TerminalSaturationStepBalanceOutcome candidate model event :=
  letI := terminalTransparentSaturationStepDecidable candidate model event
  if transparent : TerminalTransparentSaturationStep candidate model event then
    .transparent transparent
  else
    .nontransparent
      (terminalNontransparentSaturationReason candidate model event)
      transparent

/-- Boolean projection of the proof-bearing step classifier, for executable
    regression and downstream fail-closed dispatch. -/
def terminalSaturationStepTransparentBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) : Bool :=
  match classifyTerminalSaturationStepBalance candidate model event with
  | .transparent _evidence => true
  | .nontransparent _reason _failure => false

/-- The exact nontransparent reason, when the step classifier rejects. -/
def terminalSaturationStepFailureReason?
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth) :
    Option TerminalNontransparentSaturationReason :=
  match classifyTerminalSaturationStepBalance candidate model event with
  | .transparent _evidence => none
  | .nontransparent reason _failure => some reason

/-! ## Deterministic first nontransparent event -/

/-- Exact split around the first nontransparent event. -/
structure TerminalFirstNontransparentSaturationStep
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
  priorTransparent : ∀ priorEvent, priorEvent ∈ prior →
    TerminalTransparentSaturationStep candidate model priorEvent
  reason : TerminalNontransparentSaturationReason
  failure : ¬TerminalTransparentSaturationStep candidate model event

/-- Total classification of a complete event list. -/
inductive TerminalSaturationBalanceOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)) where
  | balanced
      (allTransparent : ∀ event, event ∈ events →
        TerminalTransparentSaturationStep candidate model event)
  | firstNontransparent
      (failure : TerminalFirstNontransparentSaturationStep
        candidate model events)

private def classifyTerminalSaturationBalanceEvents
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)) →
      TerminalSaturationBalanceOutcome candidate model events
  | [] => .balanced (by intro event member; cases member)
  | event :: remaining =>
      match classifyTerminalSaturationStepBalance candidate model event with
      | .nontransparent reason failure =>
          .firstNontransparent
            { prior := []
              event := event
              remaining := remaining
              split := rfl
              priorTransparent := by intro priorEvent member; cases member
              reason := reason
              failure := failure }
      | .transparent evidence =>
          match classifyTerminalSaturationBalanceEvents
              candidate model remaining with
          | .balanced allRemaining =>
              .balanced (by
                intro found member
                cases List.mem_cons.mp member with
                | inl equal => simpa [equal] using evidence
                | inr tailMember => exact allRemaining found tailMember)
          | .firstNontransparent first =>
              .firstNontransparent
                { prior := event :: first.prior
                  event := first.event
                  remaining := first.remaining
                  split := by
                    exact congrArg (fun tail => event :: tail) first.split
                  priorTransparent := by
                    intro priorEvent member
                    cases List.mem_cons.mp member with
                    | inl equal => simpa [equal] using evidence
                    | inr tailMember =>
                        exact first.priorTransparent priorEvent tailMember
                  reason := first.reason
                  failure := first.failure }

/-- Run the balance audit over the exact candidate-derived saturation trace. -/
def classifyTerminalSaturationBalance
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturationBalanceOutcome candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events :=
  classifyTerminalSaturationBalanceEvents candidate model
    (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events

/-- Boolean projection of the complete proof-bearing trace classifier. -/
def terminalSaturationBalanceBalancedBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  match classifyTerminalSaturationBalance candidate model seed with
  | .balanced _allTransparent => true
  | .firstNontransparent _failure => false

/-- Exact required record and reason at the first nontransparent event. -/
def terminalSaturationBalanceFirstFailure?
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Option (TerminalPrimitiveRecord inputs gates outputs profileWidth ×
      TerminalNontransparentSaturationReason) :=
  match classifyTerminalSaturationBalance candidate model seed with
  | .balanced _allTransparent => none
  | .firstNontransparent failure =>
      some (failure.event.required, failure.reason)

/-- A balanced result certifies every deterministic event, so the pointwise
    full-slack and projection-defect theorems apply throughout the trace. -/
theorem TerminalSaturationBalanceOutcome.balanced_event
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {events : List (TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)}
    {allTransparent : ∀ event, event ∈ events →
      TerminalTransparentSaturationStep candidate model event}
    (event : TerminalSaturationTraceEvent
      inputs gates outputs profileWidth)
    (member : event ∈ events) :
    TerminalTransparentSaturationStep candidate model event :=
  allTransparent event member

/-- The balanced branch of the production classifier preserves exact full
    slack from the normalized seed to the replayed final support. -/
theorem TerminalSaturationBalanceOutcome.balanced_fullSlack_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {allTransparent : ∀ event,
      event ∈ (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events →
      TerminalTransparentSaturationStep candidate model event} :
    (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        seed).replayRecords).fullSlack =
    (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        seed).normalizedSeed.reverse).fullSlack :=
  (terminalSaturateTrace_eventsLinked
    (terminalCandidateSaturationSystem candidate model) seed).fullSlack_preserved
      allTransparent

/-- The same balanced branch makes projection defect nondecreasing over the
    complete replayed trace. -/
theorem TerminalSaturationBalanceOutcome.balanced_projectionDefect_mono
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {allTransparent : ∀ event,
      event ∈ (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events →
      TerminalTransparentSaturationStep candidate model event} :
    (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        seed).normalizedSeed.reverse).projectionDefect ≤
    (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        seed).replayRecords).projectionDefect :=
  (terminalSaturateTrace_eventsLinked
    (terminalCandidateSaturationSystem candidate model) seed).projectionDefect_mono
      allTransparent

/-- Positive initial full slack therefore survives every balanced production
    trace. -/
theorem TerminalSaturationBalanceOutcome.balanced_fullPositive_preserved
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {allTransparent : ∀ event,
      event ∈ (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events →
      TerminalTransparentSaturationStep candidate model event}
    (positive : 0 < (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        seed).normalizedSeed.reverse).fullSlack) :
    0 < (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        seed).replayRecords).fullSlack :=
  (terminalSaturateTrace_eventsLinked
    (terminalCandidateSaturationSystem candidate model) seed).fullPositive_preserved
      allTransparent positive

end DirectWire
end PNP
