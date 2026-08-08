/-
Copyright (c) 2026 PNP Labs.

Route-aware side-tight completion for the four canonical optimum realizers on
every finite computed terminal support square.  The route query is exactly the
previous deterministic first-failure query.  A routed failure therefore
retains its exact coordinate and sound mismatch evidence, while route silence
is computed rather than supplied by a caller.

This reconstructs the `sideTightCompletionExists` dependency in the
`BN2-CoherentOptimum` paragraph of Section 11.1 of the pinned manuscript at
the local coherence boundary: in either selected mode, the first local
coherence obstruction is routed or the canonical side-tight coherent tuple
exists.  The separate forgotten-coordinate query remains a quotient-to-full
promotion firewall.  This module does not connect a local obstruction to the
complete global CritC/Q/E/L/X, gain, exact, selector, or descent route system,
prove BN2 square legitimacy, derive the terminal dependency system, enumerate
and maximize the complete tight-basis family, or prove SaturatePositive,
BCELReady, ZeroSlack, PCCMin, polynomial runtime, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalFourCornerOptimumCoherence

namespace PNP
namespace DirectWire

/-- The two fail-closed route queries at the optimum-coherence boundary.
    Mode-appropriate coherence is distinct from quotient-to-full promotion. -/
inductive TerminalOptimumRoutePhase where
  | coherence (mode : TerminalOptimumCoherenceMode)
  | quotientPromotion
  deriving Repr, DecidableEq

/-- Execute the exact first route query for one phase.  The coherence phase
    uses the selected full or quotient discipline.  The promotion phase reads
    only the separate forgotten-coordinate firewall query. -/
def TerminalFourCornerCarrier.firstOptimumRoute?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    TerminalOptimumRoutePhase ->
      Option (TerminalFourCornerOptimumFailure
        (inputs + gates) gates profileWidth)
  | .coherence mode => carrier.firstOptimumCoherenceFailure? observe mode
  | .quotientPromotion => carrier.firstOptimumModeMismatch? observe

@[simp] theorem TerminalFourCornerCarrier.firstOptimumRoute?_coherence
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    carrier.firstOptimumRoute? observe (.coherence mode) =
      carrier.firstOptimumCoherenceFailure? observe mode :=
  rfl

@[simp] theorem TerminalFourCornerCarrier.firstOptimumRoute?_quotientPromotion
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    carrier.firstOptimumRoute? observe .quotientPromotion =
      carrier.firstOptimumModeMismatch? observe :=
  rfl

/-- A proof-bearing local route is tied to the exact executable first-route
    query.  Its failure coordinate and route phase cannot be chosen
    independently by a caller. -/
structure TerminalFourCornerOptimumRoutedFailure
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (phase : TerminalOptimumRoutePhase) where
  failure : TerminalFourCornerOptimumFailure
    (inputs + gates) gates profileWidth
  first : carrier.firstOptimumRoute? observe phase = some failure

/-- Every proof-bearing route contains a genuine mismatch or genuinely open
    obligation from the selected executable query. -/
theorem TerminalFourCornerOptimumRoutedFailure.sound
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth}
    {phase : TerminalOptimumRoutePhase}
    (route : TerminalFourCornerOptimumRoutedFailure carrier observe phase) :
    route.failure.Sound := by
  cases phase with
  | coherence mode =>
      exact carrier.firstOptimumCoherenceFailure?_sound observe mode
        route.failure route.first
  | quotientPromotion =>
      exact carrier.firstOptimumModeMismatch?_sound observe
        route.failure route.first

/-- Reify an exact returned failure as a proof-bearing local route. -/
def TerminalFourCornerCarrier.routedFailureOfFirst
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (phase : TerminalOptimumRoutePhase)
    (failure : TerminalFourCornerOptimumFailure
      (inputs + gates) gates profileWidth)
    (first : carrier.firstOptimumRoute? observe phase = some failure) :
    TerminalFourCornerOptimumRoutedFailure carrier observe phase :=
  ⟨failure, first⟩

/-- Route silence is the exact `none` result of the executable query. -/
def TerminalFourCornerCarrier.NoOptimumRoute
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (phase : TerminalOptimumRoutePhase) : Prop :=
  carrier.firstOptimumRoute? observe phase = none

/-- Mode-appropriate local coherence-route silence. -/
def TerminalFourCornerCarrier.NoOptimumCoherenceRoute
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) : Prop :=
  carrier.NoOptimumRoute observe (.coherence mode)

/-- Silence of the separate quotient-to-full promotion firewall. -/
def TerminalFourCornerCarrier.NoOptimumPromotionRoute
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) : Prop :=
  carrier.NoOptimumRoute observe .quotientPromotion

/-- Local coherence-route silence in both comparison modes. -/
def TerminalFourCornerCarrier.NoOptimumCoherenceRoutes
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) : Prop :=
  carrier.NoOptimumCoherenceRoute observe .full ∧
    carrier.NoOptimumCoherenceRoute observe .quotient

/-- The route-silence predicate is definitionally the previous exact
    no-failure query, not an additional certificate. -/
theorem TerminalFourCornerCarrier.noOptimumCoherenceRoute_iff_noFailure
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    carrier.NoOptimumCoherenceRoute observe mode ↔
      carrier.firstOptimumCoherenceFailure? observe mode = none :=
  Iff.rfl

/-- Promotion-route silence is exactly absence of a forgotten-coordinate
    mismatch.  It does not itself manufacture a checked full lift. -/
theorem TerminalFourCornerCarrier.noOptimumPromotionRoute_iff_noModeMismatch
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    carrier.NoOptimumPromotionRoute observe ↔
      carrier.firstOptimumModeMismatch? observe = none :=
  Iff.rfl

/-- Soundness of every result emitted by either exact route query. -/
theorem TerminalFourCornerCarrier.firstOptimumRoute?_sound
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (phase : TerminalOptimumRoutePhase)
    (failure : TerminalFourCornerOptimumFailure
      (inputs + gates) gates profileWidth)
    (first : carrier.firstOptimumRoute? observe phase = some failure) :
    failure.Sound :=
  (carrier.routedFailureOfFirst observe phase failure first).sound

/-- Every selected mode has either the complete checked side-tight tuple or
    its exact deterministic first local route. -/
theorem TerminalFourCornerCarrier.sideTightCompletionOrFirstRoute
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple carrier observe mode) ∨
      Nonempty (TerminalFourCornerOptimumRoutedFailure
        carrier observe (.coherence mode)) := by
  cases found : carrier.firstOptimumCoherenceFailure? observe mode with
  | none =>
      exact Or.inl <|
        (carrier.noFailure_iff_coherentOptimumTuple observe mode).1 found
  | some failure =>
      exact Or.inr ⟨⟨failure, found⟩⟩

/-- An actual local route and a checked coherent completion cannot coexist. -/
theorem TerminalFourCornerOptimumRoutedFailure.excludesCoherentOptimum
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth}
    {mode : TerminalOptimumCoherenceMode}
    (route : TerminalFourCornerOptimumRoutedFailure
      carrier observe (.coherence mode)) :
    ¬Nonempty (TerminalFourCornerCoherentOptimumTuple
      carrier observe mode) := by
  rintro ⟨tuple⟩
  have first := route.first
  rw [carrier.firstOptimumRoute?_coherence observe mode] at first
  rw [tuple.noFailure] at first
  cases first

/-- The manuscript's local `sideTightCompletionExists` edge: when the exact
    mode-appropriate route query is silent, the checked side-tight coherent
    optimum tuple exists. -/
theorem TerminalFourCornerCarrier.sideTightCompletionExists
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (noRoute : carrier.NoOptimumCoherenceRoute observe mode) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple carrier observe mode) :=
  (carrier.noFailure_iff_coherentOptimumTuple observe mode).1 noRoute

/-- Silence in both local comparison modes supplies a side-tight coherent
    completion in each mode, without promoting quotient evidence to full. -/
theorem TerminalFourCornerCarrier.sideTightCompletionExistsEachMode
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (noRoutes : carrier.NoOptimumCoherenceRoutes observe) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple
        carrier observe .full) ∧
      Nonempty (TerminalFourCornerCoherentOptimumTuple
        carrier observe .quotient) :=
  ⟨carrier.sideTightCompletionExists observe .full noRoutes.1,
    carrier.sideTightCompletionExists observe .quotient noRoutes.2⟩

/-- Full-mode route silence returns the exact full minimum incidence value. -/
theorem TerminalFourCornerCarrier.sideTightCompletion_fullValue
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (noRoute : carrier.NoOptimumCoherenceRoute observe .full) :
    (carrier.canonicalOptimumFamily observe).fullBasis.sizes.tightValue?
        (carrier.optimizationCorners observe).fullMinimumSizes =
      some (carrier.optimizationCorners observe).fullDelta := by
  obtain ⟨tuple⟩ := carrier.sideTightCompletionExists observe .full noRoute
  exact tuple.fullIncidenceValue

/-- Quotient-mode route silence returns the exact quotient minimum incidence
    value while retaining comparison-only mode discipline. -/
theorem TerminalFourCornerCarrier.sideTightCompletion_quotientValue
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (noRoute : carrier.NoOptimumCoherenceRoute observe .quotient) :
    (carrier.canonicalOptimumFamily observe).quotientBasis.sizes.tightValue?
        (carrier.optimizationCorners observe).quotientMinimumSizes =
      some (carrier.optimizationCorners observe).quotientDelta := by
  obtain ⟨tuple⟩ :=
    carrier.sideTightCompletionExists observe .quotient noRoute
  exact tuple.quotientIncidenceValue

end DirectWire
end PNP
