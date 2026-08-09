/-
Copyright (c) 2026 PNP Labs.

Computed terminal BN2 square legitimacy.  Every carrier in this module is
derived from two finite seeds, one explicit terminal dependency system, the
existing saturation and governed-completion procedures, and one forgetful
terminal projection.  The resulting proof object gathers the exact frontier
pushout with the already checked physical, profile, projection, and optimum
carrier transports.

This is the finite terminal reconstruction of the structural square boundary
used by the pinned manuscript's BN2 argument.  It does not derive the terminal
dependency system from an arbitrary circuit, identify a BCEL anchor square,
connect a local failure to the complete global no-outcome route system, prove
universal route silence, SaturatePositive, BCELReady, ZeroSlack, PCCMin,
polynomial runtime, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalFourCornerTightBasisMaximum

namespace PNP
namespace DirectWire

/-- Exact structural legitimacy of one finite computed terminal support
    square.  The carrier compatibility field covers all four governed and
    physically compatible corners, exact meet/join profile transport for all
    ten terminal roles, fail-closed physical transport, and projection
    commutation.  The separate frontier field retains the full governed
    pushout equation, including the exact shared meet profile. -/
structure TerminalComputedBN2SquareLegitimate
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system) : Prop where
  carrierCompatible : carrier.Compatible
  frontierPushout :
    (carrier.support .join).frontier =
        terminalGovernedFrontierPushout
          (carrier.support .left) (carrier.support .right) ∧
      ∀ role coordinate,
        coordinate ∈ (carrier.support .meet).profileCoordinates role ↔
          coordinate ∈ (carrier.support .left).profileCoordinates role ∧
            coordinate ∈
              (carrier.support .right).profileCoordinates role

/-- Every corner of a legitimate computed square is governed and physically
    compatible. -/
theorem TerminalComputedBN2SquareLegitimate.cornerCompatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (legitimate : TerminalComputedBN2SquareLegitimate carrier)
    (corner : TerminalSupportSquareCorner) :
    (carrier.support corner).Compatible :=
  legitimate.carrierCompatible.cornerCompatible corner

/-- The exact role-indexed meet transport is part of computed legitimacy. -/
theorem TerminalComputedBN2SquareLegitimate.meetProfile
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (legitimate : TerminalComputedBN2SquareLegitimate carrier)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (carrier.support .meet).frontier.profiles role ↔
      coordinate ∈ (carrier.support .left).frontier.profiles role ∧
        coordinate ∈ (carrier.support .right).frontier.profiles role :=
  legitimate.carrierCompatible.meetProfile role coordinate

/-- The exact role-indexed join transport is part of computed legitimacy. -/
theorem TerminalComputedBN2SquareLegitimate.joinProfile
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (legitimate : TerminalComputedBN2SquareLegitimate carrier)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (carrier.support .join).frontier.profiles role ↔
      coordinate ∈ (carrier.support .left).frontier.profiles role ∨
        coordinate ∈ (carrier.support .right).frontier.profiles role :=
  legitimate.carrierCompatible.joinProfile role coordinate

/-- The forgetful terminal projection commutes with the computed meet and
    join square. -/
theorem TerminalComputedBN2SquareLegitimate.projectionCompatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (legitimate : TerminalComputedBN2SquareLegitimate carrier) :
    carrier.square.ProjectionCompatible carrier.candidate carrier.projection :=
  legitimate.carrierCompatible.projectedSquare

/-- Every finite carrier constructed by the terminal support-square API has
    the complete computed BN2 structural boundary.  Callers supply neither
    corner lists nor a legitimacy certificate. -/
theorem TerminalFourCornerCarrier.computedBN2SquareLegitimate
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system) :
    TerminalComputedBN2SquareLegitimate carrier := by
  refine
    { carrierCompatible := carrier.complete_transport
      frontierPushout := ?_ }
  simpa only [TerminalFourCornerCarrier.support] using
    carrier.square.governed_frontier_pushout carrier.candidate

/-- All minimum and defect quantities for one computed square use the same
    observer, projection, and carrier-compatible four corners. -/
structure TerminalComputedBN2SquareQuantities
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth) : Prop where
  legitimate : TerminalComputedBN2SquareLegitimate carrier
  optimaCarrierCompatible :
    (carrier.canonicalOptimumFamily observe).Compatible

/-- The quantity package retains the exact shared terminal role map. -/
theorem TerminalComputedBN2SquareQuantities.sharedRole
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth}
    (quantities : TerminalComputedBN2SquareQuantities carrier observe)
    (coordinate : Fin profileWidth) :
    (carrier.optimizationCorners observe).system.role coordinate =
      system.profileSystem.role coordinate :=
  quantities.optimaCarrierCompatible.sharedRole coordinate

/-- The quantity package retains exactly the carrier's forgetful projection. -/
theorem TerminalComputedBN2SquareQuantities.sharedProjection
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth}
    (quantities : TerminalComputedBN2SquareQuantities carrier observe) :
    (carrier.optimizationCorners observe).projection = carrier.projection :=
  quantities.optimaCarrierCompatible.sharedProjection

/-- Ambientization preserves the semantic reference minimum at every corner
    represented by the quantity package. -/
theorem TerminalComputedBN2SquareQuantities.referenceMinimumPreserved
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth}
    (quantities : TerminalComputedBN2SquareQuantities carrier observe)
    (corner : TerminalSupportSquareCorner) :
    referenceMinimum (carrier.ambientImplementation corner) =
      referenceMinimum (carrier.cornerImplementation corner) :=
  quantities.optimaCarrierCompatible.semanticMinimumPreserved corner

/-- The signed projection-transfer identity is evaluated on the same computed
    four-corner quantity package. -/
theorem TerminalComputedBN2SquareQuantities.transferIdentity
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth}
    (_quantities : TerminalComputedBN2SquareQuantities carrier observe) :
    Int.ofNat (terminalProjectionDefect
        (carrier.optimizationCorners observe).system
        (carrier.optimizationCorners observe).projection
        (carrier.optimizationCorners observe).join) +
        Int.ofNat (terminalProjectionDefect
          (carrier.optimizationCorners observe).system
          (carrier.optimizationCorners observe).projection
          (carrier.optimizationCorners observe).meet) =
      Int.ofNat (terminalProjectionDefect
          (carrier.optimizationCorners observe).system
          (carrier.optimizationCorners observe).projection
          (carrier.optimizationCorners observe).left) +
        Int.ofNat (terminalProjectionDefect
          (carrier.optimizationCorners observe).system
          (carrier.optimizationCorners observe).projection
          (carrier.optimizationCorners observe).right) +
        (carrier.optimizationCorners observe).projectionExcess :=
  (carrier.optimizationCorners observe).transferIdentity

/-- Canonical carrier-compatible full and quotient quantities for every
    legitimate computed terminal square. -/
theorem TerminalFourCornerCarrier.computedBN2SquareQuantities
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth) :
    TerminalComputedBN2SquareQuantities carrier observe :=
  { legitimate := carrier.computedBN2SquareLegitimate
    optimaCarrierCompatible :=
      carrier.fourCornerOptimaCarrierCompatible observe }

/-- Complete local BN2 conclusion for one computed square.  The no-route
    premise is the exact result of the existing executable coherence queries
    in both comparison modes; it is not a global no-outcome certificate. -/
structure TerminalComputedBN2LocalConclusion
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth) : Prop where
  quantities : TerminalComputedBN2SquareQuantities carrier observe
  noRoutes : carrier.NoOptimumCoherenceRoutes observe
  fullTuple : Nonempty
    (TerminalFourCornerCoherentOptimumTuple carrier observe .full)
  quotientTuple : Nonempty
    (TerminalFourCornerCoherentOptimumTuple carrier observe .quotient)
  fullMaximum : carrier.tightBasisMaximum? observe .full =
    some (carrier.optimizationCorners observe).fullDelta
  quotientMaximum : carrier.tightBasisMaximum? observe .quotient =
    some (carrier.optimizationCorners observe).quotientDelta

/-- Exact local route silence assembles structural legitimacy, shared
    quantities, side-tight coherent optima, and the complete tight-family
    maxima in both modes. -/
theorem TerminalFourCornerCarrier.computedBN2LocalConclusion
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth)
    (noRoutes : carrier.NoOptimumCoherenceRoutes observe) :
    TerminalComputedBN2LocalConclusion carrier observe := by
  have completions :=
    carrier.sideTightCompletionExistsEachMode observe noRoutes
  exact
    { quantities := carrier.computedBN2SquareQuantities observe
      noRoutes := noRoutes
      fullTuple := completions.1
      quotientTuple := completions.2
      fullMaximum := carrier.tightBasisMaximum?_full observe noRoutes.1
      quotientMaximum :=
        carrier.tightBasisMaximum?_quotient observe noRoutes.2 }

/-- Fail-closed local BN2 boundary in deterministic full-then-quotient order:
    either both exact local queries are silent and the complete local result
    exists, or the first selected mode exposes its proof-bearing routed
    failure. -/
theorem TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates →
      TerminalProfile profileWidth) :
    Nonempty (TerminalComputedBN2LocalConclusion carrier observe) ∨
      Nonempty (TerminalFourCornerOptimumRoutedFailure
        carrier observe (.coherence .full)) ∨
      Nonempty (TerminalFourCornerOptimumRoutedFailure
        carrier observe (.coherence .quotient)) := by
  cases fullFound : carrier.firstOptimumCoherenceFailure? observe .full with
  | some failure =>
      exact Or.inr <| Or.inl <| ⟨⟨failure, by
        change carrier.firstOptimumCoherenceFailure? observe .full = some failure
        exact fullFound⟩⟩
  | none =>
      cases quotientFound :
          carrier.firstOptimumCoherenceFailure? observe .quotient with
      | some failure =>
          exact Or.inr <| Or.inr <| ⟨⟨failure, by
            change carrier.firstOptimumCoherenceFailure?
              observe .quotient = some failure
            exact quotientFound⟩⟩
      | none =>
          apply Or.inl
          refine ⟨carrier.computedBN2LocalConclusion observe ?_⟩
          constructor
          · change carrier.firstOptimumCoherenceFailure?
              observe .full = none
            exact fullFound
          · change carrier.firstOptimumCoherenceFailure?
              observe .quotient = none
            exact quotientFound

end DirectWire
end PNP
