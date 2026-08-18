/-
Copyright (c) 2026 PNP Labs.

BN5-bound frontier and obligation reflection for the Packet
selector-faithfulness payload. The complete BN5 shadow coordinate already
retains typed frontier and obligation fields. This module compares those
fields directly instead of accepting independent `frontierChecked` and
`obligationChecked` Booleans at the active canonical-payload interface.

The construction is uniform over arbitrary finite grouped BN6 families,
finite rank carriers, and all BN5 coordinate-field types. It retains computed
grouped-footprint colour, positive source charge, the canonical source route,
the table-owned rank, and exact ten-coordinate residual descent. A returned
frontier or obligation route therefore carries inequality of the corresponding
typed BN5 field.

Both complete BN5 coordinates, the grouped family, rank map, residual ranks,
realizer claims, blocker activity, and dependency rows remain explicit inputs.
This module does not construct those coordinates from terminal data, prove a
BN5 matching edge, derive the grouped family, or discharge external full-mode
obligations. Activation, direction, and budget remain explicit Booleans. It
does not establish complete route silence, unconditional HB negative closure,
ZeroSlack, PCCMin, polynomial runtime, SAT in P, remove a project assumption,
or prove P = NP.
-/

import PNP.ResidualTerminalPacketFrontierRouteReflection
import PNP.ResidualTerminalBN5FullShadowLocalization

namespace PNP
namespace DirectWire

/-! ## BN5-bound Packet payload -/

/-- The complete typed BN5 coordinate used on both sides of the Packet
    selector comparison. -/
abbrev TerminalPacketSelectorBN5Coordinate
    (ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type) :=
  TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature TransportType
    Frontier ChargeOwner Obligation OriginKernel ModeProjection

/-- One selected positive Packet payload together with its source and selector
    BN5 coordinates. -/
structure TerminalPacketSelectorBN5ObligationPayload
    (rankCount : Nat)
    (ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type) where
  checks : TerminalPacketSelectorFaithfulnessPayload rankCount
  sourceCoordinate : TerminalPacketSelectorBN5Coordinate ActivationAtom
    SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection
  selectorCoordinate : TerminalPacketSelectorBN5Coordinate ActivationAtom
    SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection : Type}
variable [DecidableEq Anchor]

/-- Project the existing typed-frontier payload from the two complete BN5
    coordinates. -/
def TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier
    {rankCount : Nat}
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    TerminalPacketSelectorTypedFrontierPayload rankCount Frontier :=
  { checks := payload.checks
    sourceFrontier := payload.sourceCoordinate.frontier
    selectorFrontier := payload.selectorCoordinate.frontier }

/-- Executable equality of the BN5 frontier fields. -/
def TerminalPacketSelectorBN5ObligationPayload.frontierCheck
    {rankCount : Nat} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) : Bool :=
  payload.toTypedFrontier.frontierCheck

/-- Executable equality of the BN5 obligation fields. -/
def TerminalPacketSelectorBN5ObligationPayload.obligationCheck
    {rankCount : Nat} [DecidableEq Obligation]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) : Bool :=
  decide
    (payload.sourceCoordinate.obligation =
      payload.selectorCoordinate.obligation)

/-- Frontier acceptance is exactly equality of the two BN5 frontier fields. -/
theorem TerminalPacketSelectorBN5ObligationPayload.frontierCheck_eq_true_iff
    {rankCount : Nat} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.frontierCheck = true ↔
      payload.sourceCoordinate.frontier =
        payload.selectorCoordinate.frontier := by
  simpa [TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier] using
    (TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_true_iff
      payload.toTypedFrontier)

/-- Frontier rejection is exactly inequality of the two BN5 frontier fields. -/
theorem TerminalPacketSelectorBN5ObligationPayload.frontierCheck_eq_false_iff
    {rankCount : Nat} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.frontierCheck = false ↔
      payload.sourceCoordinate.frontier ≠
        payload.selectorCoordinate.frontier := by
  simpa [TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier] using
    (TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_false_iff
      payload.toTypedFrontier)

/-- Obligation acceptance is exactly equality of the two BN5 obligation
    fields. -/
theorem TerminalPacketSelectorBN5ObligationPayload.obligationCheck_eq_true_iff
    {rankCount : Nat} [DecidableEq Obligation]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.obligationCheck = true ↔
      payload.sourceCoordinate.obligation =
        payload.selectorCoordinate.obligation := by
  simp [TerminalPacketSelectorBN5ObligationPayload.obligationCheck]

/-- Obligation rejection is exactly inequality of the two BN5 obligation
    fields. -/
theorem TerminalPacketSelectorBN5ObligationPayload.obligationCheck_eq_false_iff
    {rankCount : Nat} [DecidableEq Obligation]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.obligationCheck = false ↔
      payload.sourceCoordinate.obligation ≠
        payload.selectorCoordinate.obligation := by
  simp [TerminalPacketSelectorBN5ObligationPayload.obligationCheck]

/-! ## Canonical grouped-family computation -/

variable [DecidableEq Frontier] [DecidableEq Obligation]

/-- Compute the BN5 frontier and obligation equalities while retaining every
    previously canonicalized Packet field. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  let source := (family.packetSelectorPayloadAtom handle).payload
  { (source.checks.withComputedColourChargeExactRouteRankDescent
      (family.packetSelectorCanonicalColourCheck handle)
      (rankOf handle) (beforeRank handle) (afterRank handle)) with
    frontierChecked := source.frontierCheck
    obligationChecked := source.obligationCheck }

/-- Every output field is computed from its authoritative input or preserved
    from the selected source payload. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_fields
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    let computed := family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle
    computed.colourChecked =
        family.packetSelectorCanonicalColourCheck handle ∧
      computed.frontierChecked = source.frontierCheck ∧
      computed.chargeChecked = true ∧
      computed.obligationChecked = source.obligationCheck ∧
      computed.activationChecked = source.checks.activationChecked ∧
      computed.directionChecked = source.checks.directionChecked ∧
      computed.budgetChecked = source.checks.budgetChecked ∧
      computed.rankTag = rankOf handle ∧
      computed.exactRouteClear = true ∧
      computed.strictDescentClear =
        terminalResidualRankLTBool (afterRank handle) (beforeRank handle) := by
  simp [
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Validity depends on exact BN5 frontier and obligation equality, the three
    unresolved fields, and exact residual descent. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_valid_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).Valid (rankOf handle) ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation =
          source.selectorCoordinate.obligation ∧
        source.checks.activationChecked = true ∧
        source.checks.directionChecked = true ∧
        source.checks.budgetChecked = true ∧
        (afterRank handle).LexLT (beforeRank handle) := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_true_iff]

/-- Canonical grouped-footprint eligibility makes the colour route
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_colour_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .colour ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- A frontier failure is exactly inequality of the two BN5 frontier fields. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_frontier_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .frontier ↔
      source.sourceCoordinate.frontier ≠
        source.selectorCoordinate.frontier := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Canonical positive source mass makes the charge route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_charge_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .charge ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent]

/-- An obligation failure occurs after frontier acceptance and is exactly
    inequality of the two BN5 obligation fields. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_obligation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .obligation ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation ≠
          source.selectorCoordinate.obligation := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Table-owned rank reflection makes the rank route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_rank_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .rank ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- Canonical source realization makes the internal exact-route failure
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_exactRoute_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .exactRoute ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- The final route retains exact nondecrease semantics after both BN5 checks
    and the three unresolved fields accept. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_descent_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .descent ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation =
          source.selectorCoordinate.obligation ∧
        source.checks.activationChecked = true ∧
        source.checks.directionChecked = true ∧
        source.checks.budgetChecked = true ∧
        ¬(afterRank handle).LexLT (beforeRank handle) := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_false_iff]

/-! ## Exact first-route semantics -/

/-- Faithfulness computed from the two BN5 fields and all previously
    canonicalized fields. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
    rankOf beforeRank afterRank handle).check (rankOf handle)

/-- First route from the same BN5-bound canonical payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
    rankOf beforeRank afterRank handle).firstRoute (rankOf handle)

/-- Exact failure proposition for the same BN5-bound payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
    rankOf beforeRank afterRank handle).FailureAt (rankOf handle) route

/-- Route equality and exact BN5-bound failure coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
    rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
      (rankOf handle) route

/-- The frontier route means exactly BN5 frontier inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_frontier_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = some .frontier ↔
      source.sourceCoordinate.frontier ≠
        source.selectorCoordinate.frontier := by
  calc
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = some .frontier ↔
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle).FailureAt
          (rankOf handle) .frontier :=
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
          (rankOf handle) .frontier
    _ ↔ _ :=
      family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_frontier_iff
        rankOf beforeRank afterRank handle

/-- The obligation route means accepted BN5 frontier equality followed by
    BN5 obligation inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_obligation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = some .obligation ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation ≠
          source.selectorCoordinate.obligation := by
  calc
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = some .obligation ↔
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle).FailureAt
          (rankOf handle) .obligation :=
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
          (rankOf handle) .obligation
    _ ↔ _ :=
      family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_obligation_iff
        rankOf beforeRank afterRank handle

/-- No canonical BN5-bound payload can report colour failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_colour
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle ≠ some .colour := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .colour).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_colour_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical BN5-bound payload can report source-charge failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_charge
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle ≠ some .charge := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .charge).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_charge_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical BN5-bound payload can report duplicate rank failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_rank
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle ≠ some .rank := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .rank).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_rank_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical BN5-bound payload can report internal source-route failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationRoutes_firstRoute_ne_some_exactRoute
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle ≠ some .exactRoute := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .exactRoute).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_exactRoute_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- A final route proves exact ten-coordinate nondecrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationRoutes_firstRoute_descent
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .descent).1 found
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_failureAt_descent_iff
      rankOf beforeRank afterRank handle).1 failure |>.2.2.2.2.2

/-- Accepted BN5-bound faithfulness retains actual residual descent. -/
theorem TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (accepted :
      family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes
        rankOf beforeRank afterRank handle = true) :
    (afterRank handle).LexLT (beforeRank handle) := by
  have valid :=
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      rankOf beforeRank afterRank handle).check_eq_true_iff (rankOf handle)
      |>.1 accepted
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes_valid_iff
      rankOf beforeRank afterRank handle).1 valid |>.2.2.2.2.2

/-! ## Canonicalized HB table and positive-Packet endpoint -/

/-- Rebuild table faithfulness from both BN5 equalities and all previously
    canonicalized fields. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationFaithfulness
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    TerminalPacketTypedRealizerTable current family rankCount :=
  { environment :=
      { rankOf := table.environment.rankOf
        faithful :=
          family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- BN5-bound canonicalization preserves every nonfaithfulness table input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationFaithfulness_preserves
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (rank : Fin rankCount) :
    (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
      beforeRank afterRank).environment.rankOf handle =
        table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt faithfulness bit is definitionally the BN5-bound
    computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationFaithfulness_faithful
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
      beforeRank afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationRoutes
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces a positive Packet to expose exact BN5 field
    evidence or an exact later route. -/
theorem TerminalBN6PacketConclusion.existsBN5FrontierObligationReflectedFirstRouteFailure_of_selectorSilence
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation)) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
      beforeRank afterRank).noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted handle
  rw [table.withComputedPacketSelectorBN5FrontierObligationFaithfulness_faithful
      beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationRoutes
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_iff
      table.environment.rankOf beforeRank afterRank handle route).1 found
  have notColour : route ≠ .colour := by
    intro isColour
    subst route
    exact family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_colour
      table.environment.rankOf beforeRank afterRank handle found
  have notCharge : route ≠ .charge := by
    intro isCharge
    subst route
    exact family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_charge
      table.environment.rankOf beforeRank afterRank handle found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  have notExactRoute : route ≠ .exactRoute := by
    intro isExactRoute
    subst route
    exact family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_exactRoute
      table.environment.rankOf beforeRank afterRank handle found
  have frontierMeaning :
      route ≠ .frontier ∨
        (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier := by
    by_cases isFrontier : route = .frontier
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_frontier_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isFrontier
  have obligationMeaning :
      route ≠ .obligation ∨
        ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
          (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation) := by
    by_cases isObligation : route = .obligation
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_obligation_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isObligation
  have descentMeaning :
      route ≠ .descent ∨
        ¬(afterRank handle).LexLT (beforeRank handle) := by
    by_cases isDescent : route = .descent
    · subst route
      exact Or.inr
        (family.not_rankDescent_of_computedBN5FrontierObligationRoutes_firstRoute_descent
          table.environment.rankOf beforeRank afterRank handle found)
    · exact Or.inl isDescent
  exact ⟨handle, route, found, failure, notColour, notCharge, notRank,
    notExactRoute, frontierMeaning, obligationMeaning, descentMeaning⟩

/-- Named milestone endpoint: a positive Packet under executable HB silence
    exposes exact BN5 frontier/obligation evidence or an exact later route. -/
theorem terminalBN6_packet_bn5_frontier_obligation_reflected_hb_first_route_failure
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation)) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsBN5FrontierObligationReflectedFirstRouteFailure_of_selectorSilence
    table dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
