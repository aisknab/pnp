/-
Copyright (c) 2026 PNP Labs.

Typed direction reflection for the Packet selector-faithfulness payload.  The
pinned manuscript's pair payload retains an explicit `Dir(u)` value and routes
a direction mismatch after activation and before budget.  This module compares
typed source and selector direction values directly instead of accepting an
independent `directionChecked` Boolean at the active canonical-payload
interface.

The construction is uniform over arbitrary finite grouped BN6 families,
finite rank carriers, and all payload-field types with the required decidable
equalities.  It retains computed BN5 frontier and obligation checks, exact BN4
activation, grouped-footprint colour, positive source charge, the canonical
source route, the table-owned rank, and exact ten-coordinate residual descent.

The typed direction values, complete BN5 coordinates, grouped family, rank
map, residual ranks, realizer claims, blocker activity, and dependency rows
remain explicit inputs.  This module does not construct those values from
terminal data or prove external direction transport semantics.  Budget remains
an explicit Boolean.  It does not establish complete route silence,
unconditional HB negative closure, ZeroSlack, PCCMin, polynomial runtime,
SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketBN4ActivationRouteReflection

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction : Type}
variable [DecidableEq Anchor]

/-! ## Typed direction payload and exact comparison -/

/-- The existing activation-reflected payload together with the source and
    selector `Dir(u)` values required by the Packet boundary. -/
structure TerminalPacketSelectorBN5DirectionPayload
    (rankCount : Nat)
    (ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection Direction : Type) where
  checks : TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
    SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection
  sourceDirection : Direction
  selectorDirection : Direction

/-- Executable equality of the two typed Packet direction values. -/
def TerminalPacketSelectorBN5DirectionPayload.directionCheck
    {rankCount : Nat} [DecidableEq Direction]
    (payload : TerminalPacketSelectorBN5DirectionPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection Direction) : Bool :=
  decide (payload.sourceDirection = payload.selectorDirection)

/-- Direction acceptance is exactly equality of the typed values. -/
theorem TerminalPacketSelectorBN5DirectionPayload.directionCheck_eq_true_iff
    {rankCount : Nat} [DecidableEq Direction]
    (payload : TerminalPacketSelectorBN5DirectionPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection Direction) :
    payload.directionCheck = true ↔
      payload.sourceDirection = payload.selectorDirection := by
  simp [TerminalPacketSelectorBN5DirectionPayload.directionCheck]

/-- Direction rejection is exactly inequality of the typed values. -/
theorem TerminalPacketSelectorBN5DirectionPayload.directionCheck_eq_false_iff
    {rankCount : Nat} [DecidableEq Direction]
    (payload : TerminalPacketSelectorBN5DirectionPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection Direction) :
    payload.directionCheck = false ↔
      payload.sourceDirection ≠ payload.selectorDirection := by
  simp [TerminalPacketSelectorBN5DirectionPayload.directionCheck]

/-! ## Canonical grouped-family computation -/

variable [DecidableEq ActivationAtom] [DecidableEq Frontier]
  [DecidableEq Obligation] [DecidableEq Direction]

/-- Compute every reflected field through direction while retaining the sole
    unresolved budget field. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  let source := (family.packetSelectorPayloadAtom handle).payload
  { (source.checks.checks.withComputedColourChargeExactRouteRankDescent
      (family.packetSelectorCanonicalColourCheck handle)
      (rankOf handle) (beforeRank handle) (afterRank handle)) with
    frontierChecked := source.checks.frontierCheck
    obligationChecked := source.checks.obligationCheck
    activationChecked := source.checks.activationCheck
    directionChecked := source.directionCheck }

/-- Every output field is computed from its authoritative input or preserved
    from the selected source payload. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_fields
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    let computed :=
      family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle
    computed.colourChecked =
        family.packetSelectorCanonicalColourCheck handle ∧
      computed.frontierChecked = source.checks.frontierCheck ∧
      computed.chargeChecked = true ∧
      computed.obligationChecked = source.checks.obligationCheck ∧
      computed.activationChecked = source.checks.activationCheck ∧
      computed.directionChecked = source.directionCheck ∧
      computed.budgetChecked = source.checks.checks.budgetChecked ∧
      computed.rankTag = rankOf handle ∧
      computed.exactRouteClear = true ∧
      computed.strictDescentClear =
        terminalResidualRankLTBool (afterRank handle) (beforeRank handle) := by
  simp [
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Validity is exact equality through direction, the remaining budget check,
    and exact residual descent. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_valid_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).Valid (rankOf handle) ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation =
          source.checks.selectorCoordinate.obligation ∧
        source.checks.sourceCoordinate.key.atom =
          source.checks.selectorCoordinate.key.atom ∧
        source.sourceDirection = source.selectorDirection ∧
        source.checks.checks.budgetChecked = true ∧
        (afterRank handle).LexLT (beforeRank handle) := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorBN5DirectionPayload.directionCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_true_iff]

/-- Canonical grouped-footprint eligibility makes the colour route
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_colour_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .colour ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- A frontier failure is exactly inequality of the two BN5 frontier fields. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_frontier_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .frontier ↔
      source.checks.sourceCoordinate.frontier ≠
        source.checks.selectorCoordinate.frontier := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Canonical positive source mass makes the charge route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_charge_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .charge ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent]

/-- An obligation failure occurs after frontier acceptance and is exact BN5
    obligation inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_obligation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .obligation ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation ≠
          source.checks.selectorCoordinate.obligation := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- An activation failure occurs after both earlier BN5 equalities and is exact
    inequality of the nested BN4 activation atoms. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_activation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt
        (rankOf handle) .activation ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation =
          source.checks.selectorCoordinate.obligation ∧
        source.checks.sourceCoordinate.key.atom ≠
          source.checks.selectorCoordinate.key.atom := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- A direction failure occurs after every earlier reflected equality and is
    exact inequality of the typed `Dir(u)` values. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_direction_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt
        (rankOf handle) .direction ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation =
          source.checks.selectorCoordinate.obligation ∧
        source.checks.sourceCoordinate.key.atom =
          source.checks.selectorCoordinate.key.atom ∧
        source.sourceDirection ≠ source.selectorDirection := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorBN5DirectionPayload.directionCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Table-owned rank reflection makes the rank route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_rank_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .rank ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- Canonical source-route reflection makes the exact-route failure
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_exactRoute_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .exactRoute ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- The final route retains exact nondecrease semantics after every reflected
    field and the sole unresolved budget field accept. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_descent_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .descent ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation =
          source.checks.selectorCoordinate.obligation ∧
        source.checks.sourceCoordinate.key.atom =
          source.checks.selectorCoordinate.key.atom ∧
        source.sourceDirection = source.selectorDirection ∧
        source.checks.checks.budgetChecked = true ∧
        ¬(afterRank handle).LexLT (beforeRank handle) := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorBN5DirectionPayload.directionCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_false_iff]

/-! ## Exact first-route semantics -/

/-- Faithfulness computed from every field through typed direction. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
    rankOf beforeRank afterRank handle).check (rankOf handle)

/-- Exact first failed route for the direction-reflected payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
    rankOf beforeRank afterRank handle).firstRoute (rankOf handle)

/-- Route-indexed failure proposition for the direction-reflected payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
    rankOf beforeRank afterRank handle).FailureAt (rankOf handle) route

/-- The executable route is exactly its route-indexed failure proposition. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle route := by
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
        (rankOf handle) route

/-- A frontier first route is exactly BN5 frontier inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_frontier_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = some .frontier ↔
      source.checks.sourceCoordinate.frontier ≠
        source.checks.selectorCoordinate.frontier := by
  rw [family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff]
  exact family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_frontier_iff
    rankOf beforeRank afterRank handle

/-- An obligation first route is exactly prior frontier equality and BN5
    obligation inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_obligation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = some .obligation ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation ≠
          source.checks.selectorCoordinate.obligation := by
  rw [family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff]
  exact family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_obligation_iff
    rankOf beforeRank afterRank handle

/-- An activation first route is exactly prior BN5 equality and nested BN4
    activation inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_activation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = some .activation ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation =
          source.checks.selectorCoordinate.obligation ∧
        source.checks.sourceCoordinate.key.atom ≠
          source.checks.selectorCoordinate.key.atom := by
  rw [family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff]
  exact family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_activation_iff
    rankOf beforeRank afterRank handle

/-- A direction first route is exactly all earlier equalities and typed
    direction inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_direction_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = some .direction ↔
      source.checks.sourceCoordinate.frontier =
          source.checks.selectorCoordinate.frontier ∧
        source.checks.sourceCoordinate.obligation =
          source.checks.selectorCoordinate.obligation ∧
        source.checks.sourceCoordinate.key.atom =
          source.checks.selectorCoordinate.key.atom ∧
        source.sourceDirection ≠ source.selectorDirection := by
  rw [family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff]
  exact family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_direction_iff
    rankOf beforeRank afterRank handle

/-- No direction-reflected canonical payload can report colour failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_colour
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle ≠ some .colour := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .colour).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_colour_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No direction-reflected canonical payload can report charge failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_charge
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle ≠ some .charge := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .charge).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_charge_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No direction-reflected canonical payload can report duplicate rank
    failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_rank
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle ≠ some .rank := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .rank).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_rank_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No direction-reflected canonical payload can report internal source-route
    failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_exactRoute
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle ≠ some .exactRoute := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .exactRoute).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_exactRoute_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- A final route proves exact ten-coordinate nondecrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_descent
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .descent).1 found
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_failureAt_descent_iff
      rankOf beforeRank afterRank handle).1 failure |>.2.2.2.2.2

/-- Accepted direction-reflected faithfulness retains actual residual
    descent. -/
theorem TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (accepted :
      family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf beforeRank afterRank handle = true) :
    (afterRank handle).LexLT (beforeRank handle) := by
  have valid :=
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      rankOf beforeRank afterRank handle).check_eq_true_iff (rankOf handle)
      |>.1 accepted
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes_valid_iff
      rankOf beforeRank afterRank handle).1 valid |>.2.2.2.2.2

/-! ## Canonicalized HB table and positive-Packet endpoint -/

/-- Rebuild table faithfulness from exact equality through typed direction and
    every previously canonicalized field. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    TerminalPacketTypedRealizerTable current family rankCount :=
  { environment :=
      { rankOf := table.environment.rankOf
        faithful :=
          family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Direction-reflected canonicalization preserves every nonfaithfulness table
    input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness_preserves
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (rank : Fin rankCount) :
    (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
      beforeRank afterRank).environment.rankOf handle =
        table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt faithfulness bit is definitionally the direction-reflected
    computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness_faithful
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
      beforeRank afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationDirectionRoutes
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces a positive Packet to expose exact reflected
    evidence through typed direction or an exact later route. -/
theorem TerminalBN6PacketConclusion.existsDirectionReflectedFirstRouteFailure_of_selectorSilence
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation)) ∧
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom)) ∧
          (route ≠ .direction ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceDirection ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorDirection)) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
      beforeRank afterRank).noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted handle
  rw [table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness_faithful
      beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationDirectionRoutes
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_iff
      table.environment.rankOf beforeRank afterRank handle route).1 found
  have notColour : route ≠ .colour := by
    intro isColour
    subst route
    exact family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_colour
      table.environment.rankOf beforeRank afterRank handle found
  have notCharge : route ≠ .charge := by
    intro isCharge
    subst route
    exact family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_charge
      table.environment.rankOf beforeRank afterRank handle found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  have notExactRoute : route ≠ .exactRoute := by
    intro isExactRoute
    subst route
    exact family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_exactRoute
      table.environment.rankOf beforeRank afterRank handle found
  have frontierMeaning :
      route ≠ .frontier ∨
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier ≠
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier := by
    by_cases isFrontier : route = .frontier
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_frontier_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isFrontier
  have obligationMeaning :
      route ≠ .obligation ∨
        ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
          (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation ≠
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation) := by
    by_cases isObligation : route = .obligation
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_obligation_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isObligation
  have activationMeaning :
      route ≠ .activation ∨
        ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
          (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
          (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom ≠
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom) := by
    by_cases isActivation : route = .activation
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_activation_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isActivation
  have directionMeaning :
      route ≠ .direction ∨
        ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
          (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
          (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom =
            (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom ∧
          (family.packetSelectorPayloadAtom handle).payload.sourceDirection ≠
            (family.packetSelectorPayloadAtom handle).payload.selectorDirection) := by
    by_cases isDirection : route = .direction
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_direction_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isDirection
  have descentMeaning :
      route ≠ .descent ∨
        ¬(afterRank handle).LexLT (beforeRank handle) := by
    by_cases isDescent : route = .descent
    · subst route
      exact Or.inr
        (family.not_rankDescent_of_computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_descent
          table.environment.rankOf beforeRank afterRank handle found)
    · exact Or.inl isDescent
  exact ⟨handle, route, found, failure, notColour, notCharge, notRank,
    notExactRoute, frontierMeaning, obligationMeaning, activationMeaning,
    directionMeaning, descentMeaning⟩

/-- Named milestone endpoint for typed Packet direction reflection. -/
theorem terminalBN6_packet_direction_reflected_hb_first_route_failure
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5DirectionPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation)) ∧
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom)) ∧
          (route ≠ .direction ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceDirection ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorDirection)) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsDirectionReflectedFirstRouteFailure_of_selectorSilence
    table dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
