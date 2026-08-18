import PNP.ResidualTerminalPacketBN5ObligationRouteReflection

namespace PNP
namespace DirectWire
namespace PacketBN5ObligationRouteReflectionRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5ObligationPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat

def coordinate (frontier obligation : Nat) : Coordinate :=
  { key :=
      { atom := 1
        semanticSignature := 2
        transportType := 3 }
    frontier := frontier
    chargeOwner := 4
    obligation := obligation
    originKernel := 5
    modeProjection := 6 }

def baseChecks : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { colourChecked := false
    frontierChecked := false
    chargeChecked := false
    obligationChecked := false
    activationChecked := true
    directionChecked := true
    budgetChecked := true
    rankTag := 1
    exactRouteClear := false
    strictDescentClear := false }

def equalCoordinates : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 7 11
    selectorCoordinate := coordinate 7 11 }

def unequalFrontiers : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 7 11
    selectorCoordinate := coordinate 8 11 }

def unequalObligations : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 7 11
    selectorCoordinate := coordinate 7 12 }

example : equalCoordinates.frontierCheck = true := by
  rfl

example : equalCoordinates.obligationCheck = true := by
  rfl

example : unequalFrontiers.frontierCheck = false := by
  rfl

example : unequalObligations.obligationCheck = false := by
  rfl

example :
    equalCoordinates.sourceCoordinate.frontier =
      equalCoordinates.selectorCoordinate.frontier :=
  (equalCoordinates.frontierCheck_eq_true_iff).1 rfl

example :
    unequalFrontiers.sourceCoordinate.frontier ≠
      unequalFrontiers.selectorCoordinate.frontier :=
  (unequalFrontiers.frontierCheck_eq_false_iff).1 rfl

example :
    equalCoordinates.sourceCoordinate.obligation =
      equalCoordinates.selectorCoordinate.obligation :=
  (equalCoordinates.obligationCheck_eq_true_iff).1 rfl

example :
    unequalObligations.sourceCoordinate.obligation ≠
      unequalObligations.selectorCoordinate.obligation :=
  (unequalObligations.obligationCheck_eq_false_iff).1 rfl

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle = some .frontier ↔
      (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
        (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_frontier_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle = some .obligation ↔
      (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes_eq_some_obligation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle ≠ some .colour :=
  family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_colour
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle ≠ some .charge :=
  family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_charge
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle ≠ some .rank :=
  family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_rank
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle ≠ some .exactRoute :=
  family.computedBN5FrontierObligationRoutes_firstRoute_ne_some_exactRoute
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedBN5FrontierObligationRoutes_firstRoute_descent
    rankOf before after handle found

example
    {Anchor : Type} [DecidableEq Anchor]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor (Payload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationRoutes
            table.environment.rankOf before after handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
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
            ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_bn5_frontier_obligation_reflected_hb_first_route_failure
    conclusion table dependencyTable before after silenceAccepted
      closureAccepted

end PacketBN5ObligationRouteReflectionRegression
end DirectWire
end PNP
