import PNP.ResidualTerminalPacketBN4ActivationRouteReflection

namespace PNP
namespace DirectWire
namespace PacketBN4ActivationRouteReflectionRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5ObligationPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat

def coordinate (activation frontier obligation : Nat) : Coordinate :=
  { key :=
      { atom := activation
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
    activationChecked := false
    directionChecked := true
    budgetChecked := true
    rankTag := 1
    exactRouteClear := false
    strictDescentClear := false }

def equalCoordinates : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 1 7 11
    selectorCoordinate := coordinate 1 7 11 }

def unequalFrontiers : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 1 7 11
    selectorCoordinate := coordinate 1 8 11 }

def unequalObligations : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 1 7 11
    selectorCoordinate := coordinate 1 7 12 }

def unequalActivations : Payload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 1 7 11
    selectorCoordinate := coordinate 9 7 11 }

example : equalCoordinates.frontierCheck = true := by
  rfl

example : equalCoordinates.obligationCheck = true := by
  rfl

example : equalCoordinates.activationCheck = true := by
  rfl

example : unequalFrontiers.frontierCheck = false := by
  rfl

example : unequalObligations.obligationCheck = false := by
  rfl

example : unequalActivations.activationCheck = false := by
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

example :
    unequalActivations.sourceCoordinate.key.atom ≠
      unequalActivations.selectorCoordinate.key.atom :=
  (unequalActivations.activationCheck_eq_false_iff).1 rfl

example :
    ∀ cut,
      (TerminalBN4CodeActive
          (terminalBN4ActivationCode
            equalCoordinates.sourceCoordinate.key.atom) cut ↔
        TerminalBN4CodeActive
          (terminalBN4ActivationCode
            equalCoordinates.selectorCoordinate.key.atom) cut) :=
  (equalCoordinates.activationCheck_eq_true_iff_activation).1 rfl

example :
    ¬ ∀ cut,
      (TerminalBN4CodeActive
          (terminalBN4ActivationCode
            unequalActivations.sourceCoordinate.key.atom) cut ↔
        TerminalBN4CodeActive
          (terminalBN4ActivationCode
            unequalActivations.selectorCoordinate.key.atom) cut) :=
  (unequalActivations.activationCheck_eq_false_iff_not_activation).1 rfl

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle = some .frontier ↔
      (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
        (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_frontier_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle = some .obligation ↔
      (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_obligation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle = some .activation ↔
      (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation =
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation ∧
        (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.key.atom ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.key.atom :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_activation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle ≠ some .colour :=
  family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_colour
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle ≠ some .charge :=
  family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_charge
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle ≠ some .rank :=
  family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_rank
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle ≠ some .exactRoute :=
  family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_exactRoute
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedBN5FrontierObligationActivationRoutes_firstRoute_descent
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
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationRoutes
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
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.key.atom)) ∧
          (route ≠ .descent ∨
            ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_bn4_activation_reflected_hb_first_route_failure
    conclusion table dependencyTable before after silenceAccepted
      closureAccepted

end PacketBN4ActivationRouteReflectionRegression
end DirectWire
end PNP
