import PNP.ResidualTerminalPacketFrontierRouteReflection

namespace PNP
namespace DirectWire
namespace PacketFrontierRouteReflectionRegression

def baseChecks : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { colourChecked := false
    frontierChecked := false
    chargeChecked := false
    obligationChecked := true
    activationChecked := true
    directionChecked := true
    budgetChecked := true
    rankTag := 1
    exactRouteClear := false
    strictDescentClear := false }

def equalFrontiers : TerminalPacketSelectorTypedFrontierPayload 2 Nat :=
  { checks := baseChecks
    sourceFrontier := 7
    selectorFrontier := 7 }

def unequalFrontiers : TerminalPacketSelectorTypedFrontierPayload 2 Nat :=
  { checks := baseChecks
    sourceFrontier := 7
    selectorFrontier := 8 }

example : equalFrontiers.frontierCheck = true := by
  rfl

example : unequalFrontiers.frontierCheck = false := by
  rfl

example : equalFrontiers.sourceFrontier = equalFrontiers.selectorFrontier :=
  (equalFrontiers.frontierCheck_eq_true_iff).1 rfl

example : unequalFrontiers.sourceFrontier ≠ unequalFrontiers.selectorFrontier :=
  (unequalFrontiers.frontierCheck_eq_false_iff).1 rfl

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle = some .frontier ↔
      (family.packetSelectorPayloadAtom handle).payload.sourceFrontier ≠
        (family.packetSelectorPayloadAtom handle).payload.selectorFrontier :=
  family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_frontier_iff
    rankOf before after handle

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (equal :
      (family.packetSelectorPayloadAtom handle).payload.sourceFrontier =
        (family.packetSelectorPayloadAtom handle).payload.selectorFrontier) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .frontier :=
  family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_ne_some_frontier_of_eq
    rankOf before after handle equal

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .colour :=
  family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
    rankOf before after handle

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .charge :=
  family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
    rankOf before after handle

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .rank :=
  family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
    rankOf before after handle

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .exactRoute :=
  family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
    rankOf before after handle

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_descent
    rankOf before after handle found

example
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf before after handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceFrontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorFrontier) ∧
          (route ≠ .descent ∨
            ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure
    conclusion table dependencyTable before after silenceAccepted
      closureAccepted

end PacketFrontierRouteReflectionRegression
end DirectWire
end PNP
