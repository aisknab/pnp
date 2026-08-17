import PNP.ResidualTerminalPacketRankRouteReflection

namespace PNP
namespace DirectWire
namespace PacketRankRouteReflectionRegression

def forgedRankPayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { colourChecked := true
    frontierChecked := true
    chargeChecked := true
    obligationChecked := true
    activationChecked := true
    directionChecked := true
    budgetChecked := true
    rankTag := 1
    exactRouteClear := true
    strictDescentClear := true }

def exactRouteFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRankPayload with exactRouteClear := false }

def beforeRank : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 1

def smallerAfterRank : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0

example :
    (forgedRankPayload.withComputedRankDescent 0 beforeRank beforeRank
      ).rankTag = 0 := by
  rfl

example :
    (forgedRankPayload.withComputedRankDescent 0 beforeRank beforeRank
      ).firstRoute 0 = some .descent := by
  rfl

example :
    (forgedRankPayload.withComputedRankDescent 0 beforeRank beforeRank
      ).firstRoute 0 ≠ some .rank :=
  forgedRankPayload.withComputedRankDescent_firstRoute_ne_some_rank
    0 beforeRank beforeRank

example :
    ¬(forgedRankPayload.withComputedRankDescent 0 beforeRank beforeRank
      ).FailureAt 0 .rank := by
  intro rankFailure
  exact ((forgedRankPayload.withComputedRankDescent_failureAt_rank_iff_false
    0 beforeRank beforeRank).1 rankFailure).elim

example :
    (forgedRankPayload.withComputedRankDescent 0 beforeRank smallerAfterRank
      ).firstRoute 0 = none := by
  rfl

example :
    (exactRouteFailurePayload.withComputedRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .exactRoute := by
  rfl

example : smallerAfterRank.LexLT beforeRank := by
  apply forgedRankPayload.rankDescent_of_withComputedRankDescent_check
    (expectedRank := 0) beforeRank smallerAfterRank
  rfl

example :
    (forgedRankPayload.withComputedRankDescent 0 beforeRank beforeRank
      ).firstRoute 0 = some .descent ↔
      forgedRankPayload.colourChecked = true ∧
        forgedRankPayload.frontierChecked = true ∧
        forgedRankPayload.chargeChecked = true ∧
        forgedRankPayload.obligationChecked = true ∧
        forgedRankPayload.activationChecked = true ∧
        forgedRankPayload.directionChecked = true ∧
        forgedRankPayload.budgetChecked = true ∧
        forgedRankPayload.exactRouteClear = true ∧
        ¬beforeRank.LexLT beforeRank :=
  forgedRankPayload.withComputedRankDescent_firstRoute_eq_some_descent_iff
    0 beforeRank beforeRank

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedRankDescent rankOf
        before after handle ≠ some .rank :=
  family.computedRankDescent_firstRoute_ne_some_rank rankOf before after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedRankDescent rankOf
        before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedRankDescent_firstRoute_descent rankOf
    before after handle found

example
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorRankDescentFaithfulness before after
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorRankDescentFaithfulness before after
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedRankDescent
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedRankDescent
            table.environment.rankOf before after handle route ∧
          route ≠ .rank ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_rank_tag_reflected_hb_first_route_failure conclusion table
    dependencyTable before after silenceAccepted closureAccepted

end PacketRankRouteReflectionRegression
end DirectWire
end PNP
