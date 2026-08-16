import PNP.ResidualTerminalPacketDescentRouteReflection

namespace PNP
namespace DirectWire
namespace PacketDescentRouteReflectionRegression

def forgedAcceptedPayload : TerminalPacketSelectorFaithfulnessPayload 1 :=
  { colourChecked := true
    frontierChecked := true
    chargeChecked := true
    obligationChecked := true
    activationChecked := true
    directionChecked := true
    budgetChecked := true
    rankTag := ⟨0, Nat.zero_lt_succ 0⟩
    exactRouteClear := true
    strictDescentClear := true }

def beforeRank : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 1

def smallerAfterRank : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0

example :
    (forgedAcceptedPayload.withComputedDescent beforeRank beforeRank
      ).strictDescentClear = false := by
  rfl

example :
    (forgedAcceptedPayload.withComputedDescent beforeRank smallerAfterRank
      ).strictDescentClear = true := by
  rfl

example :
    (forgedAcceptedPayload.withComputedDescent beforeRank beforeRank
      ).firstRoute 0 = some .descent := by
  rfl

example :
    (forgedAcceptedPayload.withComputedDescent beforeRank beforeRank
      ).FailureAt 0 .descent := by
  apply (forgedAcceptedPayload.withComputedDescent beforeRank beforeRank
    ).firstRoute_eq_some_iff_failureAt 0 .descent |>.1
  rfl

example : ¬beforeRank.LexLT beforeRank := by
  exact (terminalResidualRankLTBool_eq_false_iff beforeRank beforeRank).1 rfl

example : smallerAfterRank.LexLT beforeRank := by
  exact terminalResidualRank_canonicalCode_lt
    0 0 0 0 0 0 0 0 0 0 1 (Nat.zero_lt_succ 0)

example : smallerAfterRank.LexLT beforeRank := by
  apply forgedAcceptedPayload.rankDescent_of_withComputedDescent_check
    (expectedRank := 0) beforeRank smallerAfterRank
  rfl

example :
    (forgedAcceptedPayload.withComputedDescent beforeRank beforeRank
      ).firstRoute 0 = some .descent ↔
      forgedAcceptedPayload.colourChecked = true ∧
        forgedAcceptedPayload.frontierChecked = true ∧
        forgedAcceptedPayload.chargeChecked = true ∧
        forgedAcceptedPayload.obligationChecked = true ∧
        forgedAcceptedPayload.activationChecked = true ∧
        forgedAcceptedPayload.directionChecked = true ∧
        forgedAcceptedPayload.budgetChecked = true ∧
        forgedAcceptedPayload.rankTag = 0 ∧
        forgedAcceptedPayload.exactRouteClear = true ∧
        ¬beforeRank.LexLT beforeRank :=
  forgedAcceptedPayload.withComputedDescent_firstRoute_eq_some_descent_iff
    0 beforeRank beforeRank

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found : family.packetSelectorPayloadFirstRouteWithComputedDescent rankOf
      before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computed_firstRoute_descent rankOf before after
    handle found

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
      (table.withComputedPacketSelectorDescentFaithfulness before after
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorDescentFaithfulness before after
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedDescent
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedDescent
            table.environment.rankOf before after handle route ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_rank_reflected_hb_first_route_failure conclusion table
    dependencyTable before after silenceAccepted closureAccepted

end PacketDescentRouteReflectionRegression
end DirectWire
end PNP
