import PNP.ResidualTerminalPacketSelectorFirstRouteOutcome

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom
  (TerminalPacketSelectorFaithfulnessPayload rankCount)}

/-! ## Total payload and grouped-family classification -/

example
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    payload.firstRoute expectedRank = none ↔
      payload.check expectedRank = true :=
  payload.firstRoute_eq_none_iff_check_eq_true expectedRank

example
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    (∃ route : TerminalPacketSelectorFaithfulnessRoute,
      payload.firstRoute expectedRank = some route) ↔
      payload.check expectedRank = false :=
  payload.exists_firstRoute_iff_check_eq_false expectedRank

example
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRoute rankOf handle = none ↔
      family.packetSelectorPayloadFaithful rankOf handle = true :=
  family.packetSelectorPayloadFirstRoute_eq_none_iff rankOf handle

example
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    (∃ route : TerminalPacketSelectorFaithfulnessRoute,
      family.packetSelectorPayloadFirstRoute rankOf handle = some route) ↔
      family.packetSelectorPayloadFaithful rankOf handle = false :=
  family.exists_packetSelectorPayloadFirstRoute_iff rankOf handle

/-! ## Positive Packet and canonical HB outcomes -/

example
    (conclusion : TerminalBN6PacketConclusion family)
    (rankOf : family.PacketSelectorHandle -> Fin rankCount) :
    ∃ handle : family.PacketSelectorHandle,
      family.packetSelectorPayloadFaithful rankOf handle = true ∨
        ∃ route : TerminalPacketSelectorFaithfulnessRoute,
          family.packetSelectorPayloadFirstRoute rankOf handle = some route :=
  conclusion.existsFaithfulOrFirstRoute rankOf

example
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted :
      (table.withComputedPacketSelectorFaithfulness
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorFaithfulness
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRoute
          table.environment.rankOf handle = some route :=
  conclusion.existsFirstRoute_of_computedTableSelectorSilence table
    dependencyTable silenceAccepted closureAccepted

example
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted :
      (table.withComputedPacketSelectorFaithfulness
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorFaithfulness
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRoute
          table.environment.rankOf handle = some route :=
  terminalBN6_packet_computed_faithfulness_hb_first_route conclusion table
    dependencyTable silenceAccepted closureAccepted

end DirectWire
end PNP
