import PNP.ResidualTerminalPacketSelectorFaithfulnessTable

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom
  (TerminalPacketSelectorFaithfulnessPayload rankCount)}

/-! ## Exact field preservation and computed faithfulness -/

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    table.withComputedPacketSelectorFaithfulness.environment.rankOf handle =
      table.environment.rankOf handle :=
  table.withComputedPacketSelectorFaithfulness_rankOf handle

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (rank : Fin rankCount) :
    table.withComputedPacketSelectorFaithfulness.environment.hnActive rank =
      table.environment.hnActive rank :=
  table.withComputedPacketSelectorFaithfulness_hnActive rank

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (rank : Fin rankCount) :
    table.withComputedPacketSelectorFaithfulness.environment.budgetActive rank =
      table.environment.budgetActive rank :=
  table.withComputedPacketSelectorFaithfulness_budgetActive rank

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    table.withComputedPacketSelectorFaithfulness.claim handle =
      table.claim handle :=
  table.withComputedPacketSelectorFaithfulness_claim handle

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    table.withComputedPacketSelectorFaithfulness.environment.faithful handle =
      family.packetSelectorPayloadFaithful table.environment.rankOf handle :=
  table.withComputedPacketSelectorFaithfulness_faithful handle

/-! ## Binding-free Packet and HB composition -/

example
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    (table.withComputedPacketSelectorFaithfulness
      ).checkPacketSelectorFaithfulnessBinding = true :=
  table.withComputedPacketSelectorFaithfulness_binding

example
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      table.environment.rankOf = true) :
    ∃ handle : family.PacketSelectorHandle,
      (table.withComputedPacketSelectorFaithfulness
        ).environment.faithful handle = true :=
  conclusion.existsFaithfulHandle_of_computedTable table routesClear

example
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      table.environment.rankOf = true)
    (silenceAccepted :
      (table.withComputedPacketSelectorFaithfulness
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorFaithfulness
        ).environment = true) : False :=
  terminalBN6_packet_computed_faithfulness_hb_contradiction conclusion table
    dependencyTable routesClear silenceAccepted closureAccepted

end DirectWire
end PNP
