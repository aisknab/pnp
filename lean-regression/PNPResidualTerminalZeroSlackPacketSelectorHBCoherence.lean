import PNP.ZeroSlack

namespace PNP
namespace ZeroSlackPacketSelectorHBCoherenceRegression

open DirectWire

variable (packetBudgetNoLower :
  PacketBudgetNoLowerZeroSlackSidecarCertificate)
variable (bcel : BCELContradictionCertificate packetBudgetNoLower)

/-- The report-facing Selector/HB boundary uses the exact M180 family. -/
example : packetBudgetNoLower.selectorHB.family =
    packetBudgetNoLower.family :=
  packetBudgetNoLower.selectorHB_family

/-- The report-facing Selector/HB boundary uses the exact computed M180 table. -/
example : packetBudgetNoLower.selectorHB.realizerTable =
    packetBudgetNoLower.computedSelectorHBTable :=
  packetBudgetNoLower.selectorHB_realizerTable

/-- The report-facing Selector/HB boundary uses the exact M180 dependency
    table rather than a caller-supplied duplicate. -/
example : packetBudgetNoLower.selectorHB.dependencyTable =
    packetBudgetNoLower.dependencyTable :=
  packetBudgetNoLower.selectorHB_dependencyTable

/-- Every canonical selector is silent on the exact computed table. -/
example (handle : packetBudgetNoLower.family.PacketSelectorHandle) :
    packetBudgetNoLower.selectorHB.realizerTable.environment.faithful
      handle = false :=
  packetBudgetNoLower.selectorHB.no_faithful handle

/-- HB no-outcome closure is retained on the same dependency data. -/
example :
    packetBudgetNoLower.selectorHB.dependencyTable.NoOutcomeActiveClosureValid
      packetBudgetNoLower.selectorHB.realizerTable.environment :=
  packetBudgetNoLower.selectorHB.hb_closure_valid

/-- No HN or budget dependency node remains active. -/
example (node : TerminalPacketHBNode packetBudgetNoLower.rankCount) :
    packetBudgetNoLower.selectorHB.realizerTable.environment.hbActive
      node = false :=
  packetBudgetNoLower.selectorHB.no_hb_active node

/-- The named dependency endpoint retains selector/HB closure, Packet
    exclusion, and the same-family BCEL exclusion. -/
example :
    (∀ handle : packetBudgetNoLower.family.PacketSelectorHandle,
      packetBudgetNoLower.selectorHB.realizerTable.environment.faithful
        handle = false) ∧
    packetBudgetNoLower.selectorHB.dependencyTable.NoOutcomeActiveClosureValid
      packetBudgetNoLower.selectorHB.realizerTable.environment ∧
    (∀ node,
      packetBudgetNoLower.selectorHB.realizerTable.environment.hbActive
        node = false) ∧
    (¬TerminalBN6PacketConclusion packetBudgetNoLower.family) ∧
    ¬packetBudgetNoLower.family.ConstantActivation :=
  packet_selector_hb_bcel_coherent_checked_complete packetBudgetNoLower bcel

/-- ZeroSlack stores no independent Selector/HB sidecar; its accessor reduces
    to the exact Packet/budget-derived value. -/
example (zeroSlack : ZeroSlackCertificate) :
    zeroSlack.selectorHBClosure = zeroSlack.packetBudgetNoLower.selectorHB :=
  rfl

/-- PCCOracle exposes the same derived boundary as its ZeroSlack member. -/
example (oracle : PCCOracleCertificate) :
    oracle.selectorHBClosure = oracle.zeroSlack.selectorHBClosure :=
  rfl

/-- The report-facing endpoint is the exact dependency endpoint. -/
example (zeroSlack : ZeroSlackCertificate) :
    (∀ handle : zeroSlack.packetBudgetNoLower.family.PacketSelectorHandle,
      zeroSlack.selectorHBClosure.realizerTable.environment.faithful
        handle = false) ∧
    zeroSlack.selectorHBClosure.dependencyTable.NoOutcomeActiveClosureValid
      zeroSlack.selectorHBClosure.realizerTable.environment ∧
    (∀ node,
      zeroSlack.selectorHBClosure.realizerTable.environment.hbActive
        node = false) ∧
    (¬TerminalBN6PacketConclusion zeroSlack.packetBudgetNoLower.family) ∧
    ¬zeroSlack.packetBudgetNoLower.family.ConstantActivation :=
  zeroslack_packet_selector_hb_bcel_coherent_checked_complete zeroSlack

end ZeroSlackPacketSelectorHBCoherenceRegression
end PNP
