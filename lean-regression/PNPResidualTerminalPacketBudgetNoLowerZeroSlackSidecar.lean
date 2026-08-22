import PNP.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar
import PNP.ZeroSlack

namespace PNP
namespace PacketBudgetNoLowerZeroSlackSidecarRegression

open DirectWire

variable (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate)

/-- The wrapper retains the exact proposition reflected by the composed
    executable checker. -/
example : TerminalPacketBudgetNoLowerAccepted certificate.budget
    certificate.candidate certificate.model certificate.table
    certificate.dependencyTable certificate.beforeRank certificate.afterRank :=
  certificate.accepted

/-- Every admitted governed support retains semantic-minimum meaning. -/
example : ∀ seed,
    seed ∈ allTerminalSupportSeeds certificate.inputs certificate.gates
      certificate.outputs certificate.profileWidth →
    certificate.budget.Fits certificate.candidate certificate.model seed →
    IsSemanticallyMinimum
      (terminalHResolveSupportImplementation certificate.candidate
        certificate.model seed) :=
  certificate.all_feasible_support_minimum

/-- No admitted governed support retains a strict equivalent gain. -/
example : ¬∃ seed,
    seed ∈ allTerminalSupportSeeds certificate.inputs certificate.gates
      certificate.outputs certificate.profileWidth ∧
    certificate.budget.Fits certificate.candidate certificate.model seed ∧
    ∃ next, StrictEquivalentGain
      (terminalHResolveSupportImplementation certificate.candidate
        certificate.model seed) next :=
  certificate.no_feasible_gain

/-- The checked Packet branch excludes a positive conclusion over the same
    supplied family. -/
example : ¬TerminalBN6PacketConclusion certificate.family :=
  certificate.no_positive_packet

/-- The named endpoint packages exactly the three current finite-branch
    consequences. -/
example :
    (∀ seed,
      seed ∈ allTerminalSupportSeeds certificate.inputs certificate.gates
        certificate.outputs certificate.profileWidth →
      certificate.budget.Fits certificate.candidate certificate.model seed →
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation certificate.candidate
          certificate.model seed)) ∧
    (¬∃ seed,
      seed ∈ allTerminalSupportSeeds certificate.inputs certificate.gates
        certificate.outputs certificate.profileWidth ∧
      certificate.budget.Fits certificate.candidate certificate.model seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation certificate.candidate
          certificate.model seed) next) ∧
    ¬TerminalBN6PacketConclusion certificate.family :=
  packet_budget_no_lower_zeroslack_sidecar_checked_complete certificate

/-- The report-facing ZeroSlack structure now stores this proof-bearing
    boundary rather than a no-lower string. -/
example (zeroSlack : ZeroSlackCertificate) :
    PacketBudgetNoLowerZeroSlackSidecarCertificate :=
  zeroSlack.packetBudgetNoLower

end PacketBudgetNoLowerZeroSlackSidecarRegression
end PNP
