import PNP.ResidualTerminalFiniteBCELPacketCarrierCoherence
import PNP.ZeroSlack

namespace PNP
namespace FiniteBCELPacketCarrierCoherenceRegression

open DirectWire

variable {packetBudgetNoLower :
  PacketBudgetNoLowerZeroSlackSidecarCertificate}
variable (certificate :
  TerminalFiniteBCELPacketCarrierCoherenceCertificate packetBudgetNoLower)

/-- The terminal problem is definitionally indexed by the exact candidate and
    model already used by the Packet/budget certificate. -/
example : TerminalFiniteSaturatePositiveProblem
    packetBudgetNoLower.candidate packetBudgetNoLower.model :=
  certificate.problem

/-- The reflected carrier check exposes the exact bijective-map image. -/
example : packetBudgetNoLower.family.carrier =
    certificate.terminalReady.result.nucleus.anchors.map
      certificate.anchorMap :=
  certificate.family_carrier_eq

/-- The terminal ready branch retains its exact positive full-slack fact. -/
example : 0 < (terminalSaturationCostSnapshot
    packetBudgetNoLower.candidate packetBudgetNoLower.model
    certificate.problem.trace.replayRecords).fullSlack :=
  certificate.terminalReady.finalPositive

/-- The supplied representation map is a genuine bijection, not a one-way
    carrier coercion. -/
example : (∀ {left right}, certificate.anchorMap left =
    certificate.anchorMap right → left = right) ∧
    (∀ anchor, ∃ primitive, certificate.anchorMap primitive = anchor) :=
  ⟨certificate.anchorMapInjective, certificate.anchorMapSurjective⟩

/-- The mapped Packet carrier inherits the nontrivial M183 nucleus bound. -/
example : 2 ≤ packetBudgetNoLower.family.carrier.length :=
  certificate.carrier_at_least_two

/-- The same accepted M180 family still excludes a positive Packet. -/
example : ¬TerminalBN6PacketConclusion packetBudgetNoLower.family :=
  certificate.no_positive_packet

/-- Constant activation would construct the excluded Packet. -/
example : ¬packetBudgetNoLower.family.ConstantActivation :=
  certificate.not_constant_activation

/-- The named endpoint exposes the complete conservative M184 boundary. -/
example :
    (∀ event, event ∈ certificate.problem.trace.events →
      TerminalSaturationClosureSafeStep packetBudgetNoLower.candidate
        packetBudgetNoLower.model event) ∧
    0 < (terminalSaturationCostSnapshot packetBudgetNoLower.candidate
      packetBudgetNoLower.model
      certificate.problem.trace.replayRecords).fullSlack ∧
    0 < certificate.problem.anchorProblem.toProblem.familyDefect
      certificate.problem.anchorProblem.toProblem.anchorRecords ∧
    (∀ {left right}, certificate.anchorMap left =
      certificate.anchorMap right → left = right) ∧
    (∀ anchor, ∃ primitive, certificate.anchorMap primitive = anchor) ∧
    packetBudgetNoLower.family.carrier =
      certificate.terminalReady.result.nucleus.anchors.map
        certificate.anchorMap ∧
    2 ≤ packetBudgetNoLower.family.carrier.length ∧
    (¬TerminalBN6PacketConclusion packetBudgetNoLower.family) ∧
    ¬packetBudgetNoLower.family.ConstantActivation :=
  terminal_finite_bcel_packet_carrier_coherent_checked_complete certificate

/-- The report-facing ZeroSlack record now consumes the coherent M184
    certificate rather than an independent carrier-size check. -/
example (zeroSlack : ZeroSlackCertificate) :
    TerminalFiniteBCELPacketCarrierCoherenceCertificate
      zeroSlack.packetBudgetNoLower :=
  zeroSlack.bcelCarrierCoherence

/-- The report-facing soundness boundary is derived from the coherent family. -/
example (zeroSlack : ZeroSlackCertificate) :
    zeroSlackSoundnessBoundary zeroSlack :=
  zeroSlackSoundnessBoundary_proved zeroSlack

end FiniteBCELPacketCarrierCoherenceRegression
end PNP
