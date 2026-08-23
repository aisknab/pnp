import PNP.ResidualTerminalFiniteBCELPacketActivationObstruction
import PNP.ZeroSlack

namespace PNP
namespace FiniteBCELPacketActivationObstructionRegression

open DirectWire

variable {packetBudgetNoLower :
  PacketBudgetNoLowerZeroSlackSidecarCertificate}
variable (certificate :
  TerminalFiniteBCELPacketCarrierCoherenceCertificate packetBudgetNoLower)

/-- The comparison quantity is computed from the exact selected M183 nucleus. -/
example : Nat := certificate.terminalDefect

/-- The Boolean scan is exactly the complete finite coherence proposition. -/
example : checkTerminalFiniteBCELPacketActivationCoherence certificate = true ↔
    TerminalFiniteBCELPacketActivationCoherent certificate :=
  checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff certificate

/-- Hypothetical acceptance links every mapped proper cut's Packet activation
    to the exact terminal projection excess. -/
example (coherent : TerminalFiniteBCELPacketActivationCoherent certificate)
    (cut : List (TerminalPrimitiveRecord packetBudgetNoLower.inputs
      packetBudgetNoLower.gates packetBudgetNoLower.outputs
      packetBudgetNoLower.profileWidth))
    (proper : TerminalBCELProperCutSeed
      certificate.terminalReady.result.nucleus.anchors cut) :
    Int.ofNat (packetBudgetNoLower.family.activationWeight
      (cut.map certificate.anchorMap)) =
      ((certificate.problem.anchorProblem.toProblem.cutCarrier
        certificate.terminalReady.result.nucleus.anchors cut).optimizationCorners
          certificate.problem.anchorProblem.toProblem.observe).projectionExcess :=
  certificate.activation_coherent_mapped_cut_equation coherent cut proper

/-- The exact accepted M184 family cannot satisfy that bridge. -/
example : ¬TerminalFiniteBCELPacketActivationCoherent certificate :=
  certificate.not_activation_coherent

/-- The classifier always returns a proof-bearing exact obstruction. -/
example : TerminalFiniteBCELPacketActivationObstruction certificate :=
  classifyTerminalFiniteBCELPacketActivationObstruction certificate

/-- The complete checker is forced to reject rather than accepting a supplied
    success bit. -/
example : checkTerminalFiniteBCELPacketActivationCoherence certificate = false :=
  certificate.activation_coherence_check_eq_false

/-- The named endpoint exposes the two precise finite failure shapes. -/
example :
    checkTerminalFiniteBCELPacketActivationCoherence certificate = false ∧
    (packetBudgetNoLower.family.cutValue ≠ certificate.terminalDefect ∨
      ∃ cut, cut.Sublist packetBudgetNoLower.family.carrier ∧ cut ≠ [] ∧
        cut ≠ packetBudgetNoLower.family.carrier ∧
        packetBudgetNoLower.family.activationWeight cut ≠
          certificate.terminalDefect) :=
  terminal_finite_bcel_packet_activation_obstruction_checked_complete
    certificate

/-- The report-facing ZeroSlack record derives the same obstruction from its
    exact dependent M184 certificate. -/
example (zeroSlack : ZeroSlackCertificate) :
    TerminalFiniteBCELPacketActivationObstruction
      zeroSlack.bcelCarrierCoherence :=
  zeroSlack.bcelPacketActivationObstruction

/-- The report-facing endpoint retains the exact failed check and mismatch. -/
example (zeroSlack : ZeroSlackCertificate) :
    checkTerminalFiniteBCELPacketActivationCoherence
        zeroSlack.bcelCarrierCoherence = false ∧
    (zeroSlack.packetBudgetNoLower.family.cutValue ≠
        zeroSlack.bcelCarrierCoherence.terminalDefect ∨
      ∃ cut, cut.Sublist zeroSlack.packetBudgetNoLower.family.carrier ∧
        cut ≠ [] ∧ cut ≠ zeroSlack.packetBudgetNoLower.family.carrier ∧
        zeroSlack.packetBudgetNoLower.family.activationWeight cut ≠
          zeroSlack.bcelCarrierCoherence.terminalDefect) :=
  zeroslack_bcel_packet_activation_obstruction_checked_complete zeroSlack

end FiniteBCELPacketActivationObstructionRegression
end PNP
