import PNP.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar
import PNP.ZeroSlack

namespace PNP
namespace BCELPacketNoLowerZeroSlackSidecarRegression

open DirectWire

variable {packetBudgetNoLower :
  PacketBudgetNoLowerZeroSlackSidecarCertificate}
variable (certificate : BCELContradictionCertificate packetBudgetNoLower)

/-- The data-only check retains the arbitrary-finite BN6 carrier premise. -/
example : 2 ≤ packetBudgetNoLower.family.carrier.length :=
  certificate.carrier_at_least_two

/-- The exact accepted M180 branch still excludes a positive Packet. -/
example : ¬TerminalBN6PacketConclusion packetBudgetNoLower.family :=
  certificate.no_positive_packet

/-- A BCEL constant-activation equation would construct that excluded Packet. -/
example : ¬packetBudgetNoLower.family.ConstantActivation :=
  certificate.not_constant_activation

/-- The named endpoint retains the complete bounded contradiction boundary. -/
example :
    (2 ≤ packetBudgetNoLower.family.carrier.length) ∧
      (¬TerminalBN6PacketConclusion packetBudgetNoLower.family) ∧
      ¬packetBudgetNoLower.family.ConstantActivation :=
  bcel_packet_no_lower_zeroslack_sidecar_checked_complete certificate

/-- The report-facing ZeroSlack record now binds the later finite ready nucleus
    to this exact Packet/budget no-lower certificate and family. -/
example (zeroSlack : ZeroSlackCertificate) :
    TerminalFiniteBCELPacketCarrierCoherenceCertificate
      zeroSlack.packetBudgetNoLower :=
  zeroSlack.bcelCarrierCoherence

/-- The report-facing boundary exposes the checked BCEL exclusion proposition. -/
example (zeroSlack : ZeroSlackCertificate) :
    zeroSlackSoundnessBoundary zeroSlack :=
  zeroSlackSoundnessBoundary_proved zeroSlack

end BCELPacketNoLowerZeroSlackSidecarRegression
end PNP
