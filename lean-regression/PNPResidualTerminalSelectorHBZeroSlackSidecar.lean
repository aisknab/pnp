import PNP.ResidualTerminalSelectorHBZeroSlackSidecar

namespace PNP
namespace SelectorHBZeroSlackSidecarRegression

open DirectWire

variable (certificate : SelectorHBZeroSlackSidecarCertificate)

/-- The wrapper retains the exhaustive all-handle selector-silence result. -/
example : ∀ handle : certificate.family.PacketSelectorHandle,
    certificate.realizerTable.environment.faithful handle = false :=
  certificate.accepted.1

/-- Accepted rows are exact typed bottoms, not opaque log handles. -/
example : ∀ handle : certificate.family.PacketSelectorHandle,
    ∃ reason : TerminalPacketTypedRealizerBot
        certificate.family.PacketSelectorHandle certificate.rankCount,
      certificate.realizerTable.claim handle =
        TerminalPacketTypedRealizerClaim.bot reason :=
  certificate.accepted.2.1

/-- The wrapper retains both checked local closure and exact-rank validity. -/
example : certificate.dependencyTable.NoOutcomeActiveClosureValid
    certificate.realizerTable.environment :=
  certificate.hb_closure_valid

/-- No HN or budget activity bit survives the checked well-founded closure. -/
example : ∀ node,
    certificate.realizerTable.environment.hbActive node = false :=
  certificate.accepted.2.2.2.1

/-- The dependency relation remains well founded. -/
example : WellFounded certificate.dependencyTable.Depends :=
  certificate.depends_wellFounded

/-- The named endpoint packages exactly the five proof-bearing consequences. -/
example :
    (∀ handle : certificate.family.PacketSelectorHandle,
      certificate.realizerTable.environment.faithful handle = false) ∧
      (∀ handle : certificate.family.PacketSelectorHandle,
        ∃ reason : TerminalPacketTypedRealizerBot
            certificate.family.PacketSelectorHandle certificate.rankCount,
          certificate.realizerTable.claim handle =
            TerminalPacketTypedRealizerClaim.bot reason) ∧
      certificate.dependencyTable.NoOutcomeActiveClosureValid
        certificate.realizerTable.environment ∧
      (∀ node,
        certificate.realizerTable.environment.hbActive node = false) ∧
      WellFounded certificate.dependencyTable.Depends :=
  selector_hb_zeroslack_sidecar_checked_complete certificate

end SelectorHBZeroSlackSidecarRegression
end PNP
