/-
Copyright (c) 2026 PNP Labs.

Proof-bearing selector-silence and HB-closure sidecar for the report-facing
ZeroSlack certificate.  The finite grouped BN6 family, typed-realizer table,
and exact-rank HB dependency table are explicit data.  Acceptance is not a
caller flag: the existing executable checks must prove that every canonical
realizer row is a typed bottom and that every active HN/BUD node would require
a strictly lower active dependency.  Finite-rank induction then eliminates
every faithful selector and every supplied HB activity bit.

The family, tables, environment, realizer claims, activity bits, dependency
rows, and finite rank map remain inputs.  This module does not derive them from
terminal data, prove selector faithfulness or compatibility, establish HN/BUD
blocker semantics or semantic dependency completeness, connect selector
silence to the BCEL contradiction, prove unconditional ZeroSlack or PCCMin,
establish polynomial size or runtime, put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalHBExecutableSelectorSilenceInduction

namespace PNP

/-- Checked proof-bearing evidence jointly replacing the report-facing
    selector-silence and HB-closure string handles. -/
structure SelectorHBZeroSlackSidecarCertificate where
  Atom : Type
  Payload : Type
  atomDecidableEq : DecidableEq Atom
  inputs : Nat
  outputs : Nat
  rankCount : Nat
  current : DirectWire.Implementation inputs outputs
  family : DirectWire.TerminalBN6GroupedFamily Atom Payload
  realizerTable : @DirectWire.TerminalPacketTypedRealizerTable
    Atom Payload atomDecidableEq inputs outputs current family rankCount
  dependencyTable : DirectWire.TerminalPacketHBDependencyTable rankCount
  selectorSilenceAccepted :
    @DirectWire.TerminalPacketTypedRealizerTable.checkSelectorSilent
      Atom Payload atomDecidableEq inputs outputs rankCount current family
        realizerTable = true
  hbClosureAccepted :
    dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true

attribute [instance]
  SelectorHBZeroSlackSidecarCertificate.atomDecidableEq

/-- The two stored checker equations expose the complete selector-silence and
    HB-closure proposition already proved by the executable induction. -/
theorem SelectorHBZeroSlackSidecarCertificate.accepted
    (certificate : SelectorHBZeroSlackSidecarCertificate) :
    (∀ handle : certificate.family.PacketSelectorHandle,
      certificate.realizerTable.environment.faithful handle = false) ∧
      (∀ handle : certificate.family.PacketSelectorHandle,
        ∃ reason : DirectWire.TerminalPacketTypedRealizerBot
            certificate.family.PacketSelectorHandle certificate.rankCount,
          certificate.realizerTable.claim handle =
            DirectWire.TerminalPacketTypedRealizerClaim.bot reason) ∧
      certificate.dependencyTable.NoOutcomeActiveClosureValid
        certificate.realizerTable.environment ∧
      (∀ node,
        certificate.realizerTable.environment.hbActive node = false) ∧
      WellFounded certificate.dependencyTable.Depends := by
  letI : DecidableEq certificate.Atom := certificate.atomDecidableEq
  exact
    DirectWire.terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract
      certificate.realizerTable certificate.dependencyTable
        certificate.selectorSilenceAccepted certificate.hbClosureAccepted

/-- Every canonical selector in an accepted sidecar is nonfaithful. -/
theorem SelectorHBZeroSlackSidecarCertificate.no_faithful
    (certificate : SelectorHBZeroSlackSidecarCertificate)
    (handle : certificate.family.PacketSelectorHandle) :
    certificate.realizerTable.environment.faithful handle = false :=
  certificate.accepted.1 handle

/-- Every canonical realizer claim is exactly a typed bottom constructor. -/
theorem SelectorHBZeroSlackSidecarCertificate.claim_eq_bot
    (certificate : SelectorHBZeroSlackSidecarCertificate)
    (handle : certificate.family.PacketSelectorHandle) :
    ∃ reason : DirectWire.TerminalPacketTypedRealizerBot
        certificate.family.PacketSelectorHandle certificate.rankCount,
      certificate.realizerTable.claim handle =
        DirectWire.TerminalPacketTypedRealizerClaim.bot reason :=
  certificate.accepted.2.1 handle

/-- The exact-rank dependency table and local activity closure are valid. -/
theorem SelectorHBZeroSlackSidecarCertificate.hb_closure_valid
    (certificate : SelectorHBZeroSlackSidecarCertificate) :
    certificate.dependencyTable.NoOutcomeActiveClosureValid
      certificate.realizerTable.environment :=
  certificate.accepted.2.2.1

/-- No supplied hereditary or budget node remains active. -/
theorem SelectorHBZeroSlackSidecarCertificate.no_hb_active
    (certificate : SelectorHBZeroSlackSidecarCertificate)
    (node : DirectWire.TerminalPacketHBNode certificate.rankCount) :
    certificate.realizerTable.environment.hbActive node = false :=
  certificate.accepted.2.2.2.1 node

/-- The checked dependency relation remains well founded. -/
theorem SelectorHBZeroSlackSidecarCertificate.depends_wellFounded
    (certificate : SelectorHBZeroSlackSidecarCertificate) :
    WellFounded certificate.dependencyTable.Depends :=
  certificate.accepted.2.2.2.2

/-- Named M179 endpoint: one checked proof-bearing sidecar jointly supplies
    rank-complete selector silence, exact typed-bottom rows, complete HN/BUD
    inactivity, and well-founded exact-rank dependency closure. -/
theorem selector_hb_zeroslack_sidecar_checked_complete
    (certificate : SelectorHBZeroSlackSidecarCertificate) :
    (∀ handle : certificate.family.PacketSelectorHandle,
      certificate.realizerTable.environment.faithful handle = false) ∧
      (∀ handle : certificate.family.PacketSelectorHandle,
        ∃ reason : DirectWire.TerminalPacketTypedRealizerBot
            certificate.family.PacketSelectorHandle certificate.rankCount,
          certificate.realizerTable.claim handle =
            DirectWire.TerminalPacketTypedRealizerClaim.bot reason) ∧
      certificate.dependencyTable.NoOutcomeActiveClosureValid
        certificate.realizerTable.environment ∧
      (∀ node,
        certificate.realizerTable.environment.hbActive node = false) ∧
      WellFounded certificate.dependencyTable.Depends :=
  certificate.accepted

end PNP
