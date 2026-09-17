/-
Copyright (c) 2026 PNP Labs.

Structural transitions preserve previous global gate identities and complete
charge/removal history. The local "original" owner is lifted through the actual
preceding program ledger, never treated as a new global source coordinate.

This is an offered-program accounting theorem, not full manuscript profiles,
a certificate-discovery strategy, unconditional ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireOpenProgramOwnership

namespace PNP.DirectWire.WireOpenProgram.ProgramOwnership

open WireObligationHistory (State)

variable {inputs outputs fields initialGates : Nat}
variable {source : WireCarrier inputs outputs fields} {before : State source}
variable {event : RawEvent} {raw : List (Nat × Nat)}

theorem advance_structural_origin
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (kind : event.action = .structural raw)
    (receipt : WireStructuralState.Receipt before raw)
    (gate : Fin before.current.implementation.gateCount) :
    (ledger.advance position (.structural before event raw kind receipt)).origin
        (before.current.reindexForwardGate receipt.relabeling gate) = ledger.origin gate := by
  change ledger.liftOrigin position
    (receipt.ownership.origin (before.current.reindexForwardGate receipt.relabeling gate)) = _
  rw [receipt.ownership_origin_forward]
  rfl

theorem advance_structural_charged
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (kind : event.action = .structural raw)
    (receipt : WireStructuralState.Receipt before raw) :
    (ledger.advance position (.structural before event raw kind receipt)).charged =
      ledger.charged := by
  change ledger.charged ++ receipt.ownership.charged.map (ledger.liftOrigin position) = _
  rw [receipt.ownership_charged, List.map_nil, List.append_nil]

theorem advance_structural_removed
    (ledger : ProgramOwnership initialGates before.current.implementation.gateCount)
    (position : Nat) (kind : event.action = .structural raw)
    (receipt : WireStructuralState.Receipt before raw) :
    (ledger.advance position (.structural before event raw kind receipt)).removed =
      ledger.removed := by
  change ledger.removed ++ receipt.ownership.removed.map (ledger.liftOrigin position) = _
  rw [receipt.ownership_removed, List.map_nil, List.append_nil]

end PNP.DirectWire.WireOpenProgram.ProgramOwnership
