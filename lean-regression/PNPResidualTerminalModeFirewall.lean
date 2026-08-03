import PNP.ResidualTerminalModeFirewall

namespace PNP
namespace DirectWire

def terminalModeIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def terminalModeIdentityRealization :
    TerminalFullRealization redundantIdentityImplementation :=
  { implementation := terminalModeIdentityImplementation
    equivalent := identityCandidate_equivalent_redundantIdentity }

/-- One concrete computed profile bit distinguishes a zero-gate identity from
    the semantically equivalent redundant one-gate identity. -/
def terminalModeGatePresenceSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun implementation _coordinate =>
      match implementation.gateCount with
      | 0 => false
      | _ + 1 => true }

def terminalModeDropOnlyCoordinate : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def terminalModeKeepOnlyCoordinate : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => true }

def terminalModeDroppedComparison :
    TerminalQuotientComparison terminalModeGatePresenceSystem
      terminalModeDropOnlyCoordinate redundantIdentityImplementation :=
  { realization := terminalModeIdentityRealization
    keptProfileEqual := by
      intro coordinate kept
      change false = true at kept
      exact False.elim (Bool.noConfusion kept) }

theorem terminalModeDroppedComparison_mismatch :
    terminalModeDroppedComparison.ForgottenMismatch := by
  refine ⟨fin1Zero, rfl, ?_⟩
  intro equal
  exact Bool.noConfusion equal

example : ¬TerminalCheckedFullLift terminalModeDroppedComparison :=
  terminalQuotientEqualityNotConstructive terminalModeDroppedComparison
    terminalModeDroppedComparison_mismatch

def terminalModeRedundantFullRealization :
    TerminalFullCarrierRealization terminalModeGatePresenceSystem
      redundantIdentityImplementation :=
  { realization := terminalize redundantIdentityImplementation
    profileEqual := fun _coordinate => rfl }

example :
    (terminalModeRedundantFullRealization.project
      (projection := terminalModeDropOnlyCoordinate)).realization.implementation =
        redundantIdentityImplementation := rfl

example :
    (terminalModeRedundantFullRealization.project
      (projection := terminalModeDropOnlyCoordinate)).realization.implementation.gateCount =
        redundantIdentityImplementation.gateCount :=
  terminalModeRedundantFullRealization.project_gateCount

example (input : Valuation 1) (output : Fin 1) :
    (terminalModeRedundantFullRealization.project
      (projection := terminalModeDropOnlyCoordinate)).realization.implementation.candidate.semantics
        input output =
      redundantIdentityImplementation.candidate.semantics input output :=
  terminalModeRedundantFullRealization.project_semantics input output

example :
    TerminalCheckedFullLift
      (terminalModeRedundantFullRealization.project
        (projection := terminalModeDropOnlyCoordinate)) :=
  terminalModeRedundantFullRealization.checkedFullLift

example : terminalModeKeepOnlyCoordinate.KeepsAll :=
  fun _coordinate => rfl

example :
    TerminalCheckedFullLift
      (terminalModeRedundantFullRealization.project
        (projection := terminalModeKeepOnlyCoordinate)) :=
  (terminalModeRedundantFullRealization.project
    (projection := terminalModeKeepOnlyCoordinate)).checkedFullLift_of_keepsAll
      (fun _coordinate => rfl)

def terminalModeObligationSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .obligation
    observe := fun _implementation _coordinate => false }

def terminalModeObligationFull :
    TerminalFullCarrierRealization terminalModeObligationSystem
      redundantIdentityImplementation :=
  { realization := terminalize redundantIdentityImplementation
    profileEqual := fun _coordinate => rfl }

theorem terminalModeCurrentObligationsDischarged :
    terminalModeObligationSystem.ObligationsDischarged
      redundantIdentityImplementation := by
  intro _coordinate _role
  rfl

example :
    terminalModeObligationSystem.ObligationsDischarged
      terminalModeObligationFull.realization.implementation :=
  terminalModeObligationFull.obligationsDischarged
    terminalModeCurrentObligationsDischarged

def terminalModeEmptyProfileSystem : TerminalProfileSystem 0 0 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def terminalModeEmptyImplementation : Implementation 0 0 :=
  ⟨0, Candidate.ofDirectWireWord (.empty : Program 0 0)
    ⟨fun output => Fin.elim0 output⟩⟩

def terminalModeEmptyProjection : TerminalProfileProjection 0 :=
  { keep := fun coordinate => Fin.elim0 coordinate }

def terminalModeEmptyFull :
    TerminalFullCarrierRealization terminalModeEmptyProfileSystem
      terminalModeEmptyImplementation :=
  { realization := terminalize terminalModeEmptyImplementation
    profileEqual := fun coordinate => Fin.elim0 coordinate }

example :
    TerminalCheckedFullLift
      (terminalModeEmptyFull.project
        (projection := terminalModeEmptyProjection)) :=
  (terminalModeEmptyFull.project
    (projection := terminalModeEmptyProjection)).checkedFullLift_of_keepsAll
      (fun coordinate => Fin.elim0 coordinate)

example {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {projection : TerminalProfileProjection profileWidth}
    {current : Implementation inputs outputs}
    (comparison : TerminalQuotientComparison system projection current) :
    TerminalCheckedFullLift comparison ↔ comparison.FullProfileEqual :=
  terminalCheckedFullLift_iff_fullProfileEqual comparison

end DirectWire
end PNP
