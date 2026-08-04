import PNP.ResidualTerminalProjectionMinimum

namespace PNP
namespace DirectWire

def terminalProjectionIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

/-- A single computed coordinate distinguishes the redundant one-gate
    identity from its semantically equivalent zero-gate implementation. -/
def terminalProjectionGatePresenceSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun implementation _coordinate =>
      match implementation.gateCount with
      | 0 => false
      | _ + 1 => true }

def terminalProjectionForgetAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def terminalProjectionKeepAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => true }

theorem terminalProjectionFullMinimum_eq_one :
    terminalFullProfileMinimum terminalProjectionGatePresenceSystem
      redundantIdentityImplementation = 1 := by
  rfl

theorem terminalProjectionQuotientMinimum_eq_zero :
    terminalQuotientProfileMinimum terminalProjectionGatePresenceSystem
      terminalProjectionForgetAll redundantIdentityImplementation = 0 := by
  rfl

theorem terminalProjectionForgottenCoordinate_defect_eq_one :
    terminalProjectionDefect terminalProjectionGatePresenceSystem
      terminalProjectionForgetAll redundantIdentityImplementation = 1 := by
  rfl

example :
    (terminalFullProfileMinimumRealization
      terminalProjectionGatePresenceSystem
      redundantIdentityImplementation).realization.implementation.gateCount = 1 := by
  rw [terminalFullProfileMinimumRealization_gateCount]
  exact terminalProjectionFullMinimum_eq_one

example :
    (terminalQuotientProfileMinimumComparison
      terminalProjectionGatePresenceSystem terminalProjectionForgetAll
      redundantIdentityImplementation).realization.implementation.gateCount = 0 := by
  rw [terminalQuotientProfileMinimumComparison_gateCount]
  exact terminalProjectionQuotientMinimum_eq_zero

example (input : Valuation 1) (output : Fin 1) :
    (terminalFullProfileMinimumRealization
      terminalProjectionGatePresenceSystem
      redundantIdentityImplementation).realization.implementation.candidate.semantics
        input output =
      redundantIdentityImplementation.candidate.semantics input output :=
  (terminalFullProfileMinimumRealization
    terminalProjectionGatePresenceSystem
    redundantIdentityImplementation).realization.equivalent input output

example
    (full : TerminalFullCarrierRealization
      terminalProjectionGatePresenceSystem redundantIdentityImplementation) :
    1 ≤ full.realization.implementation.gateCount := by
  have lower := terminalFullProfileMinimum_le full
  rw [terminalProjectionFullMinimum_eq_one] at lower
  exact lower

example
    (comparison : TerminalQuotientComparison
      terminalProjectionGatePresenceSystem terminalProjectionForgetAll
      redundantIdentityImplementation) :
    0 ≤ comparison.realization.implementation.gateCount := by
  have lower := terminalQuotientProfileMinimum_le comparison
  rw [terminalProjectionQuotientMinimum_eq_zero] at lower
  exact lower

example :
    terminalQuotientProfileMinimum terminalProjectionGatePresenceSystem
        terminalProjectionForgetAll redundantIdentityImplementation ≤
      terminalFullProfileMinimum terminalProjectionGatePresenceSystem
        redundantIdentityImplementation :=
  terminalProjectionMinimum_mono terminalProjectionGatePresenceSystem
    terminalProjectionForgetAll redundantIdentityImplementation

example : terminalProjectionKeepAll.KeepsAll :=
  fun _coordinate => rfl

example :
    terminalQuotientProfileMinimum terminalProjectionGatePresenceSystem
        terminalProjectionKeepAll redundantIdentityImplementation =
      terminalFullProfileMinimum terminalProjectionGatePresenceSystem
        redundantIdentityImplementation :=
  terminalProfileMinima_eq_of_keepsAll terminalProjectionGatePresenceSystem
    terminalProjectionKeepAll redundantIdentityImplementation
    (fun _coordinate => rfl)

theorem terminalProjectionForgottenCoordinate_defect_pos :
    0 < terminalProjectionDefect terminalProjectionGatePresenceSystem
      terminalProjectionForgetAll redundantIdentityImplementation := by
  rw [terminalProjectionForgottenCoordinate_defect_eq_one]
  exact Nat.zero_lt_succ 0

example
    (comparison : TerminalQuotientComparison
      terminalProjectionGatePresenceSystem terminalProjectionForgetAll
      redundantIdentityImplementation)
    (atMinimum : comparison.realization.implementation.gateCount =
      terminalQuotientProfileMinimum terminalProjectionGatePresenceSystem
        terminalProjectionForgetAll redundantIdentityImplementation) :
    ¬TerminalCheckedFullLift comparison :=
  terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum
    terminalProjectionGatePresenceSystem terminalProjectionForgetAll
    redundantIdentityImplementation
    terminalProjectionForgottenCoordinate_defect_pos comparison atMinimum

def terminalProjectionEmptySystem : TerminalProfileSystem 0 0 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def terminalProjectionEmptyImplementation : Implementation 0 0 :=
  ⟨0, Candidate.ofDirectWireWord (.empty : Program 0 0)
    ⟨fun output => Fin.elim0 output⟩⟩

def terminalProjectionEmpty : TerminalProfileProjection 0 :=
  { keep := fun coordinate => Fin.elim0 coordinate }

example :
    terminalFullProfileMinimum terminalProjectionEmptySystem
      terminalProjectionEmptyImplementation = 0 := by
  rfl

example :
    terminalQuotientProfileMinimum terminalProjectionEmptySystem
      terminalProjectionEmpty terminalProjectionEmptyImplementation = 0 := by
  rfl

example :
    terminalProjectionDefect terminalProjectionEmptySystem
      terminalProjectionEmpty terminalProjectionEmptyImplementation = 0 := by
  rfl

example :
    terminalProjectionDefect terminalProjectionGatePresenceSystem
        terminalProjectionKeepAll redundantIdentityImplementation = 0 ↔
      ∃ comparison : TerminalQuotientComparison
          terminalProjectionGatePresenceSystem terminalProjectionKeepAll
          redundantIdentityImplementation,
        comparison.realization.implementation.gateCount =
            terminalQuotientProfileMinimum terminalProjectionGatePresenceSystem
              terminalProjectionKeepAll redundantIdentityImplementation ∧
          TerminalCheckedFullLift comparison :=
  terminalProjectionDefect_eq_zero_iff_exists_checkedFullLiftAtMinimum
    terminalProjectionGatePresenceSystem terminalProjectionKeepAll
    redundantIdentityImplementation

end DirectWire
end PNP
