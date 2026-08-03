import PNP.ResidualTerminalFullBridge

namespace PNP
namespace DirectWire

def terminalZeroGateIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

theorem terminalRedundantToIdentityGain :
    StrictEquivalentGain redundantIdentityImplementation
      terminalZeroGateIdentityImplementation := by
  constructor
  · exact Nat.zero_lt_succ 0
  · exact identityCandidate_equivalent_redundantIdentity

def terminalRedundantWholeSpanWitness :
    WholeSpanResidualWitness redundantIdentityImplementation :=
  { realization :=
      { implementation := terminalZeroGateIdentityImplementation
        equivalent := identityCandidate_equivalent_redundantIdentity }
    cheaper := Nat.zero_lt_succ 0 }

example :
    (terminalize redundantIdentityImplementation).implementation =
      redundantIdentityImplementation := rfl

example :
    (terminalize redundantIdentityImplementation).implementation.gateCount = 1 :=
  rfl

example (input : Valuation 1) (output : Fin 1) :
    (terminalize redundantIdentityImplementation).realize.candidate.semantics
        input output =
      redundantIdentityImplementation.candidate.semantics input output :=
  (terminalize redundantIdentityImplementation).realize_semantics input output

example : terminalFullMinimum redundantIdentityImplementation = 0 := by
  rw [terminalFullMinimum_eq_referenceMinimum,
    redundantIdentity_referenceMinimum]

example :
    IsTerminalFullMinimum redundantIdentityImplementation 0 := by
  rw [isTerminalFullMinimum_iff_eq_referenceMinimum,
    redundantIdentity_referenceMinimum]

example {gateCount : Nat} :
    IsTerminalFullMinimum redundantIdentityImplementation gateCount ↔
      gateCount = 0 := by
  rw [isTerminalFullMinimum_iff_eq_referenceMinimum,
    redundantIdentity_referenceMinimum]

example :
    Nonempty (WholeSpanResidualWitness redundantIdentityImplementation) :=
  ⟨terminalRedundantWholeSpanWitness⟩

example : 0 < residualSlack redundantIdentityImplementation :=
  (residualSlack_pos_iff_exists_wholeSpanResidualWitness
    redundantIdentityImplementation).mpr
      ⟨terminalRedundantWholeSpanWitness⟩

example :
    terminalRedundantWholeSpanWitness.strictEquivalentGain =
      terminalRedundantToIdentityGain := by
  rfl

example :
    residualSlack terminalZeroGateIdentityImplementation <
      residualSlack redundantIdentityImplementation :=
  terminalRedundantWholeSpanWitness.strictResidualDescent

theorem terminalZeroGateIdentityMinimum :
    IsSemanticallyMinimum terminalZeroGateIdentityImplementation := by
  intro gateCount _candidate _equivalent
  exact Nat.zero_le gateCount

theorem terminalZeroGateIdentitySlackZero :
    residualSlack terminalZeroGateIdentityImplementation = 0 :=
  (residualSlack_eq_zero_iff_minimum
    terminalZeroGateIdentityImplementation).mpr
      terminalZeroGateIdentityMinimum

example :
    ¬Nonempty
      (WholeSpanResidualWitness terminalZeroGateIdentityImplementation) :=
  (residualSlack_eq_zero_iff_no_wholeSpanResidualWitness
    terminalZeroGateIdentityImplementation).mp
      terminalZeroGateIdentitySlackZero

def terminalEmptyImplementation : Implementation 0 0 :=
  ⟨0, Candidate.ofDirectWireWord (.empty : Program 0 0)
    ⟨fun output => Fin.elim0 output⟩⟩

example : (terminalize terminalEmptyImplementation).implementation.gateCount = 0 :=
  rfl

example : terminalFullMinimum terminalEmptyImplementation = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (terminalFullMinimum_spec terminalEmptyImplementation).2
    (terminalize terminalEmptyImplementation)

def duplicatedIdentityWord : DirectWireWord 1 0 2 :=
  ⟨fun _output => .input fin1Zero⟩

def duplicatedIdentityImplementation : Implementation 1 2 :=
  ⟨0, Candidate.ofDirectWireWord (.empty : Program 1 0)
    duplicatedIdentityWord⟩

example (input : Valuation 1) (output : Fin 2) :
    (terminalize duplicatedIdentityImplementation).realize.candidate.semantics
        input output =
      duplicatedIdentityImplementation.candidate.semantics input output :=
  (terminalize duplicatedIdentityImplementation).realize_semantics input output

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (gateCount : Nat) :
    IsTerminalFullMinimum current gateCount ↔
      gateCount = referenceMinimum current :=
  isTerminalFullMinimum_iff_eq_referenceMinimum current

end DirectWire
end PNP
