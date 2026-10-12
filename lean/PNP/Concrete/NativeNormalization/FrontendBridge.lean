import PNP.Concrete.NANDFrontendOriginal
import PNP.Concrete.NativeNormalization.MeasuredRawFrontend

namespace PNP.Concrete.NativeNormalization.ClosedFrontendBridge

open PNP.Concrete

theorem index_value (inputs : Nat) (source : LockedNAND.RawSource) :
    NANDFrontend.sourceIndex inputs source = MeasuredRawFrontend.index inputs source := by
  cases source with
  | input index => rfl
  | gate index => rfl
  | constant value => cases value <;> rfl

theorem gate_value (inputs ordinal : Nat) (gate : LockedNAND.RawGate) :
    NANDFrontend.gateClauses inputs ordinal gate = MeasuredRawFrontend.gateData inputs ordinal gate := by
  simp only [NANDFrontend.gateClauses, MeasuredRawFrontend.gateData, index_value]

theorem clauses_value (inputs ordinal : Nat) (gates : List LockedNAND.RawGate) :
    NANDFrontend.gatesClauses inputs ordinal gates = MeasuredRawFrontend.clausesData inputs ordinal gates := by
  induction gates generalizing ordinal with
  | nil => rfl
  | cons gate rest ih =>
      simp only [NANDFrontend.gatesClauses, MeasuredRawFrontend.clausesData, gate_value, ih]

theorem formula_value (circuit : LockedNAND.RawCircuit) :
    NANDFrontend.formula circuit = MeasuredRawFrontend.formulaData circuit := by
  simp only [NANDFrontend.formula, MeasuredRawFrontend.formulaData, clauses_value,
    NANDFrontend.unitClause, NativeTseitin.unitClause, index_value]

theorem frontend_value (formula : CNFFormula) :
    NANDFrontend.formula (CNFToNAND.compileFormula formula) = NativeTseitin.frontend formula := by
  rw [formula_value]
  have checked := MeasuredRawFrontend.build_value formula
  simpa only [MeasuredRawFrontend.build, MeasuredRawFrontend.formula_value,
    MeasuredRawCompiler.build_value] using checked

theorem record_value (formula : CNFFormula) :
    NANDFrontend.circuitData (CNFToNAND.compileFormula formula) =
      NANDFrontend.recordData formula.variableCount (NativeTseitin.frontend formula) := by
  unfold NANDFrontend.circuitData
  rw [CNFToNAND.compileFormula_inputCount, frontend_value]


theorem original_output (input : BitString) :
    NANDFrontend.sourcePolynomial.output input =
      match decodeEncodedCNF input with
      | none => [false]
      | some original => NANDFrontend.recordData original.variableCount (NativeTseitin.frontend original) := by
  rw [NANDFrontend.sourcePolynomial_output]
  cases decoded : decodeEncodedCNF input with
  | none => simp only [NANDFrontend.sourceData, decoded]
  | some original => simp only [NANDFrontend.sourceData, decoded, frontend_value]

theorem original_machine_output (input : BitString) :
    machineOutput NANDFrontend.sourceRawRefinement.machine
      (NANDFrontend.sourceRawRefinement.timeBound.eval (BitString.size input)) input =
      match decodeEncodedCNF input with
      | none => [false]
      | some original => NANDFrontend.recordData original.variableCount (NativeTseitin.frontend original) := by
  rw [NANDFrontend.sourceMachine_output, ← NANDFrontend.sourcePolynomial_output]
  exact original_output input


end PNP.Concrete.NativeNormalization.ClosedFrontendBridge
