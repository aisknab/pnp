import PNP.Concrete.CNFToNANDPolynomialReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace PNP.Concrete.CNFToNANDPolynomialReductionRegression

open PNP.Concrete
open PNP.Concrete.CNFToNAND

private def emptyFormula : CNFFormula :=
  { variableCount := 0, clauses := [] }

private def emptyClauseFormula : CNFFormula :=
  { variableCount := 0, clauses := [[]] }

private def positiveFormula : CNFFormula :=
  { variableCount := 1
    clauses := [[{ positive := true, variableIndex := 0 }]] }

private def negativeFormula : CNFFormula :=
  { variableCount := 1
    clauses := [[{ positive := false, variableIndex := 0 }]] }

private def outOfRangeFormula : CNFFormula :=
  { variableCount := 0
    clauses := [[{ positive := true, variableIndex := 0 }]] }

private def mixedFormula : CNFFormula :=
  { variableCount := 2
    clauses :=
      [ [ { positive := true, variableIndex := 0 }
        , { positive := false, variableIndex := 1 } ]
      , [ { positive := true, variableIndex := 1 } ] ] }

/-! ## Fixed machine and polynomial -/

example :
    CNFToNANDCompilerMachine.machine.rules.length = 135070 := by
  simpa [CNFToNANDCompilerMachine.ruleCount] using
    CNFToNANDCompilerMachine.rules_length_literal

example (bitLength : Nat) :
    CNFToNANDCompilerPolynomialBound.allInputWorkTimePolynomial.eval
        bitLength =
      CNFToNANDCompilerPolynomialBound.allInputWorkBound bitLength :=
  CNFToNANDCompilerPolynomialBound.allInputWorkTimePolynomial_eval
    bitLength

example (bitLength : Nat) :
    CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
        bitLength =
      6 *
        CNFToNANDCompilerPolynomialBound.allInputWorkBound bitLength :=
  CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial_eval bitLength

/-! ## One unconditional machine interface covers short, odd, even,
all-zero, and all-one source words. -/

example (bits : BitString) :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape bits)) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF bits) ∧
      (encodeWorkTape final.tape).outputBits =
        compileEncodedCNFToNAND bits :=
  CNFToNANDCompilerTotalTrace.allInput_bounded_exact bits

example :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound 0 ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape [])) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF []) ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  simpa only [
    List.length_nil,
    compileEncodedCNFToNAND_of_malformed [] (by rfl)
  ] using
    CNFToNANDCompilerTotalTrace.allInput_bounded_exact []

example :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          [false].length ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape [false])) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF [false]) ∧
      (encodeWorkTape final.tape).outputBits =
      compileEncodedCNFToNAND [false] :=
  CNFToNANDCompilerTotalTrace.allInput_bounded_exact [false]

example :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          [true].length ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape [true])) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF [true]) ∧
      (encodeWorkTape final.tape).outputBits =
        compileEncodedCNFToNAND [true] :=
  CNFToNANDCompilerTotalTrace.allInput_bounded_exact [true]

example :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          [false, false, false].length ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape [false, false, false])) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF
          [false, false, false]) ∧
      (encodeWorkTape final.tape).outputBits =
        compileEncodedCNFToNAND [false, false, false] :=
  CNFToNANDCompilerTotalTrace.allInput_bounded_exact
    [false, false, false]

example :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          [false, false, false, false].length ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape [false, false, false, false])) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF
          [false, false, false, false]) ∧
      (encodeWorkTape final.tape).outputBits =
        compileEncodedCNFToNAND [false, false, false, false] :=
  CNFToNANDCompilerTotalTrace.allInput_bounded_exact
    [false, false, false, false]

example :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          [true, true, true, true].length ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape [true, true, true, true])) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      (final.state =
          CNFToNANDCompilerMachine.machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF
          [true, true, true, true]) ∧
      (encodeWorkTape final.tape).outputBits =
        compileEncodedCNFToNAND [true, true, true, true] :=
  CNFToNANDCompilerTotalTrace.allInput_bounded_exact
    [true, true, true, true]

/-! ## Canonical formulas exercise all structural compiler branches. -/

example (formula : CNFFormula) :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF formula) =
      LockedNAND.encodeCircuit (compileFormula formula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF formula) formula
      (decodeEncodedCNF_canonical formula),
  ]

example :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF emptyFormula) =
      LockedNAND.encodeCircuit (compileFormula emptyFormula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF emptyFormula) emptyFormula
      (decodeEncodedCNF_canonical emptyFormula),
  ]

example :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF emptyClauseFormula) =
      LockedNAND.encodeCircuit (compileFormula emptyClauseFormula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF emptyClauseFormula) emptyClauseFormula
      (decodeEncodedCNF_canonical emptyClauseFormula),
  ]

example :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF positiveFormula) =
      LockedNAND.encodeCircuit (compileFormula positiveFormula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF positiveFormula) positiveFormula
      (decodeEncodedCNF_canonical positiveFormula),
  ]

example :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF negativeFormula) =
      LockedNAND.encodeCircuit (compileFormula negativeFormula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF negativeFormula) negativeFormula
      (decodeEncodedCNF_canonical negativeFormula),
  ]

example :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF outOfRangeFormula) =
      LockedNAND.encodeCircuit (compileFormula outOfRangeFormula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF outOfRangeFormula) outOfRangeFormula
      (decodeEncodedCNF_canonical outOfRangeFormula),
  ]

example :
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output
        (encodeCNF mixedFormula) =
      LockedNAND.encodeCircuit (compileFormula mixedFormula) := by
  rw [
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output,
    compileEncodedCNFToNAND_of_decoded
      (encodeCNF mixedFormula) mixedFormula
      (decodeEncodedCNF_canonical mixedFormula),
  ]

/-! ## Compiled and reduction publication pins -/

example (bits : BitString) :
    machineOutput CNFToNANDCompilerCompiled.compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits =
      compileEncodedCNFToNAND bits :=
  CNFToNANDCompilerCompiled.compiledMachineOutput_eq_compileEncodedCNFToNAND
    bits

example (bits : BitString) :
    boundedDecide CNFToNANDCompilerCompiled.compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits = .accept ↔
      CNFSourceParser.ValidEncodedCNF bits :=
  CNFToNANDCompilerCompiled.compiledBoundedDecide_accept_iff bits

example (bits : BitString) :
    boundedDecide CNFToNANDCompilerCompiled.compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits ≠ .timeout :=
  CNFToNANDCompilerCompiled.compiledBoundedDecide_ne_timeout bits

example :
    FunctionProgram.RawRefinement
      CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.program :=
  CNFToNANDCompilerCompiled.cnfToNANDRawRefinement

example :
    cnfToNANDPolynomialReduction.function =
      CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction :=
  cnfToNANDPolynomialReduction_function

example (bits : BitString) :
    cnfToNANDPolynomialReduction.function.output bits =
      compileEncodedCNFToNAND bits :=
  cnfToNANDPolynomialReduction_output bits

example (bits : BitString) :
    CNFSAT bits ↔
      LockedNAND.EncodedNANDSAT
        (cnfToNANDPolynomialReduction.function.output bits) :=
  cnfToNANDPolynomialReduction_correct bits

example :
    ReducesTo CNFSAT LockedNAND.EncodedNANDSAT :=
  cnfSAT_reducesTo_encodedNANDSAT

example :
    FunctionProgram.RawRefinement
      cnfToNANDPolynomialReduction.function.program :=
  cnfToNANDPolynomialReduction_rawRefinement

example (bits : BitString) :
    cnfToLockedNANDPolynomialReduction.function.output bits =
      buildLockedNANDFromCNF bits :=
  cnfToLockedNANDPolynomialReduction_output bits

example (bits : BitString) :
    CNFSAT bits ↔
      LockedNAND.EncodedLockedNANDThreshold
        (cnfToLockedNANDPolynomialReduction.function.output bits) :=
  cnfToLockedNANDPolynomialReduction_correct bits

example :
    ReducesTo CNFSAT
      LockedNAND.EncodedLockedNANDThreshold :=
  cnfSAT_reducesTo_encodedLockedNANDThreshold

example :
    FunctionProgram.RawRefinement
      cnfToLockedNANDPolynomialReduction.function.program :=
  cnfToLockedNANDPolynomialReduction_rawRefinement

example :
    Nonempty
      (FunctionProgram.RawRefinement
        cnfToLockedNANDPolynomialReduction.function.program) :=
  cnfToLockedNANDPolynomialReduction_hasRawRefinement

end PNP.Concrete.CNFToNANDPolynomialReductionRegression
