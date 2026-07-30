import PNP.Concrete.LockedNANDPolynomialReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace PNP.Concrete.LockedNANDPolynomialReductionRegression

open PNP.Concrete
open LockedNAND

private def zeroGateCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .constant false }

private def oneGateCircuit : RawCircuit :=
  { inputCount := 0
    gates :=
      [{ left := .constant false
         right := .constant false }]
    output := .gate 0 }

private def multiGateCircuit : RawCircuit :=
  { inputCount := 1
    gates :=
      [ { left := .input 0
          right := .constant true }
      , { left := .gate 0
          right := .gate 0 } ]
    output := .gate 1 }

private def invalidReferenceCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .gate 0 }

example :
    strictLockedNANDPolynomialReduction.function =
      TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction :=
  strictLockedNANDPolynomialReduction_function

example (bits : BitString) :
    strictLockedNANDPolynomialReduction.function.output bits =
      buildLockedNANDInstance bits :=
  strictLockedNANDPolynomialReduction_output bits

example (bits : BitString) :
    EncodedNANDSAT bits ↔
      EncodedLockedNANDThreshold
        (strictLockedNANDPolynomialReduction.function.output bits) :=
  strictLockedNANDPolynomialReduction_correct bits

example :
    ReducesTo EncodedNANDSAT EncodedLockedNANDThreshold :=
  encodedNANDSAT_reducesTo_encodedLockedNANDThreshold

example :
    FunctionProgram.RawRefinement
      strictLockedNANDPolynomialReduction.function.program :=
  strictLockedNANDPolynomialReduction_rawRefinement

example :
    Nonempty
      (FunctionProgram.RawRefinement
        strictLockedNANDPolynomialReduction.function.program) :=
  strictLockedNANDPolynomialReduction_hasRawRefinement

/-! Malformed and intrinsically invalid inputs remain fail closed. -/

example :
    strictLockedNANDPolynomialReduction.function.output [] = [] := by
  rw [strictLockedNANDPolynomialReduction_output]
  rfl

example :
    ¬ EncodedLockedNANDThreshold
      (strictLockedNANDPolynomialReduction.function.output []) := by
  rw [strictLockedNANDPolynomialReduction_output]
  exact empty_not_encodedLockedNANDThreshold

example :
    strictLockedNANDPolynomialReduction.function.output
        (encodeCircuit invalidReferenceCircuit) =
      [] := by
  rw [strictLockedNANDPolynomialReduction_output]
  exact buildLockedNANDInstance_of_malformed
    (encodeCircuit invalidReferenceCircuit) (by
      unfold decodeElaboratedCircuit
      rw [decodeCircuit_encodeCircuit]
      rfl)

/-! The same reduction theorem covers valid zero-, one-, and multi-gate
circuits without a size-specific implementation. -/

example :
    EncodedNANDSAT (encodeCircuit zeroGateCircuit) ↔
      EncodedLockedNANDThreshold
        (strictLockedNANDPolynomialReduction.function.output
          (encodeCircuit zeroGateCircuit)) :=
  strictLockedNANDPolynomialReduction_correct _

example :
    EncodedNANDSAT (encodeCircuit oneGateCircuit) ↔
      EncodedLockedNANDThreshold
        (strictLockedNANDPolynomialReduction.function.output
          (encodeCircuit oneGateCircuit)) :=
  strictLockedNANDPolynomialReduction_correct _

example :
    EncodedNANDSAT (encodeCircuit multiGateCircuit) ↔
      EncodedLockedNANDThreshold
        (strictLockedNANDPolynomialReduction.function.output
          (encodeCircuit multiGateCircuit)) :=
  strictLockedNANDPolynomialReduction_correct _

end PNP.Concrete.LockedNANDPolynomialReductionRegression
