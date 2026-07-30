/-
Copyright (c) 2026 PNP Labs.

The concrete strict-version-zero polynomial many-one reduction from encoded
NAND satisfiability to the encoded locked-NAND threshold language.  All
machine construction, exact output, polynomial bounds, and raw refinement
are supplied by the already-audited parser/emitter composition.
-/

import PNP.Concrete.LockedNANDTargetEmitter

namespace PNP.Concrete.LockedNAND

/-- The strict parser/emitter composition, packaged as a concrete polynomial
many-one reduction between the exact encoded languages. -/
def strictLockedNANDPolynomialReduction :
    PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold :=
  { function :=
      TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction
    correctness := by
      intro bits
      rw [
        TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction_output
      ]
      exact buildLockedNANDInstance_correct bits }

theorem strictLockedNANDPolynomialReduction_function :
    strictLockedNANDPolynomialReduction.function =
      TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction :=
  rfl

theorem strictLockedNANDPolynomialReduction_output
    (bits : BitString) :
    strictLockedNANDPolynomialReduction.function.output bits =
      buildLockedNANDInstance bits := by
  change
    TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction.output
        bits =
      buildLockedNANDInstance bits
  exact
    TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction_output
      bits

theorem strictLockedNANDPolynomialReduction_correct
    (bits : BitString) :
    EncodedNANDSAT bits ↔
      EncodedLockedNANDThreshold
        (strictLockedNANDPolynomialReduction.function.output bits) :=
  strictLockedNANDPolynomialReduction.correctness bits

theorem encodedNANDSAT_reducesTo_encodedLockedNANDThreshold :
    ReducesTo EncodedNANDSAT EncodedLockedNANDThreshold :=
  ⟨strictLockedNANDPolynomialReduction⟩

/-- The packaged reduction retains the exact recursive raw-machine
refinement of its function program. -/
def strictLockedNANDPolynomialReduction_rawRefinement :
    FunctionProgram.RawRefinement
      strictLockedNANDPolynomialReduction.function.program := by
  change FunctionProgram.RawRefinement
    TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction.program
  exact TargetEmitterControllerCompiled.strictLockedNANDRawRefinement

/-- Proposition-level publication pin for the retained refinement witness. -/
theorem strictLockedNANDPolynomialReduction_hasRawRefinement :
    Nonempty
      (FunctionProgram.RawRefinement
        strictLockedNANDPolynomialReduction.function.program) :=
  ⟨strictLockedNANDPolynomialReduction_rawRefinement⟩

end PNP.Concrete.LockedNAND
