/-
Copyright (c) 2026 PNP Labs.

Concrete polynomial many-one reductions obtained from the literal
all-bitstring CNF-to-NAND compiler.  The first reduction targets encoded
NAND satisfiability directly.  The second is the explicit composition with
the already-audited strict locked-NAND reduction.
-/

import PNP.Concrete.CNFToNANDCompilerCompiled
import PNP.Concrete.LockedNANDPolynomialReduction

namespace PNP.Concrete.CNFToNAND

open PNP.Concrete

/-! ## Direct CNF-to-NAND reduction -/

/-- The literal compiler packaged as a concrete polynomial many-one
reduction from strict encoded CNF satisfiability to strict encoded NAND
satisfiability. -/
def cnfToNANDPolynomialReduction :
    PolynomialReduction CNFSAT LockedNAND.EncodedNANDSAT :=
  { function :=
      CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction
    correctness := by
      intro bits
      rw [
        CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output
      ]
      exact compileEncodedCNFToNAND_correct bits }

theorem cnfToNANDPolynomialReduction_function :
    cnfToNANDPolynomialReduction.function =
      CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction :=
  rfl

theorem cnfToNANDPolynomialReduction_output
    (bits : BitString) :
    cnfToNANDPolynomialReduction.function.output bits =
      compileEncodedCNFToNAND bits := by
  change
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.output bits =
      compileEncodedCNFToNAND bits
  exact
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output bits

theorem cnfToNANDPolynomialReduction_correct
    (bits : BitString) :
    CNFSAT bits ↔
      LockedNAND.EncodedNANDSAT
        (cnfToNANDPolynomialReduction.function.output bits) :=
  cnfToNANDPolynomialReduction.correctness bits

theorem cnfSAT_reducesTo_encodedNANDSAT :
    ReducesTo CNFSAT LockedNAND.EncodedNANDSAT :=
  ⟨cnfToNANDPolynomialReduction⟩

/-- The direct packaged reduction retains the compiler's exact literal
raw-machine implementation. -/
def cnfToNANDPolynomialReduction_rawRefinement :
    FunctionProgram.RawRefinement
      cnfToNANDPolynomialReduction.function.program := by
  change FunctionProgram.RawRefinement
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.program
  exact CNFToNANDCompilerCompiled.cnfToNANDRawRefinement

theorem cnfToNANDPolynomialReduction_hasRawRefinement :
    Nonempty
      (FunctionProgram.RawRefinement
        cnfToNANDPolynomialReduction.function.program) :=
  ⟨cnfToNANDPolynomialReduction_rawRefinement⟩

/-! ## Explicit composition to locked NAND -/

/-- Compose the physical CNF compiler with the physical strict locked-NAND
builder.  This remains a finite function-program tree and therefore retains
an exact recursively compiled raw-machine refinement. -/
def cnfToLockedNANDPolynomialReduction :
    PolynomialReduction CNFSAT
      LockedNAND.EncodedLockedNANDThreshold :=
  PolynomialReduction.compose
    cnfToNANDPolynomialReduction
    LockedNAND.strictLockedNANDPolynomialReduction

private theorem cnfToLockedNANDPolynomialReduction_function_eq :
    cnfToLockedNANDPolynomialReduction.function =
      PolynomialTimeFunction.compose
        cnfToNANDPolynomialReduction.function
        LockedNAND.strictLockedNANDPolynomialReduction.function :=
  rfl

theorem cnfToLockedNANDPolynomialReduction_output
    (bits : BitString) :
    cnfToLockedNANDPolynomialReduction.function.output bits =
      buildLockedNANDFromCNF bits := by
  rw [cnfToLockedNANDPolynomialReduction_function_eq,
    PolynomialTimeFunction.compose_output,
    cnfToNANDPolynomialReduction_output,
    LockedNAND.strictLockedNANDPolynomialReduction_output]
  rfl

theorem cnfToLockedNANDPolynomialReduction_correct
    (bits : BitString) :
    CNFSAT bits ↔
      LockedNAND.EncodedLockedNANDThreshold
        (cnfToLockedNANDPolynomialReduction.function.output bits) :=
  cnfToLockedNANDPolynomialReduction.correctness bits

theorem cnfSAT_reducesTo_encodedLockedNANDThreshold :
    ReducesTo CNFSAT
      LockedNAND.EncodedLockedNANDThreshold :=
  ⟨cnfToLockedNANDPolynomialReduction⟩

private theorem cnfToLockedNANDPolynomialReduction_program_eq :
    cnfToLockedNANDPolynomialReduction.function.program =
      .compose
        cnfToNANDPolynomialReduction.function.program
        LockedNAND.strictLockedNANDPolynomialReduction.function.program :=
  rfl

/-- Exact raw implementation of the two-stage reduction, obtained only from
the two leaf refinements and the generic literal sequential compiler. -/
def cnfToLockedNANDPolynomialReduction_rawRefinement :
    FunctionProgram.RawRefinement
      cnfToLockedNANDPolynomialReduction.function.program := by
  rw [cnfToLockedNANDPolynomialReduction_program_eq]
  exact FunctionProgram.RawRefinement.compose
    cnfToNANDPolynomialReduction_rawRefinement
    LockedNAND.strictLockedNANDPolynomialReduction_rawRefinement

theorem cnfToLockedNANDPolynomialReduction_hasRawRefinement :
    Nonempty
      (FunctionProgram.RawRefinement
        cnfToLockedNANDPolynomialReduction.function.program) :=
  ⟨cnfToLockedNANDPolynomialReduction_rawRefinement⟩

end PNP.Concrete.CNFToNAND
