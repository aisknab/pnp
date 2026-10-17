import PNP.Concrete.ResidualReduction.SourceCoefficientGateState

/-! Read the actual scalar head, construct the required constant-one word,
and retain its exact affine comparison. Arbitrary saved tail data is protected;
the saved boolean is produced by the program, never supplied as a premise. -/

namespace PNP.Concrete.ResidualReduction.SourceCoefficientGateHead
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState (work data zero)
open PNP.Concrete.ResidualReduction.SourceCoefficientGateState

def saveHead : Block 18 := .seq (.action (.copy 16 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 11 0))
def prepare : Block 18 := .seq (.action (.copy 0 16)) <|
  .seq (.action (.copy 5 7)) <| .seq (.action (.copy 1 13)) (.action (.clear 7))
def storeResult : Block 18 := .seq (.action (.copy 16 6)) <|
  .seq (.action (.clear 6)) <| .seq (.action (.clear 1)) (.action (.copy 0 11))
def block : Block 18 := .seq (scalar SourceScalarRow.factor) <|
  .seq saveHead <| .seq (scalar SourceTailPolynomialAffine.one) <|
  .seq prepare <| .seq (core SourceRowCoefficientInstructions.equal) storeResult
def fuel (n : Nat) : Nat := 24 * n + 45

theorem block_exec {n : Nat} (h : Affine n) (q : Quadratic n)
    (suffix savedStream : BitString) (saved : Saved) :
    Exec block (full (work (affineWord h ++ suffix)) SourceScalarState.emptySaved
      (data savedStream q) saved) (fuel n)
      (state suffix q {saved with head := [aEq h (aConst n true)]}) := by
  let beforeData := data savedStream q
  let afterData := data suffix q
  let headSaved := {saved with head := affineWord h}
  let readDone := {work suffix with output := affineWord h}
  let oneDone := {work suffix with reserved := affineWord (aConst n true)}
  let compareReady := SourceRowCoefficientInstructions.binaryReady (work []) h (aConst n true)
  let compared := SourceRowCoefficientInstructions.compared (work []) h (aConst n true)
  have read := scalar_exec (SourceScalarRow.factor_exec h q suffix savedStream []) saved
  have save : Exec saveHead (full readDone SourceScalarState.emptySaved beforeData saved) 3
      (full (work suffix) SourceScalarState.emptySaved afterData headSaved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have one := scalar_exec (SourceTailPolynomialAffine.one_exec q suffix suffix) headSaved
  have load : Exec prepare (full oneDone SourceScalarState.emptySaved afterData headSaved) 4
      (full compareReady SourceScalarState.emptySaved afterData headSaved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have compare := core_exec (SourceRowCoefficientInstructions.equal_exec (work []) h (aConst n true))
    SourceScalarState.emptySaved afterData headSaved
  have finish : Exec storeResult (full compared SourceScalarState.emptySaved afterData headSaved) 4
      (state suffix q {saved with head := [aEq h (aConst n true)]}) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : fuel n = SourceScalarRow.factorFuel n +
      (3 + (SourceTailPolynomialAffine.oneFuel n + (4 + ((12 * (n + 1) + 5) + 4)))) := by
    simp only [fuel,SourceScalarRow.factorFuel,SourceTailPolynomialAffine.oneFuel]
    omega
  simpa only [block,cost,beforeData,afterData,headSaved,readDone,oneDone,compareReady,compared,work,full] using
    Exec.seq read (Exec.seq save (Exec.seq one (Exec.seq load (Exec.seq compare finish))))

end PNP.Concrete.ResidualReduction.SourceCoefficientGateHead
