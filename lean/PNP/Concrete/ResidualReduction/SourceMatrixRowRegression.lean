import Lean
import PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions

namespace PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourcePolarInstructions
open PNP.Concrete.ResidualReduction.SourceCoefficientInstructions

-- Constants, selected flags, and repeated coefficients are deliberately mixed.
private def cross : Row 2 := ⟨true, (true, (false, true)), (false, (true, false))⟩
private def parallel : Row 2 := ⟨false, (true, (true, false)), (true, (true, true))⟩
private def source : Family 2 := [cross, parallel]

example : rowWord cross = [true, true, false, true, false, true, false] := rfl
example : rowWord parallel = [false, true, true, false, true, true, true] := rfl
example : polarBit cross 0 1 = true := rfl
example : polarBit cross 1 0 = true := rfl
example : polarBit cross 0 0 = false := rfl
example : polarBit cross 1 1 = false := rfl
example : polarBit parallel 0 1 = false := rfl
example : polarBit {cross with selected := false} 0 1 = true := rfl
example : polarBit (⟨true, (true, (false, false)), (false, (true, true))⟩ : Row 2) 0 1 = true := rfl

example : (codec.encode ⟨2, source⟩).length = 20 := rfl
example : codec.encode ⟨3, ([] : Family 3)⟩ = [true, true, true, false, false] := rfl
example : codec.decode [] = none := rfl
example : codec.decode [false] = none := rfl
example : codec.decode [true, true] = none := rfl
example : codec.decode [false, false, true] = none := rfl
example : codec.decode [false, false, false] = none := rfl
example : codec.decode [false, true, false, false, true] = none := rfl
example : codec.decode [false, true, false, false, true, false] =
    some ⟨0, [⟨false, true, false⟩]⟩ := rfl

example : MatrixInstructions.matrixBits (SourceClosure.affineMaskRows source) =
    [false, false, false, true, false, false, true, false, false, false, false, false] := by
  rw [affineMask_bytes]; rfl
example : MatrixInstructions.matrixBits (SourceClosure.affineMaskRows ([] : Family 2)) =
    [false, false, false, false] := by rw [affineMask_bytes]; rfl
example : MatrixInstructions.matrixBits
    (SourceClosure.affineMaskRows ([⟨true, true, false⟩] : Family 0)) = [] := rfl

-- Actual source-program execution, not only evaluation of the specification.
private def code : Program 12 := matrixRow.program 0 8
private def start := (working 2 0 1 [] (familyBits source) [true, false] [true]).store
set_option maxRecDepth 8192 in
example : (BitRegister.run code 187 ⟨.running 0, start⟩).control = .accepted := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run code 187 ⟨.running 0, start⟩).store.get 8 = [false, false, true, true] := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run code 187 ⟨.running 0, start⟩).store.get 3 = [true, false] := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run code 187 ⟨.running 0, start⟩).store.get 0 = [] := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run code 3
    ⟨.running 0, (working 2 0 1 [] [] [] [true]).store⟩).store.get 8 = [false, true] := rfl

-- Uniform all-family and all-coordinate contracts; finite fixtures earn no credit.
example (n : Nat) (F : Family n) : codec.decode (codec.encode ⟨n, F⟩) = some ⟨n, F⟩ :=
  roundtrip n F
example {n : Nat} (F : Family n) (i j : Fin n) (output : BitString) :
    Exec matrixRow (working n i.val j.val [] (familyBits F) [] output).store
      (loopFuel n i.val j.val F.length + 1)
      (working n i.val j.val [] [] []
        ((F.map (fun r => polarBit r i.val j.val) ++ [false]).reverse ++ output)).store :=
  matrixRow_exec F i j [] output
example {n : Nat} (F : Family n) (i j : Fin n) :
    loopFuel n i.val j.val F.length + 1 ≤ (24 * n + 62) * F.length + 2 :=
  matrixRowFuel_bound F i j
example (r : Registers) (k : Nat) :
    Exec read ({r with remaining := List.replicate k true}).store (3 * k + 3)
      ({r with input := r.input.drop k, remaining := [], excess := bitAt r.input k :: r.excess}).store :=
  read_exec r k
example : bitAt [] 100 = false := rfl
example : bitAt [true, false, true] 1 = false := rfl
example : bitAt [true, false, true] 2 = true := rfl
example : bitAt [true, false, true] 3 = false := rfl

-- Fail closed on project axioms, sorryAx, and accidental classical choice.
run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.SourceMatrixEncoding.affineMask_bytes,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEncoding.affineMatrixPacket_bound,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEncoding.roundtrip,
    ``PNP.Concrete.ResidualReduction.SourceCoefficientInstructions.drop_all,
    ``PNP.Concrete.ResidualReduction.SourceCoefficientInstructions.read_exec,
    ``PNP.Concrete.ResidualReduction.SourceCoefficientInstructions.emitPolar_exec,
    ``PNP.Concrete.ResidualReduction.SourcePolarInstructions.rowBlock_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions.exact_equation_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions.matrixRowFuel_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceMatrixEncoding.affineMask_bytes
#print axioms PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions.exact_equation_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions.matrixRowFuel_bound

end PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions.Regression
