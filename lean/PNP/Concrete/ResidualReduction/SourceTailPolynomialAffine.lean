import PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions

/-! Construct the affine contribution to a tail polynomial. The constant-one
factor is generated from the dimension by literal pushes, then the actual
input factor is multiplied and accumulated by the existing coefficient code. -/

namespace PNP.Concrete.ResidualReduction.SourceTailPolynomialAffine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceScalarState
open PNP.Concrete.ResidualReduction.MatrixInstructions

theorem product_one {n : Nat} (u : Affine n) :
    qProduct (aConst n true) u = qOfAffine u := by
  apply SourceClosure.quadratic_eval_ext
  intro x
  simp only [qProduct_eval,aConst_eval,Bool.true_and,qOfAffine_eval]

theorem one_word (n : Nat) :
    affineWord (aConst n true) = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: affineWord (aConst n true) = false :: (List.replicate n false ++ [true])
    rw [ih]

def prepareOne : Block 16 := .seq (.action (.push 8 true)) (.action (.copy 2 12))
def one : Block 16 := .seq prepareOne <|
  .seq (Frame.block 7 SourceScalarInitialization.zeroLoop) SourceScalarRow.saveLeft
def oneFuel (n : Nat) : Nat := 3 * n + 5

theorem one_exec {n : Nat} (q : Quadratic n) (input savedStream : BitString) :
    Exec one (full (work input) emptySaved (data savedStream q)) (oneFuel n)
      (full {work input with reserved := affineWord (aConst n true)}
        emptySaved (data savedStream q)) := by
  let metadata := data savedStream q
  let loaded := {work input with remaining := List.replicate n true,output := [true]}
  let emitted := {work input with output := affineWord (aConst n true)}
  have prepare : Exec prepareOne (full (work input) emptySaved metadata) 2
      (full loaded emptySaved metadata) := Exec.seq (.action _ _) (.action _ _)
  have emit : Exec SourceScalarInitialization.zeroLoop loaded.store (3 * n + 1) emitted.store := by
    simpa only [loaded,emitted,work,List.length_replicate,one_word] using
      SourceScalarInitialization.zero_exec {work input with output := [true]} (List.replicate n true)
  have save : Exec SourceScalarRow.saveLeft (full emitted emptySaved metadata) 2
      (full {work input with reserved := affineWord (aConst n true)} emptySaved metadata) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : oneFuel n = 2 + ((3 * n + 1) + 2) := by
    unfold oneFuel
    omega
  simpa only [one,cost,metadata] using
    Exec.seq prepare (Exec.seq (core_exec emit emptySaved metadata) save)

def load : Block 16 := .seq one <| .seq SourceScalarRow.factor SourceScalarRow.prepareProduct
def loadFuel (n : Nat) : Nat := 12 * n + 23

theorem load_exec {n : Nat} (u : Affine n) (q : Quadratic n) (suffix savedStream : BitString) :
    Exec load (full (work (affineWord u ++ suffix)) emptySaved (data savedStream q))
      (loadFuel n)
      (full (SourceQuadraticProduct.ready (work []) (aConst n true) u)
        emptySaved (data suffix q)) := by
  let metadata := data savedStream q
  let rightDone := {work suffix with reserved := affineWord (aConst n true),output := affineWord u}
  have first := one_exec q (affineWord u ++ suffix) savedStream
  have factor := SourceScalarRow.factor_exec u q suffix savedStream (affineWord (aConst n true))
  have prepare : Exec SourceScalarRow.prepareProduct (full rightDone emptySaved metadata) 6
      (full (SourceQuadraticProduct.ready (work []) (aConst n true) u)
        emptySaved (data suffix q)) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have cost : loadFuel n = oneFuel n + (SourceScalarRow.factorFuel n + 6) := by
    simp only [loadFuel,oneFuel,SourceScalarRow.factorFuel]
    omega
  simpa only [load,cost,rightDone,metadata] using Exec.seq first (Exec.seq factor prepare)

def block : Block 16 := .seq load <|
  .seq (Frame.block 5 SourceQuadraticProduct.forwardBlock) SourceScalarRow.accumulate
def fuel (n : Nat) : Nat :=
  loadFuel n + (SourceQuadraticProduct.forwardFuel n + SourceScalarRow.addFuel n)

theorem block_exec {n : Nat} (u : Affine n) (q : Quadratic n) (suffix savedStream : BitString) :
    Exec block (full (work (affineWord u ++ suffix)) emptySaved (data savedStream q))
      (fuel n) (state suffix (qAdd q (qOfAffine u))) := by
  have loaded := load_exec u q suffix savedStream
  obtain ⟨after,product⟩ := SourceQuadraticProduct.forward_exec (work []) emptySaved (aConst n true) u
  have add := SourceScalarRow.accumulate_exec (qProduct (aConst n true) u) q after suffix
  simpa only [block,fuel,product_one] using
    Exec.seq loaded (Exec.seq (product_exec product (data suffix q)) add)

theorem fuel_exact (n : Nat) : fuel n = 22 * quadraticBits n + 22 * n + 36 := by
  rw [fuel,loadFuel,SourcePlaneRemainderInstructions.productFuel_exact,SourceScalarRow.addFuel]
  omega

end PNP.Concrete.ResidualReduction.SourceTailPolynomialAffine
