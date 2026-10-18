import PNP.Concrete.ResidualReduction.SourceQuadraticDiagonal
import PNP.Concrete.ResidualReduction.SourceScalarRow

/-! Construct the existing plane remainder from encoded q, a and b. Widths
are allocated from the dimension, q is read from its actual coefficient word,
the factor product is computed and added literally, and its affine part is
extracted. No semantic polynomial callback or supplied remainder is used. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState

def packet {n : Nat} (q : Quadratic n) (a b : Affine n) : BitString :=
  SourceQuadraticEncoding.word q ++ (affineWord a ++ affineWord b)
theorem packet_length {n : Nat} (q : Quadratic n) (a b : Affine n) :
    (packet q a b).length = quadraticBits n + 2 * (n + 1) := by
  simp only [packet,List.length_append,SourceQuadraticEncoding.word_length,affineWord_length]
  omega

def storePolynomial : Block 16 := .seq (.action (.copy 15 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 11 0))
def loadPolynomial : Block 16 := .seq (.action (.copy 2 14)) <|
  .seq (Frame.block 7 copyLoop) <| .seq (Frame.block 7 ClauseQuery.reverseLoop) storePolynomial
def loadFuel (n : Nat) : Nat := 9 * quadraticBits n + 6

theorem load_exec {n : Nat} (q acc : Quadratic n) (suffix savedStream : BitString) :
    Exec loadPolynomial
      (full (work (SourceQuadraticEncoding.word q ++ suffix)) emptySaved (data savedStream acc))
      (loadFuel n) (state suffix q) := by
  let metadata := data savedStream acc
  let before := work (SourceQuadraticEncoding.word q ++ suffix)
  let loaded := {before with remaining := List.replicate (quadraticBits n) true}
  let copied := {work suffix with excess := (SourceQuadraticEncoding.word q).reverse}
  let reversed := {work suffix with output := SourceQuadraticEncoding.word q}
  have load : Exec (.action (.copy (2 : Fin 16) 14)) (full before emptySaved metadata) 1 (full loaded emptySaved metadata) := .action _ _
  have copy : Exec copyLoop loaded.store (5 * quadraticBits n + 1) copied.store := by
    simpa only [loaded,before,copied,work,SourceQuadraticEncoding.word_length,List.append_nil] using
      copy_exec (work []) (SourceQuadraticEncoding.word q) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * quadraticBits n + 1) reversed.store := by
    simpa only [copied,reversed,work,SourceQuadraticEncoding.word_length,List.length_reverse,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work suffix) (SourceQuadraticEncoding.word q).reverse
  have save : Exec storePolynomial (full reversed emptySaved metadata) 3 (state suffix q) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : loadFuel n = 1 + ((5 * quadraticBits n + 1) + ((4 * quadraticBits n + 1) + 3)) := by
    unfold loadFuel; omega
  simpa only [loadPolynomial,cost,before,metadata] using Exec.seq load
    (Exec.seq (core_exec copy emptySaved metadata) (Exec.seq (core_exec reverse emptySaved metadata) save))

def prepareExtract : Block 16 := .seq (.action (.copy 0 15)) (.action (.copy 1 12))
def extract : Block 16 := .seq prepareExtract (Frame.block 7 SourceQuadraticDiagonal.forwardBlock)

theorem extract_exec {n : Nat} (q : Quadratic n) :
    Exec extract (state [] q) (2 + SourceQuadraticDiagonal.forwardFuel n)
      (full {work [] with output := affineWord (affinePart q)} emptySaved (data [] q)) := by
  let loaded := {work (SourceQuadraticEncoding.word q) with target := List.replicate n true}
  have prepare : Exec prepareExtract (state [] q) 2 (full loaded emptySaved (data [] q)) :=
    Exec.seq (.action _ _) (.action _ _)
  have scan : Exec SourceQuadraticDiagonal.forwardBlock loaded.store (SourceQuadraticDiagonal.forwardFuel n)
      ({work [] with output := affineWord (affinePart q)}).store := by
    simpa only [loaded,SourceQuadraticDiagonal.ready,work,List.append_nil] using
      SourceQuadraticDiagonal.forward_exec (work []) q []
  exact Exec.seq prepare (core_exec scan emptySaved (data [] q))

def finished {n : Nat} (q : Quadratic n) (a b : Affine n) : Store 16 :=
  full {work [] with output := affineWord (planeRemainder q a b)} emptySaved (data [] (qAdd q (qProduct a b)))
def block : Block 16 := .seq SourceScalarInitialization.block <|
  .seq loadPolynomial <| .seq SourceScalarRow.selected extract
def fuel (n : Nat) : Nat := SourceScalarInitialization.fuel n +
  (loadFuel n + (SourceScalarRow.selectedFuel n + (2 + SourceQuadraticDiagonal.forwardFuel n)))

theorem block_exec {n : Nat} (q : Quadratic n) (a b : Affine n) :
    Exec block (initial n (packet q a b)) (fuel n) (finished q a b) := by
  have start := SourceScalarInitialization.block_exec n (packet q a b)
  have load := load_exec q (zero n) (affineWord a ++ affineWord b) (packet q a b)
  have product : Exec SourceScalarRow.selected (state (affineWord a ++ affineWord b) q)
      (SourceScalarRow.selectedFuel n) (state [] (qAdd q (qProduct a b))) := by
    simpa only [state,List.append_nil] using
      SourceScalarRow.selected_exec a b q [] (affineWord a ++ affineWord b)
  have tail := extract_exec (qAdd q (qProduct a b))
  exact Exec.seq start (Exec.seq load (Exec.seq product tail))

theorem productLoopFuel_exact (n : Nat) :
    SourceQuadraticProduct.loopFuel n + 6 = 7 * quadraticBits n + 10 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [SourceQuadraticProduct.loopFuel,quadraticBits,affineBits,Nat.mul_add,Nat.mul_one]
    omega
theorem productFuel_exact (n : Nat) :
    SourceQuadraticProduct.forwardFuel n = 11 * quadraticBits n + 10 * n + 2 := by
  have count := productLoopFuel_exact n
  unfold SourceQuadraticProduct.forwardFuel SourceQuadraticProduct.fuel
  omega
theorem fuel_exact (n : Nat) : fuel n = 40 * quadraticBits n + 40 * n + 70 := by
  rw [fuel,SourceScalarInitialization.fuel_exact,loadFuel,
    SourceScalarRow.selectedFuel,SourceScalarRow.loadFuel,SourceScalarRow.addFuel,
    productFuel_exact,SourceQuadraticDiagonal.forwardFuel_exact]
  omega
theorem fuel_source_bound {n : Nat} (q : Quadratic n) (a b : Affine n) :
    fuel n ≤ 40 * (packet q a b).length := by
  rw [fuel_exact,packet_length]
  omega

theorem output_get {n : Nat} (q : Quadratic n) (a b : Affine n) :
    (finished q a b).get 8 = affineWord (planeRemainder q a b) := rfl
theorem output_decode {n : Nat} (q : Quadratic n) (a b : Affine n) :
    (SourceEncoding.affineCodec n).decode ((finished q a b).get 8) = some (planeRemainder q a b) :=
  decode_encode (SourceEncoding.affineCodec n) (planeRemainder q a b)
theorem output_length {n : Nat} (q : Quadratic n) (a b : Affine n) :
    ((finished q a b).get 8).length = n + 1 := affineWord_length _
theorem output_source_bound {n : Nat} (q : Quadratic n) (a b : Affine n) :
    ((finished q a b).get 8).length ≤ (packet q a b).length := by
  rw [output_length,packet_length]
  omega

end PNP.Concrete.ResidualReduction.SourcePlaneRemainderInstructions
