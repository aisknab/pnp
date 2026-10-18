import PNP.Concrete.ResidualReduction.SourceMenuInsertOutput
import PNP.Concrete.ResidualReduction.SourceDirectionEncoding

/-! Literal canonical query packet assembly from retained source words and the
current normal record(s). All four copies and the final reversal are counted;
the packet is not supplied as an unexplained string by the dispatcher. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectionPacket
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMenuInsertOutput

def ready (dimension count normals family : BitString) : Registers :=
  ⟨family,dimension,[],[],normals,count,[],[],[]⟩
def bytes (dimension count normals family : BitString) : BitString :=
  dimension ++ (count ++ (normals ++ family))
def copied (r : Registers) : Registers :=
  appended (appended (appended (appended r r.target) r.mode) r.sign) r.input
def result (dimension count normals family : BitString) : Registers :=
  finished (copied (ready dimension count normals family))
def block : Block 9 := .seq (append 1) <| .seq (append 5) <|
  .seq (append 4) <| .seq (append 0) finish
def fuel (dimension count normals family : BitString) : Nat :=
  8 * (bytes dimension count normals family).length + 24

theorem block_exec (dimension count normals family : BitString) :
    Exec block (ready dimension count normals family).store (fuel dimension count normals family)
      (result dimension count normals family).store := by
  let r := ready dimension count normals family
  let r1 := appended r dimension
  let r2 := appended r1 count
  let r3 := appended r2 normals
  let r4 := appended r3 family
  have first : Exec (append 1) r.store (4 * dimension.length + 5) r1.store := append_exec r 1
  have second : Exec (append 5) r1.store (4 * count.length + 5) r2.store := append_exec r1 5
  have third : Exec (append 4) r2.store (4 * normals.length + 5) r3.store := append_exec r2 4
  have fourth : Exec (append 0) r3.store (4 * family.length + 5) r4.store := append_exec r3 0
  have last := finish_exec r4
  have cost : fuel dimension count normals family =
      (4 * dimension.length + 5) + ((4 * count.length + 5) +
        ((4 * normals.length + 5) + ((4 * family.length + 5) + finalCost r4))) := by
    simp only [fuel,bytes,r4,r3,r2,r1,r,ready,finalCost,appended,
      List.length_append,List.length_reverse,List.length_nil]
    omega
  simpa only [block,cost,result,copied,r4,r3,r2,r1,r,ready] using
    Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth last)))

theorem result_output (dimension count normals family : BitString) :
    (result dimension count normals family).output = bytes dimension count normals family := by
  simp only [result,finished,copied,ready,appended,bytes,List.reverse_append,
    List.reverse_reverse,List.reverse_nil,List.nil_append,List.append_assoc]

def initial {n : Nat} (F : Family n) (U : System n) : Registers :=
  ready (natural n) (natural U.length) (matrixBits U) ((SourceEncoding.familyCodec n).encode F)
def terminal {n : Nat} (F : Family n) (U : System n) : Registers :=
  result (natural n) (natural U.length) (matrixBits U) ((SourceEncoding.familyCodec n).encode F)

theorem canonical_bytes {n : Nat} (F : Family n) (U : System n) :
    bytes (natural n) (natural U.length) (matrixBits U) ((SourceEncoding.familyCodec n).encode F) =
      SourceDirectionEncoding.codec.encode ⟨n,U,F⟩ := by
  rw [SourceDirectionEncoding.codec_bits]
  change natural n ++ (natural U.length ++ (matrixBits U ++
      (natural F.length ++ encodeSeq (SourceEncoding.rowCodec n).encode F))) = _
  rw [SourceMatrixEncoding.familyBits_encode]

theorem canonical_exec {n : Nat} (F : Family n) (U : System n) :
    Exec block (initial F U).store (8 * (SourceDirectionEncoding.codec.encode ⟨n,U,F⟩).length + 24)
      (terminal F U).store := by
  have checked := block_exec (natural n) (natural U.length) (matrixBits U)
    ((SourceEncoding.familyCodec n).encode F)
  simpa only [initial,terminal,fuel,canonical_bytes] using checked

theorem terminal_output {n : Nat} (F : Family n) (U : System n) :
    (terminal F U).output = SourceDirectionEncoding.codec.encode ⟨n,U,F⟩ := by
  rw [terminal,result_output,canonical_bytes]

theorem line_packet_length {n : Nat} (F : Family n) (a : Affine n) :
    (SourceDirectionEncoding.codec.encode ⟨n,[a],F⟩).length =
      (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + n + 3 := by
  rw [SourceDirectionEncoding.codec_length,SourceMatrixEncoding.codec_length]
  simp only [List.length_cons,List.length_nil,Nat.zero_add,Nat.mul_one]
  omega

theorem plane_packet_length {n : Nat} (F : Family n) (a b : Affine n) :
    (SourceDirectionEncoding.codec.encode ⟨n,[a,b],F⟩).length =
      (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 2 * n + 5 := by
  rw [SourceDirectionEncoding.codec_length,SourceMatrixEncoding.codec_length]
  simp only [List.length_cons,List.length_nil,Nat.zero_add]
  omega

theorem line_instruction_bound {n : Nat} (F : Family n) (a : Affine n) :
    8 * (SourceDirectionEncoding.codec.encode ⟨n,[a],F⟩).length + 24 ≤
      16 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 48 := by
  rw [line_packet_length]
  have dimension := SourceMatrixEncoding.dimension_bound n F
  omega

theorem plane_instruction_bound {n : Nat} (F : Family n) (a b : Affine n) :
    8 * (SourceDirectionEncoding.codec.encode ⟨n,[a,b],F⟩).length + 24 ≤
      24 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 64 := by
  rw [plane_packet_length]
  have dimension := SourceMatrixEncoding.dimension_bound n F
  omega

end PNP.Concrete.ResidualReduction.SourceSelectionPacket
