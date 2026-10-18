import PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

/-! Read the dimension and pivot from the actual packet. The remainder of the
packet is preserved exactly; protected words are updated by literal copies,
not installed by a semantic constructor at runtime. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

def fieldSet : Field → Saved → BitString → Saved
  | .dimension,s,word => {s with dimension := word}
  | .pivot,s,word => {s with pivot := word}
  | .normals,s,word => {s with normals := word}
  | .family,s,word => {s with family := word}
  | .quadratic,s,word => {s with quadratic := word}
  | .tail,s,word => {s with tail := word}
def saveHeader (field : Field) : Block 29 := .seq (.action (.copy field.slot 1)) <|
  .seq (.action (.clear 1)) (.action (.clear 4))
def header (field : Field) : Block 29 := .seq (core MatrixStrictHeader.block) (saveHeader field)

theorem header_exec (field : Field) (count : Nat) (suffix : BitString) (s : Saved) :
    Exec (header field) (work (natural count ++ suffix) [] s) (4 * count + 12)
      (work suffix [] (fieldSet field s (List.replicate count true))) := by
  let before := SourceScalarState.work (natural count ++ suffix)
  let counted := {SourceScalarState.work suffix with target := List.replicate count true,sign := [true]}
  have scan : Exec MatrixStrictHeader.block before.store (4 * count + 9) counted.store := by
    simpa only [SourceCoefficientGateRaw.header_fuel,MatrixStrictHeader.result,
      MatrixStrictHeader.scan_canonical,if_true,before,counted,SourceScalarState.work,List.append_nil] using
      MatrixStrictHeader.block_exec (natural count ++ suffix) before
  have save : Exec (saveHeader field) (withCore counted s) 3
      (work suffix [] (fieldSet field s (List.replicate count true))) := by
    cases field <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : 4 * count + 12 = (4 * count + 9) + 3 := by omega
  simpa only [header,cost,work,before,SourceScalarState.work] using Exec.seq (core_exec scan s) save

def dimensions (n pivot : Nat) : Saved :=
  ⟨List.replicate n true,List.replicate pivot true,[],[],[],[]⟩
def headers : Block 29 := .seq (header .dimension) (header .pivot)
def headersFuel (n pivot : Nat) : Nat := 4 * n + 4 * pivot + 24

theorem headers_exec (n pivot : Nat) (suffix : BitString) :
    Exec headers (initial (natural n ++ (natural pivot ++ suffix))) (headersFuel n pivot)
      (work suffix [] (dimensions n pivot)) := by
  have first := header_exec Field.dimension n (natural pivot ++ suffix) emptySaved
  have second := header_exec Field.pivot pivot suffix (fieldSet .dimension emptySaved (List.replicate n true))
  have cost : headersFuel n pivot = (4 * n + 12) + (4 * pivot + 12) := by
    unfold headersFuel
    omega
  simpa only [headers,cost,SourceChartedSuccessorState.initial,fieldSet,emptySaved,dimensions] using Exec.seq first second

def packet {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : BitString :=
  natural n ++ (natural k.val ++ ((normalsCodec n).encode normals ++
    (SourceEncoding.familyCodec (n + 1)).encode F))

theorem packet_length {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (packet F k normals).length = n + 1 + (k.val + 1) +
      ((normalsCodec n).encode normals).length + ((SourceEncoding.familyCodec (n + 1)).encode F).length := by
  simp only [packet,List.length_append,natural_length,Nat.add_assoc]

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorInput
