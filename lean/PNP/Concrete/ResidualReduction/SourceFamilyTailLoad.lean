import PNP.Concrete.ResidualReduction.SourceFamilyReductionInstructions

/-! Load the computed tail's own canonical bytes into protected registers.
The kind tag, original normal pair and remainder are read from the stream;
no tail parameter or family result is inserted by a semantic callback. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyTailLoad
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceRowReductionState (work parameters emptyData)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState

def noParameters : SourcePlanePartnerBuilder.Saved := ⟨[],[],[]⟩
def noData : SourceRowReductionState.Data := ⟨[],[],[],[],[],[],[]⟩
def blank (n : Nat) (input : BitString) : Store 19 :=
  SourceRowReductionState.full (work n input) noParameters noData
inductive Field where
  | left | right | remainder
def fieldIndex : Field → Fin 23
  | .left => 9
  | .right => 10
  | .remainder => 12
def fieldParameters (p : SourcePlanePartnerBuilder.Saved) (field : Field) (word : BitString) :
    SourcePlanePartnerBuilder.Saved :=
  match field with
  | .left => {p with left := word}
  | .right => {p with right := word}
  | .remainder => p
def fieldData (d : SourceRowReductionState.Data) (field : Field) (word : BitString) :
    SourceRowReductionState.Data :=
  match field with
  | .left | .right => d
  | .remainder => {d with remainder := word}
def saveField (field : Field) : Block 23 :=
  .seq (.action (.copy (fieldIndex field) 8)) (.action (.clear 8))
def readField (field : Field) : Block 23 := .seq (.action (.copy 2 1)) <|
  .seq (core copyLoop) <| .seq (core ClauseQuery.reverseLoop) (saveField field)
def fieldFuel (n : Nat) : Nat := 9 * (n + 1) + 5

theorem readField_exec {n : Nat} (f : Affine n) (suffix : BitString)
    (p : SourcePlanePartnerBuilder.Saved) (d : SourceRowReductionState.Data) (s : Saved) (field : Field) :
    Exec (readField field) (full (SourceRowReductionState.full (work n (affineWord f ++ suffix)) p d) s)
      (fieldFuel n)
      (full (SourceRowReductionState.full (work n suffix)
        (fieldParameters p field (affineWord f)) (fieldData d field (affineWord f))) s) := by
  let before := work n (affineWord f ++ suffix)
  let ready := {before with remaining := List.replicate (n + 1) true}
  let copied := {work n suffix with excess := (affineWord f).reverse}
  let reversed := {work n suffix with output := affineWord f}
  have load : Exec (.action (.copy (2 : Fin 23) 1))
      (full (SourceRowReductionState.full before p d) s) 1
      (full (SourceRowReductionState.full ready p d) s) := .action _ _
  have copy : Exec copyLoop ready.store (5 * (n + 1) + 1) copied.store := by
    simpa only [ready,before,copied,work,affineWord_length,List.append_nil] using
      copy_exec (work n []) (affineWord f) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * (n + 1) + 1) reversed.store := by
    simpa only [copied,reversed,work,List.length_reverse,affineWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work n suffix) (affineWord f).reverse
  have save : Exec (saveField field) (full (SourceRowReductionState.full reversed p d) s) 2
      (full (SourceRowReductionState.full (work n suffix)
        (fieldParameters p field (affineWord f)) (fieldData d field (affineWord f))) s) := by
    cases field <;> exact Exec.seq (.action _ _) (.action _ _)
  have cost : fieldFuel n = 1 + ((5 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 2)) := by
    unfold fieldFuel
    omega
  simpa only [readField,cost,before] using
    Exec.seq load (Exec.seq (core_exec copy p d s) (Exec.seq (core_exec reverse p d s) save))

def takeKind : Block 23 := .branch 0 .skip
  (.seq (.action (.pop 0)) (.action (.push 18 false)))
  (.seq (.action (.pop 0)) (.action (.push 18 true)))
theorem takeKind_exec (r : Registers) (p : SourcePlanePartnerBuilder.Saved)
    (d : SourceRowReductionState.Data) (s : Saved) (bit : Bool) :
    Exec takeKind (full (SourceRowReductionState.full {r with input := bit :: r.input} p d) s) 3
      (full (SourceRowReductionState.full r p {d with kind := bit :: d.kind}) s) := by
  cases bit
  · exact Exec.zero rfl (Exec.seq (.action _ _) (.action _ _))
  · exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))

def fields : Block 23 := .branch 18 .skip (readField .remainder)
  (.seq (readField .left) (.seq (readField .right) (readField .remainder)))
def block : Block 23 := .seq takeKind fields
def fieldsFuel {n : Nat} : TailForm n → Nat
  | .affine _ => fieldFuel n
  | .plane _ _ _ => fieldFuel n + (fieldFuel n + fieldFuel n)
def fuel {n : Nat} (t : TailForm n) : Nat := 3 + (1 + fieldsFuel t)

theorem block_exec {n : Nat} (t : TailForm n) (suffix : BitString) (s : Saved) :
    Exec block (full (blank n ((SourceComputedTailEncoding.codec n).encode t ++ suffix)) s) (fuel t)
      (full (base t suffix) s) := by
  cases t with
  | affine u =>
    let d : SourceRowReductionState.Data := {noData with kind := [false]}
    have tag := takeKind_exec (work n (affineWord u ++ suffix)) noParameters noData s false
    have body : Exec fields
        (full (SourceRowReductionState.full (work n (affineWord u ++ suffix)) noParameters d) s)
        (1 + fieldFuel n) (full (base (.affine u) suffix) s) :=
      Exec.zero rfl (readField_exec u suffix noParameters d s .remainder)
    simpa only [block,fuel,fieldsFuel,blank,work,SourceComputedTailEncoding.affine_bytes,List.cons_append,d] using
      Exec.seq tag body
  | plane a b u =>
    let d : SourceRowReductionState.Data := {noData with kind := [true]}
    let p1 := fieldParameters noParameters .left (affineWord a)
    let p2 := fieldParameters p1 .right (affineWord b)
    have tag := takeKind_exec (work n (affineWord a ++ (affineWord b ++ (affineWord u ++ suffix))))
      noParameters noData s true
    have first := readField_exec a (affineWord b ++ (affineWord u ++ suffix)) noParameters d s .left
    have second := readField_exec b (affineWord u ++ suffix) p1 d s .right
    have third := readField_exec u suffix p2 d s .remainder
    have body : Exec fields
        (full (SourceRowReductionState.full
          (work n (affineWord a ++ (affineWord b ++ (affineWord u ++ suffix)))) noParameters d) s)
        (1 + (fieldFuel n + (fieldFuel n + fieldFuel n))) (full (base (.plane a b u) suffix) s) :=
      Exec.one rfl (Exec.seq first (Exec.seq second third))
    simpa only [block,fuel,fieldsFuel,blank,work,SourceComputedTailEncoding.plane_bytes,List.cons_append,
      List.append_assoc,d] using Exec.seq tag body

theorem fuel_bound {n : Nat} (t : TailForm n) : fuel t ≤ 27 * (n + 1) + 19 := by
  cases t <;> simp only [fuel,fieldsFuel,fieldFuel] <;> omega

end PNP.Concrete.ResidualReduction.SourceFamilyTailLoad
