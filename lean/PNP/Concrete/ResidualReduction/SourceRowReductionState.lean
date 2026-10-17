import PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions
import PNP.Concrete.ResidualReduction.SourceMatrixEncoding
import PNP.Concrete.ResidualReduction.SourceComputedTailEncoding

/-! Framed state and exact output format for row reduction. The original
tail parameters and source suffix remain separate from the partner lookup's
scratch, while every row coefficient is read by the row-loading phase. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

structure Data where
  remainder : BitString
  right : BitString
  selected : BitString
  leftHead : BitString
  rightHead : BitString
  stream : BitString
  kind : BitString

def Data.store (d : Data) : Store 7 :=
  .cons d.remainder <| .cons d.right <| .cons d.selected <| .cons d.leftHead <|
    .cons d.rightHead <| .cons d.stream (.cons d.kind .nil)
def full (r : Registers) (s : SourcePlanePartnerBuilder.Saved) (d : Data) : Store 19 :=
  Frame.join (SourcePlanePartnerBuilder.full r s) d.store
def core (b : Block 9) : Block 19 := Frame.block 7 (SourcePlanePartnerBuilder.core b)
def partner (b : Block 12) : Block 19 := Frame.block 7 b

theorem core_exec {b : Block 9} {before after : Registers} {ticks : Nat}
    (h : Exec b before.store ticks after.store) (s : SourcePlanePartnerBuilder.Saved) (d : Data) :
    Exec (core b) (full before s d) ticks (full after s d) :=
  Frame.execution (SourcePlanePartnerBuilder.core_exec h s) d.store
theorem partner_exec {b : Block 12} {before after : Store 12} {ticks : Nat}
    (h : Exec b before ticks after) (d : Data) :
    Exec (partner b) (Frame.join before d.store) ticks (Frame.join after d.store) :=
  Frame.execution h d.store

def work (n : Nat) (input : BitString) : Registers :=
  ⟨input,List.replicate (n + 1) true,[],[],[],[],[],[],[]⟩
def rowData {n : Nat} (u g : Affine n) (selected leftHead rightHead : Bool)
    (suffix : BitString) (kind : Bool) : Data :=
  ⟨affineWord u,affineWord g,[selected],[leftHead],[rightHead],suffix,[kind]⟩
def prepared {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected leftHead rightHead : Bool) (suffix : BitString) (kind : Bool) : Store 19 :=
  full (work n []) ⟨A,B,affineWord f⟩ (rowData u g selected leftHead rightHead suffix kind)

def parameters {n : Nat} : TailForm n → SourcePlanePartnerBuilder.Saved
  | .affine _ => ⟨[],[],[]⟩
  | .plane a b _ => ⟨affineWord a,affineWord b,[]⟩
def remainder {n : Nat} : TailForm n → Affine n
  | .affine u => u
  | .plane _ _ u => u
def kind {n : Nat} : TailForm n → Bool
  | .affine _ => false
  | .plane _ _ _ => true
def emptyData {n : Nat} (t : TailForm n) (stream : BitString) : Data :=
  ⟨affineWord (remainder t),[],[],[],[],stream,[kind t]⟩
def initial {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) : Store 19 :=
  full (work n (rowWord r ++ suffix)) (parameters t) (emptyData t [])
def loaded {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) : Store 19 :=
  prepared (parameters t).left (parameters t).right (remainder t) r.left.2 r.right.2
    r.selected r.left.1 r.right.1 suffix (kind t)

def reduceRow {n : Nat} : TailForm n → Row (n + 1) → Option (Row n)
  | .affine u,r => some (affineRow u r)
  | .plane a b u,r => planeRow a b u r
def codec (n : Nat) : Codec (Option (Row n)) :=
  MatrixSolutionEncoding.optionCodec (SourceEncoding.rowCodec n)
theorem none_bytes (n : Nat) : (codec n).encode none = [false] := rfl
theorem some_bytes {n : Nat} (r : Row n) : (codec n).encode (some r) = true :: rowWord r := rfl
theorem roundtrip {n : Nat} (r : Option (Row n)) :
    (codec n).decode ((codec n).encode r) = some r := decode_encode _ _
theorem bytes_bound {n : Nat} (r : Option (Row n)) :
    ((codec n).encode r).length ≤ 2 * n + 4 := by
  cases r with
  | none => rw [none_bytes]; simp only [List.length_cons,List.length_nil]; omega
  | some r => rw [some_bytes,List.length_cons,rowWord_length]; omega

def clearedCore (r : Registers) (d : Data) : Registers :=
  {r with input := d.stream,remaining := [],excess := [],sign := [],mode := [],active := [],reserved := []}
def clearedSaved (s : SourcePlanePartnerBuilder.Saved) : SourcePlanePartnerBuilder.Saved :=
  {s with query := []}
def clearedData (d : Data) : Data :=
  {d with right := [],selected := [],leftHead := [],rightHead := []}
def restoreCore (r : Registers) (d : Data) : Registers :=
  {r with input := d.stream,remaining := [],excess := [],sign := []}
def scratchCore (r : Registers) : Registers := {r with mode := [],active := [],reserved := []}
def restore : Block 19 := .seq (.action (.copy 0 17)) <|
  .seq (.action (.clear 2)) <| .seq (.action (.clear 3)) (.action (.clear 4))
def clearScratch : Block 19 := .seq (.action (.clear 5)) <|
  .seq (.action (.clear 6)) (.action (.clear 7))
def clearMetadata : Block 19 := .seq (.action (.clear 11)) <|
  .seq (.action (.clear 13)) <| .seq (.action (.clear 14)) <|
  .seq (.action (.clear 15)) (.action (.clear 16))
def cleanup : Block 19 := .seq restore (.seq clearScratch clearMetadata)

private theorem restore_exec (r : Registers) (s : SourcePlanePartnerBuilder.Saved) (d : Data) :
    Exec restore (full r s d) 4 (full (restoreCore r d) s d) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
private theorem clearScratch_exec (r : Registers) (s : SourcePlanePartnerBuilder.Saved) (d : Data) :
    Exec clearScratch (full r s d) 3 (full (scratchCore r) s d) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
private theorem clearMetadata_exec (r : Registers) (s : SourcePlanePartnerBuilder.Saved) (d : Data) :
    Exec clearMetadata (full r s d) 5 (full r (clearedSaved s) (clearedData d)) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (.action _ _))))

theorem cleanup_exec (r : Registers) (s : SourcePlanePartnerBuilder.Saved) (d : Data) :
    Exec cleanup (full r s d) 12 (full (clearedCore r d) (clearedSaved s) (clearedData d)) :=
  Exec.seq (restore_exec r s d)
    (Exec.seq (clearScratch_exec (restoreCore r d) s d)
      (clearMetadata_exec (scratchCore (restoreCore r d)) s d))

def finished {n : Nat} (t : TailForm n) (suffix : BitString) (result : Option (Row n)) : Store 19 :=
  full {work n suffix with output := (codec n).encode result} (parameters t) (emptyData t suffix)
theorem output_get {n : Nat} (t : TailForm n) (suffix : BitString) (result : Option (Row n)) :
    (finished t suffix result).get 8 = (codec n).encode result := rfl
theorem suffix_get {n : Nat} (t : TailForm n) (suffix : BitString) (result : Option (Row n)) :
    (finished t suffix result).get 0 = suffix := rfl
theorem output_decode {n : Nat} (t : TailForm n) (suffix : BitString) (result : Option (Row n)) :
    (codec n).decode ((finished t suffix result).get 8) = some result := roundtrip _

end PNP.Concrete.ResidualReduction.SourceRowReductionState
