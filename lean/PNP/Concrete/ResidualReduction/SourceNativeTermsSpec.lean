import PNP.Concrete.ResidualReduction.SourceNativeLabel

/-! Specification of complete sparse coefficient-list conversion, with failure
and the actual unread suffix explicit. The machine below will derive these
objects from bytes; this specification is not a supplied correctness premise. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsSpec
open PNP.Concrete PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction

def selected (input : BitString) (n : Nat) : Option (Fin n) :=
  let p := SourceNativeRowIndex.parse input
  if p.valid then if h : p.index < n then some ⟨p.index,h⟩ else none else none
def remaining (input : BitString) : BitString := (SourceNativeRowIndex.parse input).rest
def readCore (input : BitString) (n : Nat) : Registers :=
  let p := SourceNativeRowIndex.parse input
  if p.valid then SourceNativeCoordinate.result p.rest n p.index
  else SourceNativeRowIndex.state p.rest p.index false

theorem label_result (input : BitString) (n : Nat) :
    SourceNativeLabel.result input n =
      SourceNativeLabel.full (readCore input n) (List.replicate n true) := by
  cases flag : (SourceNativeRowIndex.parse input).valid <;>
    simp only [SourceNativeLabel.result,readCore,flag,Bool.false_eq_true,↓reduceIte]
theorem readCore_input (input : BitString) (n : Nat) :
    (readCore input n).input = remaining input := by
  cases flag : (SourceNativeRowIndex.parse input).valid with
  | false =>
    simp only [readCore,flag,Bool.false_eq_true,↓reduceIte]
    rfl
  | true =>
    simp only [readCore,flag,↓reduceIte]
    unfold SourceNativeCoordinate.result
    split <;> rfl

theorem readCore_some (input : BitString) (n : Nat) (j : Fin n)
    (chosen : selected input n = some j) :
    readCore input n =
      {SourceNativeRowIndex.state (remaining input) 0 true with output :=
        (SourceNativeEncoding.affineWord (NativeSource.coordinateForm n j)).reverse} := by
  cases flag : (SourceNativeRowIndex.parse input).valid with
  | false =>
    simp only [selected,flag,Bool.false_eq_true,↓reduceIte] at chosen
    cases chosen
  | true =>
    by_cases bound : (SourceNativeRowIndex.parse input).index < n
    · simp only [selected,flag,↓reduceIte,bound,dif_pos,Option.some.injEq] at chosen
      subst j
      simp only [readCore,flag,↓reduceIte,SourceNativeCoordinate.result,bound,
        SourceNativeCoordinate.passed,remaining,SourceNativeEncoding.coordinate_word,
        SourceUnitDirectionInstructions.unit_bytes]
    · simp only [selected,flag,↓reduceIte,bound] at chosen
      cases chosen

theorem readCore_none (input : BitString) (n : Nat)
    (absent : selected input n = none) : (readCore input n).sign = [] := by
  cases flag : (SourceNativeRowIndex.parse input).valid with
  | false => simp only [readCore,flag,Bool.false_eq_true,↓reduceIte]; rfl
  | true =>
    by_cases bound : (SourceNativeRowIndex.parse input).index < n
    · simp only [selected,flag,↓reduceIte,bound,dif_pos] at absent
      cases absent
    · simp only [readCore,flag,↓reduceIte,SourceNativeCoordinate.result,bound]
      rfl

theorem remaining_bound (input : BitString) : (remaining input).length ≤ input.length :=
  (SourceNativeRowIndex.parse_bounds input).1

theorem selected_canonical {c : Nat} (row : NativeEquations.Row c) (suffix : BitString) :
    selected ((NativeSystemCodec.rowCodec c).encode row ++ suffix) (2 * c) =
      some (NativeSource.rowIndex row) := by
  simp only [selected,SourceNativeRowIndex.canonical,↓reduceIte,(NativeSource.rowIndex row).isLt,dif_pos]
theorem remaining_canonical {c : Nat} (row : NativeEquations.Row c) (suffix : BitString) :
    remaining ((NativeSystemCodec.rowCodec c).encode row ++ suffix) = suffix := by
  simp only [remaining,SourceNativeRowIndex.canonical]

structure Result (n : Nat) where
  input : BitString
  accumulator : Affine n
  valid : Bool

def scan {n : Nat} : Nat → BitString → Affine n → Result n
  | 0,input,a => ⟨input,a,true⟩
  | count + 1,input,a =>
    match selected input n with
    | none => ⟨remaining input,a,false⟩
    | some j => scan count (remaining input) (aAdd (NativeSource.coordinateForm n j) a)

theorem scan_input_bound {n : Nat} (count : Nat) (input : BitString) (a : Affine n) :
    (scan count input a).input.length ≤ input.length := by
  induction count generalizing input a with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    cases chosen : selected input n with
    | none => simpa only [scan,chosen] using remaining_bound input
    | some j =>
      simpa only [scan,chosen] using
        Nat.le_trans (ih (remaining input) (aAdd (NativeSource.coordinateForm n j) a))
          (remaining_bound input)

theorem scan_canonical {c : Nat} (xs : NativeCoefficients.Coefficients c)
    (suffix : BitString) (a : Affine (2 * c)) :
    scan xs.length (encodeSeq (NativeSystemCodec.rowCodec c).encode xs ++ suffix) a =
      ⟨suffix,SourceNativeEncoding.accumulate xs a,true⟩ := by
  induction xs generalizing a with
  | nil => rfl
  | cons row xs ih =>
    simp only [List.length_cons,encodeSeq,List.append_assoc,scan,selected_canonical,
      remaining_canonical,SourceNativeEncoding.accumulate]
    exact ih _

end PNP.Concrete.ResidualReduction.SourceNativeTermsSpec
