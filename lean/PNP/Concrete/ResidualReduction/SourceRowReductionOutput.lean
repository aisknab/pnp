import PNP.Concrete.ResidualReduction.SourceRowReductionLoad

/-! Serialize constructed row coefficients in the canonical optional-row
format. Both words and the actual selection flag are copied by counted
instructions, then scratch is cleared and the saved source suffix restored. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceRowReductionState

def buffered {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected leftHead rightHead : Bool) (suffix : BitString) (kind : Bool) (out : BitString) : Store 19 :=
  full {work n [] with output := out} ⟨A,B,affineWord f⟩ (rowData u g selected leftHead rightHead suffix kind)
def terminal {n : Nat} (A B : BitString) (u : Affine n) (suffix : BitString)
    (kind : Bool) (out : BitString) : Store 19 :=
  full {work n suffix with output := out} ⟨A,B,[]⟩ ⟨affineWord u,[],[],[],[],suffix,[kind]⟩

def prepareLeft : Block 19 := .seq (.action (.copy 0 11)) (.action (.copy 2 1))
def prepareRight : Block 19 := .seq (.action (.copy 0 13)) (.action (.copy 2 1))
def serialize : Block 19 := .seq (.action (.copy 3 14)) <| .seq prepareLeft <|
  .seq (core copyLoop) <| .seq prepareRight <| .seq (core copyLoop) <|
  .seq (core ClauseQuery.reverseLoop) (.action (.push 8 true))
def fuel (n : Nat) : Nat := 18 * (n + 1) + 13

theorem serialize_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected leftHead rightHead : Bool) (suffix : BitString) (kind : Bool) :
    Exec serialize (prepared A B u f g selected leftHead rightHead suffix kind) (fuel n)
      (buffered A B u f g selected leftHead rightHead suffix kind
        ((codec n).encode (some ⟨selected,f,g⟩))) := by
  let s : SourcePlanePartnerBuilder.Saved := ⟨A,B,affineWord f⟩
  let d := rowData u g selected leftHead rightHead suffix kind
  let base := work n []
  let flagged := {base with excess := [selected]}
  let leftReady := {flagged with input := affineWord f,remaining := List.replicate (n + 1) true}
  let leftDone := {base with excess := (affineWord f).reverse ++ [selected]}
  let rightReady := {leftDone with input := affineWord g,remaining := List.replicate (n + 1) true}
  let rightDone := {base with excess := (rowWord (⟨selected,f,g⟩ : Row n)).reverse}
  let encoded := {base with output := rowWord (⟨selected,f,g⟩ : Row n)}
  have flag : Exec (.action (.copy (3 : Fin 19) 14)) (full base s d) 1 (full flagged s d) := .action _ _
  have loadLeft : Exec prepareLeft (full flagged s d) 2 (full leftReady s d) :=
    Exec.seq (.action _ _) (.action _ _)
  have left : Exec copyLoop leftReady.store (5 * (n + 1) + 1) leftDone.store := by
    simpa only [leftReady,leftDone,flagged,base,work,affineWord_length,List.append_nil] using
      copy_exec flagged (affineWord f) []
  have loadRight : Exec prepareRight (full leftDone s d) 2 (full rightReady s d) :=
    Exec.seq (.action _ _) (.action _ _)
  have right : Exec copyLoop rightReady.store (5 * (n + 1) + 1) rightDone.store := by
    simpa only [rightReady,rightDone,leftDone,base,work,affineWord_length,List.append_nil,
      rowWord,List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append] using
      copy_exec leftDone (affineWord g) []
  have reverse : Exec ClauseQuery.reverseLoop rightDone.store (4 * (2 * n + 3) + 1) encoded.store := by
    simpa only [rightDone,encoded,base,work,List.length_reverse,rowWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec base (rowWord (⟨selected,f,g⟩ : Row n)).reverse
  have tag : Exec (.action (.push (8 : Fin 19) true)) (full encoded s d) 1
      (buffered A B u f g selected leftHead rightHead suffix kind
        ((codec n).encode (some ⟨selected,f,g⟩))) := .action _ _
  have cost : fuel n = 1 + (2 + ((5 * (n + 1) + 1) +
      (2 + ((5 * (n + 1) + 1) + ((4 * (2 * n + 3) + 1) + 1))))) := by
    unfold fuel
    omega
  simpa only [serialize,cost,prepared,s,d,base] using Exec.seq flag (Exec.seq loadLeft
    (Exec.seq (core_exec left s d) (Exec.seq loadRight
      (Exec.seq (core_exec right s d) (Exec.seq (core_exec reverse s d) tag)))))

theorem cleanup_buffered {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected leftHead rightHead : Bool) (suffix : BitString) (kind : Bool) (out : BitString) :
    Exec cleanup (buffered A B u f g selected leftHead rightHead suffix kind out) 12
      (terminal A B u suffix kind out) :=
  cleanup_exec {work n [] with output := out} ⟨A,B,affineWord f⟩
    (rowData u g selected leftHead rightHead suffix kind)

def finish : Block 19 := .seq serialize cleanup
def finishFuel (n : Nat) : Nat := fuel n + 12

theorem finish_exec {n : Nat} (A B : BitString) (u f g : Affine n)
    (selected leftHead rightHead : Bool) (suffix : BitString) (kind : Bool) :
    Exec finish (prepared A B u f g selected leftHead rightHead suffix kind) (finishFuel n)
      (terminal A B u suffix kind ((codec n).encode (some ⟨selected,f,g⟩))) :=
  Exec.seq (serialize_exec A B u f g selected leftHead rightHead suffix kind)
    (cleanup_buffered A B u f g selected leftHead rightHead suffix kind _)

end PNP.Concrete.ResidualReduction.SourceRowReductionOutput
