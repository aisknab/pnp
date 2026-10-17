import PNP.Concrete.ResidualReduction.SourceRowReductionState

/-! Read every bit of a typed source row into protected working registers.
The input suffix is obtained from the consumed stream, not supplied as stored
metadata. Selection, both leading coefficients and both affine tails are read. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionLoad
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceRowReductionState

inductive Flag where
  | selected | left | right
def flagIndex : Flag → Fin 19
  | .selected => 14
  | .left => 15
  | .right => 16
def pushedFlag (d : Data) (slot : Flag) (bit : Bool) : Data :=
  match slot with
  | .selected => {d with selected := bit :: d.selected}
  | .left => {d with leftHead := bit :: d.leftHead}
  | .right => {d with rightHead := bit :: d.rightHead}
def takeFlag (slot : Flag) : Block 19 := .branch 0 .skip
  (.seq (.action (.pop 0)) (.action (.push (flagIndex slot) false)))
  (.seq (.action (.pop 0)) (.action (.push (flagIndex slot) true)))

theorem takeFlag_exec (r : Registers) (s : SourcePlanePartnerBuilder.Saved) (d : Data)
    (slot : Flag) (bit : Bool) :
    Exec (takeFlag slot) (full {r with input := bit :: r.input} s d) 3
      (full r s (pushedFlag d slot bit)) := by
  cases slot <;> cases bit
  all_goals first
    | exact Exec.zero rfl (Exec.seq (.action _ _) (.action _ _))
    | exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))

def factorIndex (right : Bool) : Fin 19 := if right then 13 else 11
def factorSaved (s : SourcePlanePartnerBuilder.Saved) (right : Bool) (word : BitString) :
    SourcePlanePartnerBuilder.Saved := if right then s else {s with query := word}
def factorData (d : Data) (right : Bool) (word : BitString) : Data :=
  if right then {d with right := word} else d
def storeFactor (right : Bool) : Block 19 :=
  .seq (.action (.copy (factorIndex right) 8)) (.action (.clear 8))
def factor (right : Bool) : Block 19 := .seq (.action (.copy 2 1)) <|
  .seq (core copyLoop) <| .seq (core ClauseQuery.reverseLoop) (storeFactor right)
def factorFuel (n : Nat) : Nat := 9 * (n + 1) + 5

theorem factor_exec {n : Nat} (f : Affine n) (suffix : BitString)
    (s : SourcePlanePartnerBuilder.Saved) (d : Data) (right : Bool) :
    Exec (factor right) (full (work n (affineWord f ++ suffix)) s d) (factorFuel n)
      (full (work n suffix) (factorSaved s right (affineWord f)) (factorData d right (affineWord f))) := by
  let before := work n (affineWord f ++ suffix)
  let ready := {before with remaining := List.replicate (n + 1) true}
  let copied := {work n suffix with excess := (affineWord f).reverse}
  let reversed := {work n suffix with output := affineWord f}
  have load : Exec (.action (.copy (2 : Fin 19) 1)) (full before s d) 1 (full ready s d) := .action _ _
  have copy : Exec copyLoop ready.store (5 * (n + 1) + 1) copied.store := by
    simpa only [ready,before,copied,work,affineWord_length,List.append_nil] using
      copy_exec (work n []) (affineWord f) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * (n + 1) + 1) reversed.store := by
    simpa only [copied,reversed,work,List.length_reverse,affineWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work n suffix) (affineWord f).reverse
  have save : Exec (storeFactor right) (full reversed s d) 2
      (full (work n suffix) (factorSaved s right (affineWord f)) (factorData d right (affineWord f))) := by
    cases right <;> exact Exec.seq (.action _ _) (.action _ _)
  have cost : factorFuel n = 1 + ((5 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 2)) := by
    unfold factorFuel
    omega
  simpa only [factor,cost,before] using
    Exec.seq load (Exec.seq (core_exec copy s d) (Exec.seq (core_exec reverse s d) save))

def saveSuffix : Block 19 := .seq (.action (.copy 17 0)) (.action (.clear 0))
def block : Block 19 := .seq (takeFlag .selected) <| .seq (takeFlag .left) <|
  .seq (factor false) <| .seq (takeFlag .right) <| .seq (factor true) saveSuffix
def fuel (n : Nat) : Nat := 18 * (n + 1) + 21

theorem block_exec {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    Exec block (SourceRowReductionState.initial t r suffix) (fuel n) (loaded t r suffix) := by
  rcases r with ⟨selected,⟨leftHead,f⟩,⟨rightHead,g⟩⟩
  let row : Row (n + 1) := ⟨selected,(leftHead,f),(rightHead,g)⟩
  let s := parameters t
  let d0 := emptyData t []
  let d1 := pushedFlag d0 .selected selected
  let d2 := pushedFlag d1 .left leftHead
  let leftInput := affineWord f ++ (rightHead :: (affineWord g ++ suffix))
  let leftReady := work n leftInput
  let afterSelection := work n (leftHead :: leftInput)
  let s1 := factorSaved s false (affineWord f)
  let d3 := pushedFlag d2 .right rightHead
  let d4 := factorData d3 true (affineWord g)
  have selection : Exec (takeFlag .selected) (SourceRowReductionState.initial t row suffix) 3
      (full afterSelection s d1) := by
    simpa only [SourceRowReductionState.initial,row,rowWord,affineWord_cons,List.cons_append,
      List.append_assoc,afterSelection,leftInput,work,s,d0,d1] using
      takeFlag_exec afterSelection s d0 .selected selected
  have leftBit : Exec (takeFlag .left) (full afterSelection s d1) 3 (full leftReady s d2) :=
    takeFlag_exec leftReady s d1 .left leftHead
  have left : Exec (factor false) (full leftReady s d2) (factorFuel n)
      (full (work n (rightHead :: (affineWord g ++ suffix))) s1 d2) :=
    factor_exec f (rightHead :: (affineWord g ++ suffix)) s d2 false
  have rightBit : Exec (takeFlag .right)
      (full (work n (rightHead :: (affineWord g ++ suffix))) s1 d2) 3
      (full (work n (affineWord g ++ suffix)) s1 d3) :=
    takeFlag_exec (work n (affineWord g ++ suffix)) s1 d2 .right rightHead
  have right : Exec (factor true) (full (work n (affineWord g ++ suffix)) s1 d3) (factorFuel n)
      (full (work n suffix) s1 d4) := factor_exec g suffix s1 d3 true
  have finish : Exec saveSuffix (full (work n suffix) s1 d4) 2 (loaded t row suffix) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : fuel n = 3 + (3 + (factorFuel n + (3 + (factorFuel n + 2)))) := by
    unfold fuel factorFuel
    omega
  simpa only [block,cost,row] using
    Exec.seq selection (Exec.seq leftBit (Exec.seq left (Exec.seq rightBit (Exec.seq right finish))))

end PNP.Concrete.ResidualReduction.SourceRowReductionLoad
