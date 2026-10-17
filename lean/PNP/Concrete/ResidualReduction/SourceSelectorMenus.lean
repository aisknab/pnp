import PNP.Concrete.ResidualReduction.SourceSelectorState

/-! On-demand, source-derived selector menus. The line menu is constructed once
and saved outside the query prefix. The plane fallback consumes that same saved
menu, constructs every eligible pair and derives its doubled record width by
literal instructions. No second menu or supplied correctness certificate is
introduced. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectorMenus
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceSelectorState
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held)
open PNP.Concrete.ResidualReduction.SourceCandidateSearch (current)
open PNP.Concrete.ResidualReduction.SourceCandidateQueries (base)

def compareZero : SourceMenuCompare.Saved := ⟨[],[],[]⟩
def sortZero : SourceMenuSortStep.Held := ⟨[],[]⟩
def pairZero : SourcePlaneMenu.Held := ⟨[],[]⟩
def retained {n : Nat} (F : Family n) : Saved :=
  ⟨matrixBits (sourceMenu F),List.replicate (n + 1) true⟩

def lineLoad : Block 48 := .seq (.action (.copy 0 41)) <|
  .seq (.action (.copy 1 47)) (.action (.pop 1))
theorem lineLoad_exec {n : Nat} (F : Family n) (count : Nat)
    (normal packet output oldMenu : BitString) (t : Held) :
    Exec lineLoad (full (Store.empty 38) (current (base F count) normal packet output)
      t ⟨oldMenu,List.replicate (n + 1) true⟩) 3
      (full (menuCore (SourceMenuFromFamily.initial F compareZero sortZero))
        (current (base F count) normal packet output) t ⟨oldMenu,List.replicate (n + 1) true⟩) := by
  simp only [List.replicate_succ]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def linePrepare : Block 48 := .seq reset lineLoad
theorem linePrepare_exec {n : Nat} (F : Family n) (count : Nat) (r : Store 38)
    (normal packet output oldMenu : BitString) (t : Held) :
    Exec linePrepare (full r (current (base F count) normal packet output)
      t ⟨oldMenu,List.replicate (n + 1) true⟩) 42
      (full (menuCore (SourceMenuFromFamily.initial F compareZero sortZero))
        (current (base F count) normal packet output) t ⟨oldMenu,List.replicate (n + 1) true⟩) :=
  Exec.seq (reset_exec _ _ _ _) (lineLoad_exec F count normal packet output oldMenu t)

def lineCapture : Block 48 := .seq (copyPending 7) <| .seq (copyMenu 7) copyWidth
theorem lineCapture_exec {n : Nat} (F : Family n)
    (c : SourceMenuCompare.Saved) (h : SourceMenuSortStep.Held)
    (d : Data) (t : Held) (oldMenu : BitString) :
    Exec lineCapture (full (menuCore (SourceMenuFromFamily.terminal F c h))
      d t ⟨oldMenu,List.replicate (n + 1) true⟩) 3
      (full (menuCore (SourceMenuFromFamily.terminal F c h)) d
        ⟨matrixBits (sourceMenu F),List.replicate (n + 1) true⟩ (retained F)) := by
  let r := menuCore (SourceMenuFromFamily.terminal F c h)
  let s : Saved := ⟨oldMenu,List.replicate (n + 1) true⟩
  have output : r.get 7 = matrixBits (sourceMenu F) :=
    Frame.get_core (SourceMenuFromFamily.terminal F c h) (Store.empty 24) 7
  have first := copyPending_exec r d t s 7
  rw [output] at first
  have second := copyMenu_exec r d {t with pending := matrixBits (sourceMenu F)} s 7
  rw [output] at second
  have third := copyWidth_exec r d {t with pending := matrixBits (sourceMenu F)} (retained F)
  exact Exec.seq first (Exec.seq second third)

def line : Block 48 := .seq linePrepare <|
  .seq (Frame.block 34 SourceMenuFromFamily.block) <|
    .seq lineCapture (countWrite (natural 1))
def linePolynomial : NatPolynomial := .add SourceMenuBudget.costPolynomial (.constant 48)

theorem line_exec {n : Nat} (F : Family n) (count : Nat) (r : Store 38)
    (normal packet output oldMenu : BitString) (t : Held) :
    ∃ used after, Exec line
      (full r (current (base F count) normal packet output)
        t ⟨oldMenu,List.replicate (n + 1) true⟩) used
      (full after (current (base F 1) normal packet output)
        ⟨matrixBits (sourceMenu F),List.replicate (n + 1) true⟩ (retained F)) ∧
      used ≤ linePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let d := current (base F count) normal packet output
  let s : Saved := ⟨oldMenu,List.replicate (n + 1) true⟩
  have first := linePrepare_exec F count r normal packet output oldMenu t
  obtain ⟨used,c,h,built,bound⟩ := SourceMenuBudget.block_original_bound F compareZero sortZero
  have second := Frame.execution built (menuFrame d t s)
  have third := lineCapture_exec F c h d t oldMenu
  have fourth : Exec (countWrite (natural 1))
      (full (menuCore (SourceMenuFromFamily.terminal F c h)) d
        ⟨matrixBits (sourceMenu F),List.replicate (n + 1) true⟩ (retained F)) 3
      (full (menuCore (SourceMenuFromFamily.terminal F c h))
        (current (base F 1) normal packet output)
        ⟨matrixBits (sourceMenu F),List.replicate (n + 1) true⟩ (retained F)) :=
    countWrite_exec _ _ _ _ _
  refine ⟨42 + (used + (3 + 3)),menuCore (SourceMenuFromFamily.terminal F c h),
    Exec.seq first (Exec.seq second (Exec.seq third fourth)),?_⟩
  change _ ≤ SourceMenuBudget.costPolynomial.eval _ + 48
  omega

def planeLoad : Block 48 := .seq (.action (.copy 0 46)) (.action (.copy 1 47))
theorem planeLoad_exec {n : Nat} (F : Family n) (d : Data) (t : Held) :
    Exec planeLoad (full (Store.empty 38) d t (retained F)) 2
      (full (menuCore (SourcePlaneMenu.full (SourcePlaneMenu.initial (sourceMenu F) [])
        compareZero pairZero)) d t (retained F)) := Exec.seq (.action _ _) (.action _ _)
def planePrepare : Block 48 := .seq reset planeLoad
theorem planePrepare_exec {n : Nat} (F : Family n) (r : Store 38) (d : Data) (t : Held) :
    Exec planePrepare (full r d t (retained F)) 41
      (full (menuCore (SourcePlaneMenu.full (SourcePlaneMenu.initial (sourceMenu F) [])
        compareZero pairZero)) d t (retained F)) :=
  Exec.seq (reset_exec _ _ _ _) (planeLoad_exec F d t)

def widthBody : Block 9 := .seq (.action (.push 8 true)) (.action (.pop 2))
def widthLoop : Block 9 := .loop 2 widthBody
theorem widthLoop_exec (r : Registers) (remaining prior : Nat) :
    Exec widthLoop
      ({r with remaining := List.replicate remaining true,output := List.replicate prior true}).store
      (3 * remaining + 1)
      ({r with remaining := [],output := List.replicate (remaining + prior) true}).store := by
  induction remaining generalizing prior with
  | zero =>
    simp only [Nat.zero_add,Nat.mul_zero]
    exact Exec.loopStop rfl
  | succ remaining ih =>
    have first : Exec widthBody
        ({r with remaining := List.replicate (remaining + 1) true, output := List.replicate prior true}).store 2
        ({r with remaining := List.replicate remaining true, output := List.replicate (prior + 1) true}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have total : remaining + (prior + 1) = (remaining + 1) + prior := by omega
    have cost : 3 * (remaining + 1) + 1 = 1 + (2 + (3 * remaining + 1)) := by omega
    simpa only [widthLoop,total,cost] using Exec.loopStep (source := (2 : Fin 9)) rfl first (ih (prior + 1))

def doubleWidth : Block 9 :=
  .seq (.seq (.action (.copy 8 1)) (.action (.copy 2 1))) widthLoop
def doubled (r : Registers) (width : Nat) : Registers :=
  {r with remaining := [],output := List.replicate (2 * width) true}
theorem doubleWidth_exec (r : Registers) (width : Nat) (h : r.target = List.replicate width true) :
    Exec doubleWidth r.store (3 * width + 3) (doubled r width).store := by
  have copied : Exec (.seq (.action (.copy (8 : Fin 9) 1)) (.action (.copy 2 1))) r.store 2
      ({r with remaining := r.target,output := r.target}).store :=
    Exec.seq (.action _ _) (.action _ _)
  rw [h] at copied
  have last := widthLoop_exec r width width
  have total : width + width = 2 * width := by omega
  have cost : 3 * width + 3 = 2 + (3 * width + 1) := by omega
  rw [h,total] at last
  have run := Exec.seq copied last
  simpa only [doubleWidth,doubled,cost,h] using run

def pairCore (r : Registers) (c : SourceMenuCompare.Saved) (h : SourcePlaneMenu.Held) : Store 38 :=
  menuCore (SourcePlaneMenu.full r c h)
def pairFrame (c : SourceMenuCompare.Saved) (h : SourcePlaneMenu.Held)
    (d : Data) (t : Held) (s : Saved) : Store 39 :=
  Frame.join (SourcePlaneMenu.frame c h) (menuFrame d t s)

def planeCapture : Block 48 := .seq (.action (.copy 44 8)) <|
  .seq (Frame.block 39 doubleWidth) <|
    .seq (.action (.copy 45 8)) (countWrite (natural 2))

theorem planeCapture_exec (r : Registers) (c : SourceMenuCompare.Saved) (h : SourcePlaneMenu.Held)
    (d : Data) (t : Held) (s : Saved) (width : Nat)
    (size : r.target = List.replicate width true) :
    Exec planeCapture (full (pairCore r c h) d t s) (3 * width + 9)
      (full (pairCore (doubled r width) c h) {d with count := natural 2}
        ⟨r.output,List.replicate (2 * width) true⟩ s) := by
  let saved : Held := ⟨r.output,t.width⟩
  let last : Held := ⟨r.output,List.replicate (2 * width) true⟩
  have first : Exec (.action (.copy (44 : Fin 48) 8)) (full (pairCore r c h) d t s) 1
      (full (pairCore r c h) d saved s) := Exec.action _ _
  have second := Frame.execution (doubleWidth_exec r width size) (pairFrame c h d saved s)
  have third : Exec (.action (.copy (45 : Fin 48) 8))
      (full (pairCore (doubled r width) c h) d saved s) 1
      (full (pairCore (doubled r width) c h) d last s) := Exec.action _ _
  have fourth : Exec (countWrite (natural 2))
      (full (pairCore (doubled r width) c h) d last s) 4
      (full (pairCore (doubled r width) c h) {d with count := natural 2} last s) :=
    countWrite_exec _ _ _ _ _
  have cost : 3 * width + 9 = 1 + ((3 * width + 3) + (1 + 4)) := by omega
  simpa only [planeCapture,cost,last] using Exec.seq first (Exec.seq second (Exec.seq third fourth))

def plane : Block 48 := .seq planePrepare <|
  .seq (Frame.block 34 SourcePlaneMenu.block) planeCapture
def planePolynomial : NatPolynomial := .add SourcePlaneMenuBudget.costPolynomial (.linear 3 53)

theorem plane_exec {n : Nat} (F : Family n) (count : Nat) (r : Store 38)
    (normal packet output : BitString) (t : Held) :
    ∃ used after, Exec plane
      (full r (current (base F count) normal packet output) t (retained F)) used
      (full after (current (base F 2) normal packet output)
        ⟨SourcePlaneMenuBytes.pairBits (planeMenu (sourceMenu F)),
          List.replicate (2 * (n + 1)) true⟩ (retained F)) ∧
      used ≤ planePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let d := current (base F count) normal packet output
  have first := planePrepare_exec F r d t
  obtain ⟨used,c,pending,built,bound⟩ := SourcePlaneMenuBudget.block_original_bound F compareZero pairZero
  let h : SourcePlaneMenu.Held := ⟨pending,matrixBits (sourceMenu F)⟩
  have second := Frame.execution built (menuFrame d t (retained F))
  have third := planeCapture_exec (SourcePlaneMenu.result (sourceMenu F)) c h d t (retained F)
    (n + 1) rfl
  rw [SourcePlaneMenu.result_output] at third
  refine ⟨41 + (used + (3 * (n + 1) + 9)),
    pairCore (doubled (SourcePlaneMenu.result (sourceMenu F)) (n + 1)) c h,
    Exec.seq first (Exec.seq second third),?_⟩
  have dim := SourceMatrixEncoding.dimension_bound n F
  simp only [planePolynomial,NatPolynomial.eval_add,NatPolynomial.eval_linear]
  omega

end PNP.Concrete.ResidualReduction.SourceSelectorMenus
