import PNP.Concrete.ResidualReduction.SourceMenuInsertion
import PNP.Concrete.ResidualReduction.SourceMenuFamily

/-! One outer sorting step for an arbitrary homogeneous candidate stream.
Pending source records and width are protected while the exact insertion
machine runs. No sorted-menu or runtime certificate is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuSortStep
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder

structure Held where
  pending : BitString
  width : BitString
deriving Repr

def Held.store (t : Held) : Store 2 := .cons t.pending (.cons t.width .nil)
def full (r : Registers) (s : SourceMenuCompare.Saved) (t : Held) : Store 14 :=
  Frame.join (SourceMenuCompare.full r s) t.store
def frame (s : SourceMenuCompare.Saved) (t : Held) : Store 5 :=
  Frame.join s.store t.store

def initial {n : Nat} (xs us : List (Affine n)) : Registers :=
  ⟨matrixBits xs, List.replicate (n + 1) true, [], [], [], [], [], matrixBits us, []⟩
def loaded {n : Nat} (a : Affine n) (xs us : List (Affine n)) : Registers :=
  {initial xs us with sign := affineWord a}
def loadFinish : Block 9 := .seq (.action (.copy 4 8)) (.action (.clear 8))
def load : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq copyLoop <| .seq ClauseQuery.reverseLoop loadFinish
def loadCost (n : Nat) : Nat := 9 * (n + 1) + 5

theorem load_exec {n : Nat} (a : Affine n) (xs us : List (Affine n)) :
    Exec load (initial (a :: xs) us).store (loadCost n) (loaded a xs us).store := by
  let seed := initial xs us
  have first : Exec (.action (.copy (2 : Fin 9) 1)) (initial (a :: xs) us).store 1
      ({seed with
        input := affineWord a ++ matrixBits xs, remaining := List.replicate (n + 1) true}).store :=
    Exec.action _ _
  have copied : Exec copyLoop
      ({seed with
        input := affineWord a ++ matrixBits xs, remaining := List.replicate (n + 1) true}).store
      (5 * (n + 1) + 1) ({seed with excess := (affineWord a).reverse}).store := by
    simpa only [seed, initial, affineWord_length, List.append_nil] using
      copy_exec seed (affineWord a) (matrixBits xs)
  have reversed : Exec ClauseQuery.reverseLoop ({seed with excess := (affineWord a).reverse}).store
      (4 * (n + 1) + 1) ({seed with output := affineWord a}).store := by
    simpa only [seed, initial, List.length_reverse, affineWord_length,
      List.reverse_reverse, List.append_nil] using ClauseQuery.reverse_exec seed (affineWord a).reverse
  have last : Exec loadFinish ({seed with output := affineWord a}).store 2
      (loaded a xs us).store := Exec.seq (.action _ _) (.action _ _)
  have count : loadCost n = 1 + ((5 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 2)) := by
    unfold loadCost
    omega
  simpa only [load, count] using Exec.seq first (Exec.seq copied (Exec.seq reversed last))

def snapshot (r : Registers) : Held := ⟨r.input, r.target⟩
def capture : Block 14 := .seq (.action (.copy 12 0)) (.action (.copy 13 1))
theorem capture_exec (r : Registers) (s : SourceMenuCompare.Saved) (t : Held) :
    Exec capture (full r s t) 2 (full r s (snapshot r)) :=
  Exec.seq (.action _ _) (.action _ _)

def prepare : Block 9 := .seq (.action (.copy 0 7)) <|
  .seq (.action (.push 6 true)) (.action (.clear 7))
theorem prepare_exec {n : Nat} (a : Affine n) (xs us : List (Affine n)) :
    Exec prepare (loaded a xs us).store 3 (SourceMenuInsertStep.ready a us []).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def enter : Block 14 := .seq capture (Frame.block 5 prepare)
theorem enter_exec {n : Nat} (a : Affine n) (xs us : List (Affine n))
    (s : SourceMenuCompare.Saved) (t : Held) :
    Exec enter (full (loaded a xs us) s t) 5
      (full (SourceMenuInsertStep.ready a us []) s (snapshot (loaded a xs us))) :=
  Exec.seq (capture_exec (loaded a xs us) s t)
    (Frame.execution (prepare_exec a xs us) (frame s (snapshot (loaded a xs us))))

def reload : Block 14 := .seq (.action (.copy 0 12)) <|
  .seq (.action (.copy 1 13)) (.action (.copy 7 8))
def reloaded (r : Registers) (t : Held) : Registers :=
  {r with input := t.pending, target := t.width, reserved := r.output}
theorem reload_exec (r : Registers) (s : SourceMenuCompare.Saved) (t : Held) :
    Exec reload (full r s t) 3 (full (reloaded r t) s t) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def restore : Block 14 := .seq reload (Frame.block 5 SourceMenuRow.clearWork)
theorem restore_exec (r : Registers) (s : SourceMenuCompare.Saved) (t : Held) :
    Exec restore (full r s t) 9 (full (SourceMenuRow.cleared (reloaded r t)) s t) :=
  Exec.seq (reload_exec r s t)
    (Frame.execution (SourceMenuRow.clearWork_exec (reloaded r t)) (frame s t))

def block : Block 14 := .seq (Frame.block 5 load) <|
  .seq enter <| .seq (Frame.block 2 SourceMenuInsertion.block) restore
def bound (n m : Nat) : Nat := loadCost n + (5 + (SourceMenuInsertion.bound n m 0 + 9))

theorem block_exec {n : Nat} (a : Affine n) (xs us : List (Affine n))
    (ha : Homogeneous a) (hu : ∀ b ∈ us, Homogeneous b)
    (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held, Exec block (full (initial (a :: xs) us) s t) used
      (full (initial xs (insertNormal a us)) last held) ∧ used ≤ bound n us.length := by
  have first := Frame.execution (load_exec a xs us) (frame s t)
  have second := enter_exec a xs us s t
  obtain ⟨used, after, last, inserted, _, output, budget⟩ :=
    SourceMenuInsertion.block_exec a ha us [] s hu
  let held := snapshot (loaded a xs us)
  have third := Frame.execution inserted held.store
  have fourth := restore_exec after last held
  have restored : SourceMenuRow.cleared (reloaded after held) = initial xs (insertNormal a us) := by
    simp only [List.reverse_nil, List.nil_append] at output
    simp only [SourceMenuRow.cleared, reloaded, held, snapshot, loaded, initial, output]
  rw [restored] at fourth
  refine ⟨loadCost n + (5 + (used + 9)), last, held,
    Exec.seq first (Exec.seq second (Exec.seq third fourth)), ?_⟩
  simpa only [bound, List.length_nil] using Nat.add_le_add_left
    (Nat.add_le_add_left (Nat.add_le_add_right budget 9) 5) (loadCost n)

theorem bound_mono (n a b : Nat) (h : a ≤ b) : bound n a ≤ bound n b := by
  have multiplied := Nat.mul_le_mul_left (80 * (n + 1) + 80) (Nat.add_le_add_right h 1)
  simp only [bound, SourceMenuInsertion.bound, Nat.mul_zero, Nat.add_zero]
  omega

end PNP.Concrete.ResidualReduction.SourceMenuSortStep
