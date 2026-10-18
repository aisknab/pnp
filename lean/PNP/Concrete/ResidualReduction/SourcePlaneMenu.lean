import PNP.Concrete.ResidualReduction.SourcePlaneMenuScan
import PNP.Concrete.ResidualReduction.SourceMenuSortStep

/-! Literal nested traversal for the ordered plane candidate menu. The complete
menu is copied from the input, not supplied as a second authority. Each eligible
pair is emitted in reference order after one final byte reversal. This prepared
block is a component of selection, not a complete contraction or SAT solver. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMenu
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes

structure Held where
  pending : BitString
  menu : BitString
deriving Repr
def Held.store (t : Held) : Store 2 := .cons t.pending (.cons t.menu .nil)
def full (r : Registers) (s : SourceMenuCompare.Saved) (t : Held) : Store 14 :=
  Frame.join (SourceMenuCompare.full r s) t.store
def frame (s : SourceMenuCompare.Saved) (t : Held) : Store 5 :=
  Frame.join s.store t.store
def initial {n : Nat} (xs : List (Affine n)) (prior : BitString) : Registers :=
  ⟨matrixBits xs, List.replicate (n + 1) true, [], [], [], [], [], prior, []⟩
def loaded {n : Nat} (a : Affine n) (xs : List (Affine n)) (prior : BitString) : Registers :=
  {initial xs prior with sign := affineWord a}

theorem load_exec {n : Nat} (a : Affine n) (xs : List (Affine n)) (prior : BitString) :
    Exec SourceMenuSortStep.load (initial (a :: xs) prior).store
      (SourceMenuSortStep.loadCost n) (loaded a xs prior).store := by
  let seed := initial xs prior
  have first : Exec (.action (.copy (2 : Fin 9) 1)) (initial (a :: xs) prior).store 1
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
  have last : Exec SourceMenuSortStep.loadFinish ({seed with output := affineWord a}).store 2
      (loaded a xs prior).store := Exec.seq (.action _ _) (.action _ _)
  have count : SourceMenuSortStep.loadCost n =
      1 + ((5 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 2)) := by
    unfold SourceMenuSortStep.loadCost
    omega
  simpa only [SourceMenuSortStep.load, count] using
    Exec.seq first (Exec.seq copied (Exec.seq reversed last))

def enter : Block 14 := .seq (.action (.copy 12 0)) <|
  .seq (.action (.copy 0 13)) (.action (.push 6 true))
theorem enter_exec {n : Nat} (a : Affine n) (xs us : List (Affine n)) (prior pending : BitString)
    (s : SourceMenuCompare.Saved) :
    Exec enter (full (loaded a xs prior) s ⟨pending, matrixBits us⟩) 3
      (full (SourceMenuInsertStep.ready a us prior) s ⟨matrixBits xs, matrixBits us⟩) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def restore : Block 14 := .seq (.action (.copy 0 12)) <|
  .seq (.action (.clear 4)) (.action (.clear 6))
theorem restore_exec {n : Nat} (a : Affine n) (xs us : List (Affine n)) (prior : BitString)
    (s : SourceMenuCompare.Saved) :
    Exec restore (full (SourceMenuInsertStep.ready a [] prior) s ⟨matrixBits xs, matrixBits us⟩) 3
      (full (initial xs prior) s ⟨matrixBits xs, matrixBits us⟩) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def step : Block 14 := .seq (Frame.block 5 SourceMenuSortStep.load) <|
  .seq enter <| .seq (Frame.block 2 SourcePlaneMenuScan.block) restore
def stepBound (n k : Nat) : Nat :=
  SourceMenuSortStep.loadCost n + (3 + (SourcePlaneMenuScan.bound n k + 3))

theorem step_exec {n : Nat} (a : Affine n) (xs us : List (Affine n))
    (prior pending : BitString) (s : SourceMenuCompare.Saved)
    (ha : Homogeneous a) (hu : ∀ b ∈ us, Homogeneous b) :
    ∃ used last, Exec step (full (initial (a :: xs) prior) s ⟨pending, matrixBits us⟩) used
      (full (initial xs ((rowBits a us).reverse ++ prior)) last ⟨matrixBits xs, matrixBits us⟩) ∧
      used ≤ stepBound n us.length := by
  have first := Frame.execution (load_exec a xs prior) (frame s ⟨pending, matrixBits us⟩)
  have second := enter_exec a xs us prior pending s
  obtain ⟨used, last, checked, budget⟩ := SourcePlaneMenuScan.block_exec a ha us prior s hu
  have third := Frame.execution checked (Held.store ⟨matrixBits xs, matrixBits us⟩)
  have fourth := restore_exec a xs us ((rowBits a us).reverse ++ prior) last
  refine ⟨SourceMenuSortStep.loadCost n + (3 + (used + 3)), last,
    Exec.seq first (Exec.seq second (Exec.seq third fourth)), ?_⟩
  unfold stepBound
  omega

def loop : Block 14 := .loop 0 step
def loopBound (n k remaining : Nat) : Nat := (stepBound n k + 1) * remaining + 1

theorem input_present {n : Nat} (a : Affine n) (xs : List (Affine n))
    (prior : BitString) (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ bit rest, (full (initial (a :: xs) prior) s t).get 0 = bit :: rest := by
  cases h : affineWord a with
  | nil =>
    have length := affineWord_length a
    rw [h] at length
    exact False.elim (by simp only [List.length_nil] at length; omega)
  | cons bit rest =>
    refine ⟨bit, rest ++ matrixBits xs, ?_⟩
    change affineWord a ++ matrixBits xs = _
    rw [h]
    rfl

theorem loop_exec {n : Nat} (xs us : List (Affine n)) (hu : ∀ b ∈ us, Homogeneous b) :
    ∀ (prior pending : BitString) (s : SourceMenuCompare.Saved), (∀ a ∈ xs, Homogeneous a) →
      ∃ used last held, Exec loop (full (initial xs prior) s ⟨pending, matrixBits us⟩) used
        (full (initial (n := n) [] ((pairBits (rows xs us)).reverse ++ prior)) last ⟨held, matrixBits us⟩) ∧
        used ≤ loopBound n us.length xs.length := by
  induction xs with
  | nil =>
    intro prior pending s _
    refine ⟨1, s, pending, ?_, ?_⟩
    · exact Exec.loopStop rfl
    · simp only [loopBound, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons a xs ih =>
    intro prior pending s hx
    have ha := hx a List.mem_cons_self
    have hx' : ∀ b ∈ xs, Homogeneous b := fun b hb => hx b (List.mem_cons_of_mem a hb)
    obtain ⟨headUsed, middle, first, headBound⟩ := step_exec a xs us prior pending s ha hu
    obtain ⟨used, last, held, rest, budget⟩ :=
      ih ((rowBits a us).reverse ++ prior) (matrixBits xs) middle hx'
    have output : (pairBits (rows xs us)).reverse ++ ((rowBits a us).reverse ++ prior) =
        (pairBits (rows (a :: xs) us)).reverse ++ prior := by
      simp only [rows_cons, pairBits_append, rowBits, List.reverse_append, List.append_assoc]
    rw [output] at rest
    obtain ⟨bit, tail, present⟩ := input_present a xs prior s ⟨pending, matrixBits us⟩
    refine ⟨1 + (headUsed + used), last, held,
      Exec.loopStep (source := (0 : Fin 14)) present first rest, ?_⟩
    simp only [loopBound, List.length_cons, Nat.mul_add, Nat.mul_one] at budget ⊢
    omega

def seed : Block 14 := .action (.copy 13 0)
theorem seed_exec {n : Nat} (us : List (Affine n)) (s : SourceMenuCompare.Saved) (t : Held) :
    Exec seed (full (initial us []) s t) 1
      (full (initial us []) s ⟨t.pending, matrixBits us⟩) := Exec.action _ _

def block : Block 14 := .seq seed <| .seq loop (Frame.block 5 SourceMenuInsertOutput.finish)
def bound (n k : Nat) : Nat :=
  1 + (loopBound n k k + (4 * ((2 * (n + 1)) * (k * k)) + 4))
def result {n : Nat} (us : List (Affine n)) : Registers :=
  SourceMenuInsertOutput.finished (initial (n := n) [] (pairBits (planeMenu us)).reverse)

theorem block_exec {n : Nat} (us : List (Affine n)) (hu : ∀ a ∈ us, Homogeneous a)
    (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held, Exec block (full (initial us []) s t) used
      (full (result us) last ⟨held, matrixBits us⟩) ∧ used ≤ bound n us.length := by
  have first := seed_exec us s t
  obtain ⟨used, last, held, checked, budget⟩ := loop_exec us us hu [] t.pending s hu
  simp only [rows_menu, List.append_nil] at checked
  have finish := Frame.execution
    (SourceMenuInsertOutput.finish_exec (initial (n := n) [] (pairBits (planeMenu us)).reverse))
    (frame last ⟨held, matrixBits us⟩)
  refine ⟨1 + (used + SourceMenuInsertOutput.finalCost
    (initial (n := n) [] (pairBits (planeMenu us)).reverse)), last, held,
    Exec.seq first (Exec.seq checked finish), ?_⟩
  have bytes := menu_bytes_length us
  have scaled := Nat.mul_le_mul_left 4 bytes
  simp only [bound, SourceMenuInsertOutput.finalCost, initial, List.length_reverse]
  omega

theorem result_output {n : Nat} (us : List (Affine n)) :
    (result us).output = pairBits (planeMenu us) := by
  simp only [result, SourceMenuInsertOutput.finished, initial, List.reverse_reverse]

def program : Program 14 := block.program 0 8
theorem program_run {n : Nat} (us : List (Affine n)) (hu : ∀ a ∈ us, Homogeneous a)
    (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held,
      BitRegister.run program (used + 1) ⟨.running 0, full (initial us []) s t⟩ =
        ⟨.accepted, full (result us) last ⟨held, matrixBits us⟩⟩ ∧
      (full (result us) last ⟨held, matrixBits us⟩).get 8 = pairBits (planeMenu us) ∧
      used + 1 ≤ bound n us.length + 1 := by
  obtain ⟨used, last, held, checked, budget⟩ := block_exec us hu s t
  exact ⟨used, last, held, checked.program_run 0 8, result_output us, by omega⟩

end PNP.Concrete.ResidualReduction.SourcePlaneMenu
