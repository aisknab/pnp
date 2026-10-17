import PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes

/-! Counted inner traversal of the exact ordered plane menu. Strictly eligible
pairs are appended to a reversed byte accumulator; the full normal words are
compared, never their positions or a supplied order certificate. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMenuScan
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourceMenuCompare
open PNP.Concrete.ResidualReduction.SourceMenuInsertStep
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes

def discard : Block 9 := .seq (.action (.clear 2)) (.action (.clear 5))
def discarded (r : Registers) : Registers := {r with remaining := [], mode := []}
theorem discard_exec (r : Registers) :
    Exec discard r.store 2 (discarded r).store := Exec.seq (.action _ _) (.action _ _)

def emit : Block 9 := .seq (SourceMenuInsertOutput.append 4) <|
  .seq (SourceMenuInsertOutput.append 5) discard
def emitted (r : Registers) : Registers :=
  discarded (SourceMenuInsertOutput.appended (SourceMenuInsertOutput.appended r r.sign) r.mode)
def emitCost (r : Registers) : Nat := 4 * r.sign.length + (4 * r.mode.length + 12)

theorem emit_exec (r : Registers) : Exec emit r.store (emitCost r) (emitted r).store := by
  have first := SourceMenuInsertOutput.append_exec r 4
  have second := SourceMenuInsertOutput.append_exec (SourceMenuInsertOutput.appended r r.sign) 5
  have last := discard_exec
    (SourceMenuInsertOutput.appended (SourceMenuInsertOutput.appended r r.sign) r.mode)
  have count : emitCost r = SourceMenuInsertOutput.appendCost r 4 +
      (SourceMenuInsertOutput.appendCost (SourceMenuInsertOutput.appended r r.sign) 5 + 2) := by
    change 4 * r.sign.length + (4 * r.mode.length + 12) =
      (4 * r.sign.length + 5) + ((4 * r.mode.length + 5) + 2)
    omega
  simpa only [emit, emitted, count] using Exec.seq first (Exec.seq second last)

def gate : Block 12 := .branch 11 .skip (Frame.block 3 emit) (Frame.block 3 discard)
def gateCost (r : Registers) (flag : Bool) : Nat := 1 + (if flag then 2 else emitCost r)
def selected (r : Registers) (flag : Bool) : Registers :=
  if flag then discarded r else emitted r

theorem gate_exec (r : Registers) (s : Saved) (flag : Bool) (h : s.firstFlag = [flag]) :
    Exec gate (full r s) (gateCost r flag) (full (selected r flag) s) := by
  have readFlag : (full r s).get 11 = [flag] := by change s.firstFlag = [flag]; exact h
  cases flag <;> simp only [gateCost, selected, Bool.false_eq_true, ↓reduceIte]
  · exact Exec.zero readFlag (Frame.execution (emit_exec r) s.store)
  · exact Exec.one readFlag (Frame.execution (discard_exec r) s.store)

def step : Block 12 := .seq (Frame.block 3 loadHead) <| .seq SourceMenuCompare.block gate
def stepCost {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) : Nat :=
  headCost n + (compareCost a b + gateCost (compared a b us prior) (lower a b))
def nextPrior {n : Nat} (a b : Affine n) (prior : BitString) : BitString :=
  if lower a b then prior else (pairWord (a,b)).reverse ++ prior

theorem selected_state {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) :
    selected (compared a b us prior) (lower a b) = ready a us (nextPrior a b prior) := by
  cases h : lower a b <;>
    simp only [selected, nextPrior, h, Bool.false_eq_true, ↓reduceIte, emitted, discarded,
      SourceMenuInsertOutput.appended, compared, SourceMenuCompare.resultCore, loaded, ready,
      pairWord, List.reverse_append, List.append_assoc]

theorem step_exec {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) (s : Saved) :
    Exec step (full (ready a (b :: us) prior) s) (stepCost a b us prior)
      (full (ready a us (nextPrior a b prior)) (saved a b us prior)) := by
  have first := Frame.execution (loadHead_exec a b us prior) s.store
  have comparison := SourceMenuCompare.block_exec (loaded a b us prior) s
  have decision := gate_exec (compared a b us prior) (saved a b us prior) (lower a b) rfl
  rw [selected_state] at decision
  exact Exec.seq first (Exec.seq comparison decision)

def stepBound (n : Nat) : Nat := 50 * (n + 1) + 40
theorem step_cost_bound {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) :
    stepCost a b us prior ≤ stepBound n := by
  have comparison := compareCost_bound a b
  cases h : lower a b <;>
    simp only [stepCost, h, gateCost, Bool.false_eq_true, ↓reduceIte, emitCost, compared,
      SourceMenuCompare.resultCore, loaded, ready, affineWord_length, headCost, stepBound]
  all_goals omega

def block : Block 12 := .loop 0 step
def bound (n k : Nat) : Nat := (stepBound n + 1) * k + 1

theorem input_present {n : Nat} (a b : Affine n) (us : List (Affine n))
    (prior : BitString) (s : Saved) :
    ∃ bit rest, (full (ready a (b :: us) prior) s).get 0 = bit :: rest := by
  cases h : affineWord b with
  | nil =>
    have length := affineWord_length b
    rw [h] at length
    exact False.elim (by simp only [List.length_nil] at length; omega)
  | cons bit rest =>
    refine ⟨bit, rest ++ matrixBits us, ?_⟩
    change affineWord b ++ matrixBits us = _
    rw [h]
    rfl

theorem block_exec {n : Nat} (a : Affine n) (ha : Homogeneous a) (us : List (Affine n)) :
    ∀ (prior : BitString) (s : Saved), (∀ b ∈ us, Homogeneous b) →
      ∃ used last, Exec block (full (ready a us prior) s) used
        (full (ready a [] ((rowBits a us).reverse ++ prior)) last) ∧
        used ≤ bound n us.length := by
  induction us with
  | nil =>
    intro prior s _
    refine ⟨1, s, ?_, ?_⟩
    · exact Exec.loopStop rfl
    · simp only [bound, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons b us ih =>
    intro prior s hu
    have hb := hu b List.mem_cons_self
    have hu' : ∀ c ∈ us, Homogeneous c := fun c hc => hu c (List.mem_cons_of_mem b hc)
    have first := step_exec a b us prior s
    obtain ⟨used, last, rest, budget⟩ := ih (nextPrior a b prior) (saved a b us prior) hu'
    obtain ⟨bit, tail, present⟩ := input_present a b us prior s
    have output : (rowBits a us).reverse ++ nextPrior a b prior =
        (rowBits a (b :: us)).reverse ++ prior := by
      rw [rowBits_cons a b us ha hb]
      cases h : lower a b <;> simp only [nextPrior, h, Bool.false_eq_true, ↓reduceIte,
        List.reverse_append, List.append_assoc]
    rw [output] at rest
    refine ⟨1 + (stepCost a b us prior + used), last,
      Exec.loopStep (source := (0 : Fin 12)) present first rest, ?_⟩
    have head := step_cost_bound a b us prior
    simp only [bound, List.length_cons, Nat.mul_add, Nat.mul_one] at budget ⊢
    omega

end PNP.Concrete.ResidualReduction.SourcePlaneMenuScan
