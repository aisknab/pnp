import PNP.Concrete.ResidualReduction.SourceMenuInsertOutput

/-! One general insertion step: read the next complete encoded normal, compare
it with the candidate using literal binary scans, and either continue, merge
an equal record, or insert before it. All suffix and prefix work is counted. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuInsertStep
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourceMenuCompare

def ready {n : Nat} (a : Affine n) (us : List (Affine n)) (prior : BitString) : Registers :=
  ⟨matrixBits us, List.replicate (n + 1) true, [], [], affineWord a,
    [], [true], prior, []⟩
def loaded {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) : Registers :=
  {ready a us prior with mode := affineWord b}
def headFinish : Block 9 := .seq (.action (.copy 5 8)) (.action (.clear 8))
def loadHead : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq copyLoop <| .seq ClauseQuery.reverseLoop headFinish
def headCost (n : Nat) : Nat := 9 * (n + 1) + 5

theorem loadHead_exec {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) :
    Exec loadHead (ready a (b :: us) prior).store (headCost n) (loaded a b us prior).store := by
  let seed := ready a us prior
  have first : Exec (.action (.copy (2 : Fin 9) 1)) (ready a (b :: us) prior).store 1
      ({seed with
        input := affineWord b ++ matrixBits us, remaining := List.replicate (n + 1) true}).store :=
    Exec.action _ _
  have copied : Exec copyLoop
      ({seed with
        input := affineWord b ++ matrixBits us, remaining := List.replicate (n + 1) true}).store
      (5 * (n + 1) + 1) ({seed with excess := (affineWord b).reverse}).store := by
    simpa only [seed, ready, affineWord_length, List.append_nil] using
      copy_exec seed (affineWord b) (matrixBits us)
  have reversed : Exec ClauseQuery.reverseLoop ({seed with excess := (affineWord b).reverse}).store
      (4 * (n + 1) + 1) ({seed with output := affineWord b}).store := by
    simpa only [seed, ready, List.length_reverse, affineWord_length, List.reverse_reverse,
      List.append_nil] using ClauseQuery.reverse_exec seed (affineWord b).reverse
  have last : Exec headFinish ({seed with output := affineWord b}).store 2 (loaded a b us prior).store :=
    Exec.seq (.action _ _) (.action _ _)
  have checked := Exec.seq first (Exec.seq copied (Exec.seq reversed last))
  have count : headCost n = 1 + ((5 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 2)) := by
    unfold headCost
    omega
  simpa only [loadHead, count] using checked

def gate : Block 12 := .branch 11 .skip (Frame.block 3 SourceMenuInsertOutput.advance)
  (.branch 2 .skip (Frame.block 3 SourceMenuInsertOutput.before)
    (Frame.block 3 SourceMenuInsertOutput.equal))
def gateCost (r : Registers) (first second : Bool) : Nat :=
  if first then
    1 + (1 + (if second then SourceMenuInsertOutput.equalCost r else SourceMenuInsertOutput.beforeCost r))
  else 1 + SourceMenuInsertOutput.advanceCost r
def selected (r : Registers) (first second : Bool) : Registers :=
  if first then
    if second then SourceMenuInsertOutput.equalResult r else SourceMenuInsertOutput.beforeResult r
  else SourceMenuInsertOutput.advanced r

theorem gate_exec (r : Registers) (s : Saved) (first second : Bool)
    (hf : s.firstFlag = [first]) (hs : r.remaining = [second]) :
    Exec gate (full r s) (gateCost r first second) (full (selected r first second) s) := by
  have firstRead : (full r s).get 11 = [first] := by change s.firstFlag = [first]; exact hf
  have secondRead : (full r s).get 2 = [second] := by change r.remaining = [second]; exact hs
  cases first <;> cases second <;> simp only [gateCost, selected, ↓reduceIte]
  · exact Exec.zero firstRead (Frame.execution (SourceMenuInsertOutput.advance_exec r) s.store)
  · exact Exec.zero firstRead (Frame.execution (SourceMenuInsertOutput.advance_exec r) s.store)
  · exact Exec.one firstRead (Exec.zero secondRead (Frame.execution (SourceMenuInsertOutput.before_exec r) s.store))
  · exact Exec.one firstRead (Exec.one secondRead (Frame.execution (SourceMenuInsertOutput.equal_exec r) s.store))

def compared {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) : Registers :=
  SourceMenuCompare.resultCore (loaded a b us prior)
def saved {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) : Saved :=
  SourceMenuCompare.resultSaved (loaded a b us prior)
def compareCost {n : Nat} (a b : Affine n) : Nat :=
  2 + (4 + (CoefficientComparison.fuel (affineWord a) (affineWord b) +
    (3 + (CoefficientComparison.fuel (affineWord b) (affineWord a) + 2))))
def step : Block 12 := .seq (Frame.block 3 loadHead) <| .seq SourceMenuCompare.block gate
def stepCost {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) : Nat :=
  headCost n + (compareCost a b + gateCost (compared a b us prior) (lower a b) (lower b a))

theorem step_exec {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) (s : Saved) :
    Exec step (full (ready a (b :: us) prior) s) (stepCost a b us prior)
      (full (selected (compared a b us prior) (lower a b) (lower b a)) (saved a b us prior)) := by
  have first := Frame.execution (loadHead_exec a b us prior) s.store
  have comparison := SourceMenuCompare.block_exec (loaded a b us prior) s
  have decision := gate_exec (compared a b us prior) (saved a b us prior) (lower a b) (lower b a) rfl rfl
  exact Exec.seq first (Exec.seq comparison decision)

theorem compareCost_bound {n : Nat} (a b : Affine n) :
    compareCost a b ≤ 28 * (n + 1) + 19 := by
  have left := CoefficientComparison.fuel_bound (affineWord a) (affineWord b)
  have right := CoefficientComparison.fuel_bound (affineWord b) (affineWord a)
  rw [affineWord_length, affineWord_length] at left right
  unfold compareCost
  omega

theorem advance_cost_bound {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString)
    (h : lower a b = false) : stepCost a b us prior ≤ 41 * (n + 1) + 32 := by
  have comparison := compareCost_bound a b
  simp only [stepCost, gateCost, h, Bool.false_eq_true, ↓reduceIte,
    SourceMenuInsertOutput.advanceCost, compared, SourceMenuCompare.resultCore, loaded, ready,
    affineWord_length, headCost]
  omega

theorem stop_cost_bound {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString)
    (h : lower a b = true) :
    stepCost a b us prior ≤ 53 * (n + 1) + 4 * prior.length +
      8 * ((n + 1) * us.length) + 45 := by
  have comparison := compareCost_bound a b
  cases second : lower b a <;>
    simp only [stepCost, gateCost, h, second, Bool.false_eq_true, ↓reduceIte,
      SourceMenuInsertOutput.equalCost, SourceMenuInsertOutput.beforeCost, compared,
      SourceMenuCompare.resultCore, loaded, ready, affineWord_length, matrixBits_length, headCost]
  all_goals omega

theorem advance_state {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) :
    SourceMenuInsertOutput.advanced (compared a b us prior) =
      ready a us ((affineWord b).reverse ++ prior) := rfl

theorem end_output {n : Nat} (a : Affine n) (prior : BitString) :
    (SourceMenuInsertOutput.endResult (ready a [] prior)).output =
      prior.reverse ++ matrixBits [a] := by
  rw [SourceMenuInsertOutput.end_output]
  simp only [ready, matrixBits, List.append_nil]

theorem equal_output {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) :
    (SourceMenuInsertOutput.equalResult (compared a b us prior)).output =
      prior.reverse ++ matrixBits (b :: us) := by
  rw [SourceMenuInsertOutput.equal_output]
  rfl

theorem before_output {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) :
    (SourceMenuInsertOutput.beforeResult (compared a b us prior)).output =
      prior.reverse ++ matrixBits (a :: b :: us) := by
  rw [SourceMenuInsertOutput.before_output]
  rfl

end PNP.Concrete.ResidualReduction.SourceMenuInsertStep
