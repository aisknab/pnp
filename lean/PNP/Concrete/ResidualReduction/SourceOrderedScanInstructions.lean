import PNP.Concrete.ResidualReduction.SourceOrderedScanAlgebra

/-! Literal paired scans for the first nonzero and first differing matrix entry.
The flag and unary position are computed internally. Every rejected coefficient
and the no-entry branch are included in the instruction count. -/

namespace PNP.Concrete.ResidualReduction.SourceOrderedScan
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra (coefficientMatrixBits_length)
open PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions (readInput readInput_exec)
open PNP.Concrete.ResidualReduction.SourceBilinearEvaluation (readTarget readTarget_exec)

/-- Registers 0 and 1 are working matrix copies; 4 is the found flag and 8
the unary number of rejected entries. Other registers are preserved. -/
def step (difference : Bool) : Block 9 :=
  readInput fun c => readTarget fun a =>
    if test difference c a then
      .seq (.action (.clear 0)) (.seq (.action (.clear 1)) (.action (.push 4 true)))
    else .action (.push 8 true)
def block (difference : Bool) : Block 9 := .loop 0 (step difference)

theorem step_miss (r : Registers) (difference c a : Bool)
    (h : test difference c a = false) :
    Exec (step difference)
      ({r with input := c :: r.input, target := a :: r.target, sign := []}).store 5
      ({r with sign := [], output := true :: r.output}).store := by
  unfold step
  refine readInput_exec {r with target := a :: r.target, sign := []} c _ 3 _ ?_
  refine readTarget_exec {r with sign := []} a _ 1 _ ?_
  simp only [h, Bool.false_eq_true, if_false]
  exact .action _ _

theorem step_hit (r : Registers) (difference c a : Bool)
    (h : test difference c a = true) :
    Exec (step difference)
      ({r with input := c :: r.input, target := a :: r.target, sign := []}).store 7
      ({r with input := [], target := [], sign := [true]}).store := by
  unfold step
  refine readInput_exec {r with target := a :: r.target, sign := []} c _ 5 _ ?_
  refine readTarget_exec {r with sign := []} a _ 3 _ ?_
  simp only [h, if_true]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def flag : Bool → BitString
  | false => []
  | true => [true]
def fuel (result : Bool × Nat) : Nat := 6 * result.2 + if result.1 then 9 else 1

private theorem replicate_push (count : Nat) (output : BitString) :
    List.replicate count true ++ true :: output = List.replicate (count + 1) true ++ output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

theorem block_exec (r : Registers) (difference : Bool) (cs as : BitString)
    (same : cs.length = as.length) :
    let result := search (List.zipWith (test difference) cs as)
    Exec (block difference) ({r with input := cs, target := as, sign := []}).store
      (fuel result)
      ({r with
        input := [], target := [], sign := flag result.1,
        output := List.replicate result.2 true ++ r.output}).store := by
  dsimp only
  induction cs generalizing r as with
  | nil =>
    cases as with
    | nil => exact Exec.loopStop rfl
    | cons a as => cases same
  | cons c cs ih =>
    cases as with
    | nil => cases same
    | cons a as =>
      have lengths : cs.length = as.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using same
      cases h : test difference c a with
      | true =>
        have first := step_hit {r with input := cs, target := as} difference c a h
        have last : Exec (block difference)
            ({r with input := [], target := [], sign := [true]}).store 1
            ({r with input := [], target := [], sign := [true]}).store :=
          Exec.loopStop rfl
        have checked := Exec.loopStep (source := (0 : Fin 9)) rfl first last
        simpa only [block, List.zipWith_cons_cons, h, search, flag, fuel, Nat.mul_zero,
          Nat.zero_add, if_true, List.replicate_zero, List.nil_append] using checked
      | false =>
        have first := step_miss {r with input := cs, target := as} difference c a h
        have rest := ih {r with output := true :: r.output} as lengths
        have checked := Exec.loopStep (source := (0 : Fin 9)) rfl first rest
        have cost : fuel (search (List.zipWith (test difference) (c :: cs) (a :: as))) =
            1 + (5 + fuel (search (List.zipWith (test difference) cs as))) := by
          simp only [List.zipWith_cons_cons, h, search, fuel]
          omega
        rw [cost]
        simpa only [block, List.zipWith_cons_cons, h, search, replicate_push] using checked

theorem fuel_bound (result : Bool × Nat) (length : Nat) (h : result.2 ≤ length) :
    fuel result ≤ 6 * length + 9 := by
  have bound := Nat.mul_le_mul_left 6 h
  unfold fuel
  split <;> omega

def matrixStart {m n : Nat} (r : Registers) (A C : Matrix m n) : Registers :=
  {r with input := coefficientMatrixBits C, target := coefficientMatrixBits A, sign := [], output := []}
def matrixResult {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) : Registers :=
  {r with
    input := [], target := [],
    sign := flag (matrixSearch difference A C).1,
    output := List.replicate (matrixSearch difference A C).2 true}

theorem matrix_exec (r : Registers) {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    Exec (block difference) (matrixStart r A C).store (fuel (matrixSearch difference A C))
      (matrixResult r difference A C).store := by
  simpa only [matrixStart, matrixResult, matrixSearch, List.append_nil] using
    block_exec {r with output := []} difference (coefficientMatrixBits C) (coefficientMatrixBits A)
      (by rw [coefficientMatrixBits_length, coefficientMatrixBits_length])

theorem matrix_fuel_bound {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    fuel (matrixSearch difference A C) ≤ 6 * (m * n) + 9 :=
  fuel_bound _ _ (matrix_search_bound difference A C)

def program (difference : Bool) : Program 9 := (block difference).program 0 8
theorem program_run (r : Registers) {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    BitRegister.run (program difference) (fuel (matrixSearch difference A C) + 1)
        ⟨.running 0, (matrixStart r A C).store⟩ =
      ⟨.accepted, (matrixResult r difference A C).store⟩ :=
  (matrix_exec r difference A C).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceOrderedScan
