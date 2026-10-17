import PNP.Concrete.ResidualReduction.SourceBilinearPullbackEntry

/-! Complete row-major construction of the pulled-back bilinear matrix.
Natural counters enumerate every pair of parameters. Coefficients are
computed by the literal entry program, never supplied as an oracle. Empty
parameter spaces terminate through the same counted loops. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearPullback
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

def coefficient {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (i j : Nat) : Bool :=
  if hi : i < s.parameters then
    if hj : j < t.parameters then pullMatrix M s t ⟨i, hi⟩ ⟨j, hj⟩ else false
  else false
theorem coefficient_fin {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) :
    coefficient M s t i.val j.val = pullMatrix M s t i j := by
  simp only [coefficient, dif_pos i.isLt, dif_pos j.isLt]
def columnBytes {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (i start count : Nat) : BitString :=
  (List.range' start count).map (coefficient M s t i)
def matrixBytes {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (start count : Nat) : BitString :=
  (List.range' start count).flatMap (fun i => columnBytes M s t i 0 t.parameters)
theorem columnBytes_succ {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (i start count : Nat) :
    columnBytes M s t i start (count + 1) = coefficient M s t i start :: columnBytes M s t i (start + 1) count := by
  simp only [columnBytes, List.range'_succ, List.map_cons]
theorem matrixBytes_succ {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (start count : Nat) :
    matrixBytes M s t start (count + 1) = columnBytes M s t start 0 t.parameters ++ matrixBytes M s t (start + 1) count := by
  simp only [matrixBytes, List.range'_succ, List.flatMap_cons]
theorem matrixBytes_exact {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    matrixBytes M s t 0 s.parameters = coefficientMatrixBits (pullMatrix M s t) := by
  unfold matrixBytes columnBytes coefficientMatrixBits
  rw [← SourceMatrixSchedule.finite_range_values s.parameters, ← SourceMatrixSchedule.finite_range_values t.parameters]
  simp only [List.flatMap_map, List.map_map, Function.comp_def, coefficient_fin]
theorem matrixBytes_length {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    (matrixBytes M s t 0 s.parameters).length = s.parameters * t.parameters := by
  rw [matrixBytes_exact, SourceLineQueryMatrixAlgebra.coefficientMatrixBits_length]

structure State where
  core : SourceBilinearPullbackEntry.State
  rows : BitString
  columns : BitString
  output : BitString
def State.frame (r : State) : Store 3 := .cons r.rows (.cons r.columns (.cons r.output .nil))
def State.store (r : State) : Store 21 := Frame.join r.core.store r.frame
def lifted (body : Block 18) : Block 21 := Frame.block 3 body
theorem lifted_exec (body : Block 18) (r : State) (fuel : Nat) (after : SourceBilinearPullbackEntry.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame
def registers (r : State) : Registers := r.core.core.core
def setRegisters (r : State) (s : Registers) : State :=
  {r with core := {r.core with core := {r.core.core with core := s}}}
def small (body : Block 9) : Block 21 := lifted (SourceBilinearPullbackEntry.small body)
theorem small_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body (registers r).store fuel after.store) :
    Exec (small body) r.store fuel (setRegisters r after).store :=
  lifted_exec _ r _ _ (SourceBilinearPullbackEntry.small_exec body r.core fuel after checked)
def ready {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i j rows columns : Nat) (output : BitString) : State :=
  ⟨⟨⟨base 0 [], []⟩, coefficientMatrixBits M, mapBits s.forms, mapBits t.forms,
      List.replicate s.parameters true, List.replicate t.parameters true,
      List.replicate i true, List.replicate j true, []⟩,
    List.replicate rows true, List.replicate columns true, output⟩
def withOutput (r : State) (word : BitString) : State :=
  setRegisters r {registers r with output := word}

def emit : Block 21 := .branch 8 .skip
  (.seq (.action (.pop 8)) (.action (.push 20 false)))
  (.seq (.action (.pop 8)) (.action (.push 20 true)))
theorem emit_exec (r : State) (b : Bool) :
    Exec emit (withOutput r [b]).store 3 ({withOutput r [] with output := b :: r.output}).store := by
  cases b with
  | false => exact Exec.zero (source := (8 : Fin 21)) rfl (Exec.seq (.action _ _) (.action _ _))
  | true => exact Exec.one (source := (8 : Fin 21)) rfl (Exec.seq (.action _ _) (.action _ _))
def advanceColumn : Block 21 := .seq (.action (.push 16 true)) (.action (.pop 19))
def columnStep : Block 21 := .seq (lifted SourceBilinearPullbackEntry.block) (.seq emit advanceColumn)
theorem columnStep_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (j : Fin t.parameters) (rows count : Nat) (output : BitString) :
    Exec columnStep (ready M s t i.val j.val rows (count + 1) output).store
      (SourceBilinearPullbackEntry.fuel m n s.parameters t.parameters i.val j.val + 5)
      (ready M s t i.val (j.val + 1) rows count (coefficient M s t i.val j.val :: output)).store := by
  let before := ready M s t i.val j.val rows (count + 1) output
  let computed := withOutput before [pullMatrix M s t i j]
  let emitted := ready M s t i.val j.val rows (count + 1) (pullMatrix M s t i j :: output)
  have entry : Exec (lifted SourceBilinearPullbackEntry.block) before.store
      (SourceBilinearPullbackEntry.fuel m n s.parameters t.parameters i.val j.val) computed.store :=
    lifted_exec _ before _ _ (SourceBilinearPullbackEntry.block_exec M s t i j)
  have copied : Exec emit computed.store 3 emitted.store := emit_exec before (pullMatrix M s t i j)
  have advanced : Exec advanceColumn emitted.store 2
      (ready M s t i.val (j.val + 1) rows count (pullMatrix M s t i j :: output)).store :=
    Exec.seq (.action _ _) (.action _ _)
  rw [coefficient_fin]
  exact Exec.seq entry (Exec.seq copied advanced)

def columnLoop : Block 21 := .loop 19 columnStep
def columnFuel (m n p q i : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | j, count + 1 => 1 + ((SourceBilinearPullbackEntry.fuel m n p q i j + 5) + columnFuel m n p q i (j + 1) count)
theorem columnLoop_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (count j rows : Nat) (output : BitString) (bound : j + count ≤ t.parameters) :
    Exec columnLoop (ready M s t i.val j rows count output).store
      (columnFuel m n s.parameters t.parameters i.val j count)
      (ready M s t i.val (j + count) rows 0 ((columnBytes M s t i.val j count).reverse ++ output)).store := by
  induction count generalizing j output with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have hj : j < t.parameters := by omega
    let current : Fin t.parameters := ⟨j, hj⟩
    have first := columnStep_exec M s t i current rows count output
    have rest := ih (j + 1) (coefficient M s t i.val j :: output) (by omega)
    have checked := Exec.loopStep (source := (19 : Fin 21)) rfl first rest
    have index : j + 1 + count = j + (count + 1) := by omega
    simpa only [columnLoop, columnFuel, current, columnBytes_succ, List.reverse_cons,
      List.append_assoc, List.singleton_append, index] using checked
theorem columnFuel_bound (m n p q : Nat) (i : Fin p) (count j : Nat) (bound : j + count ≤ q) :
    columnFuel m n p q i.val j count ≤ (SourceBilinearPullbackEntry.budget m n p q + 6) * count + 1 := by
  induction count generalizing j with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have hj : j < q := by omega
    have one := SourceBilinearPullbackEntry.fuel_bound (m := m) (n := n) i ⟨j, hj⟩
    have rest := ih (j + 1) (by omega)
    simp only [columnFuel, Nat.mul_add, Nat.mul_one] at one rest ⊢
    omega

def advanceRow : Block 21 := .seq (.action (.clear 16)) <|
  .seq (.action (.push 15 true)) (.action (.pop 18))
def row : Block 21 := .seq (.action (.copy 19 14)) (.seq columnLoop advanceRow)
theorem row_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (rows : Nat) (output : BitString) :
    Exec row (ready M s t i.val 0 (rows + 1) 0 output).store
      (1 + (columnFuel m n s.parameters t.parameters i.val 0 t.parameters + 3))
      (ready M s t (i.val + 1) 0 rows 0 ((columnBytes M s t i.val 0 t.parameters).reverse ++ output)).store := by
  have seed : Exec (.action (.copy (19 : Fin 21) 14)) (ready M s t i.val 0 (rows + 1) 0 output).store 1
      (ready M s t i.val 0 (rows + 1) t.parameters output).store := .action _ _
  have columns := columnLoop_exec M s t i t.parameters 0 (rows + 1) output (by omega)
  simp only [Nat.zero_add] at columns
  have advance : Exec advanceRow
      (ready M s t i.val t.parameters (rows + 1) 0 ((columnBytes M s t i.val 0 t.parameters).reverse ++ output)).store 3
      (ready M s t (i.val + 1) 0 rows 0 ((columnBytes M s t i.val 0 t.parameters).reverse ++ output)).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq seed (Exec.seq columns advance)

def matrixLoop : Block 21 := .loop 18 row
def matrixFuel (m n p q : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, count + 1 => 1 + ((1 + (columnFuel m n p q i 0 q + 3)) + matrixFuel m n p q (i + 1) count)
theorem matrixLoop_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (count i : Nat) (output : BitString) (bound : i + count ≤ s.parameters) :
    Exec matrixLoop (ready M s t i 0 count 0 output).store
      (matrixFuel m n s.parameters t.parameters i count)
      (ready M s t (i + count) 0 0 0 ((matrixBytes M s t i count).reverse ++ output)).store := by
  induction count generalizing i output with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have hi : i < s.parameters := by omega
    let current : Fin s.parameters := ⟨i, hi⟩
    have first := row_exec M s t current count output
    have rest := ih (i + 1) ((columnBytes M s t i 0 t.parameters).reverse ++ output) (by omega)
    have checked := Exec.loopStep (source := (18 : Fin 21)) rfl first rest
    have index : i + 1 + count = i + (count + 1) := by omega
    simpa only [matrixLoop, matrixFuel, current, matrixBytes_succ, List.reverse_append,
      List.append_assoc, index] using checked
theorem matrixFuel_bound (m n p q count i : Nat) (bound : i + count ≤ p) :
    matrixFuel m n p q i count ≤ ((SourceBilinearPullbackEntry.budget m n p q + 6) * q + 6) * count + 1 := by
  induction count generalizing i with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have hi : i < p := by omega
    have one := columnFuel_bound m n p q ⟨i, hi⟩ q 0 (by omega)
    have rest := ih (i + 1) (by omega)
    simp only [matrixFuel, Nat.mul_add, Nat.mul_one] at one rest ⊢
    omega

def reorder : Block 21 := .seq (.action (.copy 3 20)) <|
  .seq (.action (.clear 20)) (small ClauseQuery.reverseLoop)
theorem reorder_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (word : BitString) :
    Exec reorder (ready M s t s.parameters 0 0 0 word.reverse).store (4 * word.length + 3)
      (withOutput (ready M s t s.parameters 0 0 0 []) word).store := by
  let before := ready M s t s.parameters 0 0 0 word.reverse
  let copied := setRegisters before {base 0 [] with excess := word.reverse}
  let staged := {copied with output := []}
  let after := withOutput (ready M s t s.parameters 0 0 0 []) word
  have copy : Exec (.action (.copy (3 : Fin 21) 20)) before.store 1 copied.store := .action _ _
  have clear : Exec (.action (.clear (20 : Fin 21))) copied.store 1 staged.store := .action _ _
  have core : Exec ClauseQuery.reverseLoop (registers staged).store (4 * word.length + 1) (registers after).store := by
    simpa only [staged, copied, after, before, setRegisters, registers, withOutput, ready, base,
      List.length_reverse, List.reverse_reverse, List.append_nil] using ClauseQuery.reverse_exec (base 0 []) word.reverse
  have reversed : Exec (small ClauseQuery.reverseLoop) staged.store (4 * word.length + 1) after.store :=
    small_exec _ staged _ (registers after) core
  have cost : 4 * word.length + 3 = 1 + (1 + (4 * word.length + 1)) := by omega
  simpa only [reorder, cost, before, after] using Exec.seq copy (Exec.seq clear reversed)

def start {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) : State := ready M s t 0 0 0 0 []
def result {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) : State :=
  withOutput (ready M s t s.parameters 0 0 0 []) (coefficientMatrixBits (pullMatrix M s t))
def block : Block 21 := .seq (.action (.copy 18 13)) (.seq matrixLoop reorder)
def fuel (m n p q : Nat) : Nat := 1 + (matrixFuel m n p q 0 p + (4 * (p * q) + 3))
theorem block_exec {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    Exec block (start M s t).store (fuel m n s.parameters t.parameters) (result M s t).store := by
  have seed : Exec (.action (.copy (18 : Fin 21) 13)) (start M s t).store 1
      (ready M s t 0 0 s.parameters 0 []).store := .action _ _
  have computed := matrixLoop_exec M s t s.parameters 0 [] (by omega)
  simp only [Nat.zero_add, List.append_nil, matrixBytes_exact] at computed
  have ordered := reorder_exec M s t (coefficientMatrixBits (pullMatrix M s t))
  rw [SourceLineQueryMatrixAlgebra.coefficientMatrixBits_length] at ordered
  exact Exec.seq seed (Exec.seq computed ordered)
theorem result_output {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    (result M s t).store.get 8 = coefficientMatrixBits (pullMatrix M s t) := rfl
def budget (m n p q : Nat) : Nat :=
  1 + ((((SourceBilinearPullbackEntry.budget m n p q + 6) * q + 6) * p + 1) + (4 * (p * q) + 3))
theorem fuel_bound (m n p q : Nat) : fuel m n p q ≤ budget m n p q := by
  have scan := matrixFuel_bound m n p q p 0 (by omega)
  unfold fuel budget
  omega
theorem budget_mono (m n p q M N P Q : Nat)
    (hm : m ≤ M) (hn : n ≤ N) (hp : p ≤ P) (hq : q ≤ Q) :
    budget m n p q ≤ budget M N P Q := by
  have entry := SourceBilinearPullbackEntry.budget_mono m n p q M N P Q hm hn hp hq
  have columns := Nat.mul_le_mul (Nat.add_le_add_right entry 6) hq
  have rows := Nat.mul_le_mul (Nat.add_le_add_right columns 6) hp
  have bytes := Nat.mul_le_mul hp hq
  unfold budget
  omega
def program : Program 21 := block.program 0 8
theorem program_run {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    BitRegister.run program (fuel m n s.parameters t.parameters + 1) ⟨.running 0, (start M s t).store⟩ =
      ⟨.accepted, (result M s t).store⟩ := (block_exec M s t).program_run 0 8

def mapPolynomial : NatPolynomial :=
  .add (.mul (.constant 4) .variable)
    (.add (.add (.mul (.constant 4) .variable) (.constant 3))
      (.add (.constant 3) (.add (.mul (.add (.mul (.constant 9) .variable) (.constant 14)) .variable) (.constant 4))))
def evaluationPolynomial : NatPolynomial :=
  .add (.constant 1) (.add (.add (.mul (.add (.mul (.constant 8) .variable) (.constant 5)) .variable) (.constant 1)) (.constant 2))
def entryPolynomial : NatPolynomial :=
  .add (.constant 4) (.add mapPolynomial (.add (.constant 7)
    (.add mapPolynomial (.add (.constant 4) (.add evaluationPolynomial (.constant 3))))))
def costPolynomial : NatPolynomial :=
  .add (.constant 1)
    (.add (.add (.mul (.add (.mul (.add entryPolynomial (.constant 6)) .variable) (.constant 6)) .variable) (.constant 1))
      (.add (.mul (.constant 4) (.mul .variable .variable)) (.constant 3)))
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = budget L L L L := rfl
theorem bounded_fuel (m n p q L : Nat) (hm : m ≤ L) (hn : n ≤ L) (hp : p ≤ L) (hq : q ≤ L) :
    fuel m n p q ≤ costPolynomial.eval L :=
  Nat.le_trans (fuel_bound m n p q) (budget_mono m n p q L L L L hm hn hp hq)
theorem output_bound {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (L : Nat) (hp : s.parameters ≤ L) (hq : t.parameters ≤ L) :
    ((result M s t).store.get 8).length ≤ L * L := by
  rw [result_output, SourceLineQueryMatrixAlgebra.coefficientMatrixBits_length]
  exact Nat.mul_le_mul hp hq

/-- A source-bound budget for the exact spaces required by lineRawQuery.
This bounds the pullback construction; the physical source/solver handoff
and the later selector are deliberately not claimed by this theorem. -/
theorem original_line_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (n + F.length) (SourceDirections.directionSpace F [alpha]).parameters
      (kernelSpace (SourceLine.rankOneRows F alpha)).parameters
      (kernelSpace ([] : System (SourceDirections.directionSpace F [alpha]).parameters)).parameters ≤
      costPolynomial.eval (2 * (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length) := by
  let L := (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [alpha]
  have hd : (SourceDirections.directionSpace F [alpha]).parameters ≤ L :=
    SourceLineQueryMatrices.parameter_bound F alpha
  have rows : n + F.length ≤ 2 * L := by omega
  have columns : (SourceDirections.directionSpace F [alpha]).parameters ≤ 2 * L := by omega
  have left := Nat.le_trans (kernelSpace_parameter_bound (SourceLine.rankOneRows F alpha)) rows
  have right := Nat.le_trans
    (kernelSpace_parameter_bound ([] : System (SourceDirections.directionSpace F [alpha]).parameters)) columns
  exact bounded_fuel _ _ _ _ (2 * L) rows columns left right

end PNP.Concrete.ResidualReduction.SourceBilinearPullback
