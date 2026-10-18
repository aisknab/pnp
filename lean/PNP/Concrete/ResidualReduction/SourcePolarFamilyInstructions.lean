import PNP.Concrete.ResidualReduction.SourcePolarRowInstructions

/-! Literal construction of the complete polar-row family from source-row
bytes and an explicit coefficient map. Source extraction, both pullbacks,
every basis row, and output reordering are charged. The final input-to-kernel
caller must still construct this map and prove its original-input handoff. -/

namespace PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarRowInstructions

structure State where
  core : SourcePolarPairInstructions.State
  source : BitString
def State.frame (r : State) : Store 1 := .cons r.source .nil
def State.store (r : State) : Store 18 := Frame.join r.core.store r.frame
def lift (body : Block 17) : Block 18 := Frame.block 1 body
theorem lift_exec (body : Block 17) (r : State) (fuel : Nat)
    (after : SourcePolarPairInstructions.State) (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame
def small (body : Block 9) : Block 18 := lift (SourcePolarPairInstructions.lift body)
theorem small_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.core.store fuel after.store) :
    Exec (small body) r.store fuel ({r with core := {r.core with core := after}}).store :=
  Frame.execution (Frame.execution checked r.core.frame) r.frame

def ready (n k : Nat) (map source output : BitString) : State :=
  ⟨idle n (k + 1) map output, source⟩
def extract : Block 9 := .seq copyLoop ClauseQuery.reverseLoop
theorem extract_exec (width : Nat) (front suffix : BitString) :
    Exec extract ({base width [] with input := front ++ suffix, remaining := List.replicate front.length true}).store
      (9 * front.length + 2) ({base width [] with input := suffix, output := front}).store := by
  have copied : Exec copyLoop
      ({base width [] with input := front ++ suffix, remaining := List.replicate front.length true}).store
      (5 * front.length + 1) ({base width [] with input := suffix, excess := front.reverse}).store := by
    simpa only [base, List.append_nil] using copy_exec (base width []) front suffix
  have reversed : Exec ClauseQuery.reverseLoop
      ({base width [] with input := suffix, excess := front.reverse}).store
      (4 * front.length + 1) ({base width [] with input := suffix, output := front}).store := by
    simpa only [base, List.append_nil, List.length_reverse, List.reverse_reverse] using
      ClauseQuery.reverse_exec {base width [] with input := suffix} front.reverse
  have cost : 9 * front.length + 2 = (5 * front.length + 1) + (4 * front.length + 1) := by omega
  simpa only [extract, cost] using Exec.seq copied reversed

def loadHeader : Block 18 := .seq (.action (.copy 16 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.copy 0 17)) <|
    .seq (.action (.pop 0)) <| .seq (.action (.copy 2 9)) (.action (.push 2 true))
def loadRight : Block 18 := .seq (.action (.copy 10 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.copy 2 9)) (.action (.push 2 true))
def loadFinish : Block 18 := .seq (.action (.copy 11 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.copy 17 0)) <|
    .seq (.action (.clear 0)) <| .seq (.action (.copy 14 1)) (.action (.pop 14))
def load : Block 18 := .seq loadHeader <| .seq (small extract) <|
  .seq loadRight (.seq (small extract) loadFinish)
def loadFuel (n : Nat) : Nat := 18 * (n + 1) + 20

theorem load_exec {n k : Nat} (row : Row n) (m : AffineMap n k) (suffix output : BitString) :
    Exec load (ready n k (mapBits m) (rowWord row ++ suffix) output).store (loadFuel n)
      (State.mk (start row m output) suffix).store := by
  let before := ready n k (mapBits m) (rowWord row ++ suffix) output
  let loaded : State := ⟨{idle n (k + 1) (mapBits m) [] with core := {base (k + 1) [] with input := (affineWord row.left ++ affineWord row.right) ++ suffix, remaining := List.replicate (n + 1) true}, savedOutput := output}, before.source⟩
  let leftDone : State := {loaded with core := {loaded.core with core := {base (k + 1) [] with input := affineWord row.right ++ suffix, output := affineWord row.left}}}
  let rightReady : State := {leftDone with core := {leftDone.core with core := {base (k + 1) [] with input := affineWord row.right ++ suffix, remaining := List.replicate (n + 1) true}, left := affineWord row.left}}
  let rightDone : State := {rightReady with core := {rightReady.core with core := {base (k + 1) [] with input := suffix, output := affineWord row.right}}}
  have header : Exec loadHeader before.store 6 loaded.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have leftCore : Exec extract loaded.core.core.store (9 * (n + 1) + 2) leftDone.core.core.store := by
    simpa only [loaded, leftDone, affineWord_length, List.append_assoc] using
      extract_exec (k + 1) (affineWord row.left) (affineWord row.right ++ suffix)
  have left := small_exec extract loaded _ leftDone.core.core leftCore
  have rightHeader : Exec loadRight leftDone.store 4 rightReady.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have rightCore : Exec extract rightReady.core.core.store (9 * (n + 1) + 2) rightDone.core.core.store := by
    simpa only [rightReady, rightDone, affineWord_length] using
      extract_exec (k + 1) (affineWord row.right) suffix
  have right := small_exec extract rightReady _ rightDone.core.core rightCore
  have finish : Exec loadFinish rightDone.store 6 (State.mk (start row m output) suffix).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have cost : loadFuel n = 6 + ((9 * (n + 1) + 2) + (4 + ((9 * (n + 1) + 2) + 6))) := by
    unfold loadFuel
    omega
  simpa only [load, cost] using Exec.seq header (Exec.seq left (Exec.seq rightHeader (Exec.seq right finish)))

def row : Block 18 := .seq load (lift SourcePolarRowInstructions.block)
theorem row_exec {n k : Nat} (r : Row n) (m : AffineMap n k) (suffix output : BitString) :
    Exec row (ready n k (mapBits m) (rowWord r ++ suffix) output).store
      (loadFuel n + SourcePolarRowInstructions.fuel k r)
      (ready n k (mapBits m) suffix
        ((matrixBits (pairRows r (pullback r.left m) (pullback r.right m))).reverse ++ output)).store :=
  Exec.seq (load_exec r m suffix output)
    (lift_exec SourcePolarRowInstructions.block ⟨start r m output, suffix⟩ _ _
      (SourcePolarRowInstructions.block_exec r m output))

def loop : Block 18 := .loop 17 row
def loopFuel {n : Nat} (k : Nat) : Family n → Nat
  | [] => 1
  | r :: F => 1 + ((loadFuel n + SourcePolarRowInstructions.fuel k r) + loopFuel k F)
private theorem matrix_append {n : Nat} (xs ys : System n) :
    matrixBits (xs ++ ys) = matrixBits xs ++ matrixBits ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, matrixBits, ih, List.append_assoc]


theorem loop_exec {n : Nat} (F : Family n) (s : Space n) (output : BitString) :
    Exec loop (ready n s.parameters (mapBits s.forms) (familyBits F) output).store
      (loopFuel s.parameters F)
      (ready n s.parameters (mapBits s.forms) []
        ((matrixBits (sourceRows F s)).reverse ++ output)).store := by
  induction F generalizing output with
  | nil => exact Exec.loopStop rfl
  | cons r F ih =>
    have first := row_exec r s.forms (familyBits F) output
    have rest := ih ((matrixBits (pairRows r (pullback r.left s.forms) (pullback r.right s.forms))).reverse ++ output)
    have checked := Exec.loopStep (source := (17 : Fin 18)) rfl first rest
    simpa only [loop, loopFuel, familyBits, sourceRows, matrixBits_flatMap,
      List.flatMap_cons, matrix_append, List.reverse_append, List.append_assoc] using checked

theorem rowFuel_bound {n k : Nat} (r : Row n) :
    loadFuel n + SourcePolarRowInstructions.fuel k r ≤ 130 * (k + 2) * (n + 1) := by
  have bound := SourcePolarRowInstructions.fuel_bound (k := k) r
  simp only [loadFuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc,
    Nat.mul_comm k n] at *
  omega

theorem loopFuel_bound {n : Nat} (k : Nat) (F : Family n) :
    loopFuel k F ≤ (130 * (k + 2) * (n + 1) + 1) * F.length + 1 := by
  induction F with
  | nil => simp only [loopFuel, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons r F ih =>
    have one := rowFuel_bound (k := k) r
    have arithmetic (C m x y : Nat) (hx : x ≤ C) (hy : y ≤ (C + 1) * m + 1) :
        1 + (x + y) ≤ (C + 1) * (m + 1) + 1 := by
      rw [Nat.mul_succ]
      omega
    exact arithmetic (130 * (k + 2) * (n + 1)) F.length
      (loadFuel n + SourcePolarRowInstructions.fuel k r) (loopFuel k F) one ih

def reverseHeader : Block 18 := .seq (.action (.copy 3 8)) (.action (.clear 8))
def reorder : Block 18 := .seq reverseHeader (small ClauseQuery.reverseLoop)
theorem reorder_exec (n k : Nat) (map bits : BitString) :
    Exec reorder (ready n k map [] bits.reverse).store (4 * bits.length + 3)
      (ready n k map [] bits).store := by
  let before := ready n k map [] bits.reverse
  let prepared := {before with core := {before.core with core := {base (k + 1) [] with excess := bits.reverse}}}
  have header : Exec reverseHeader before.store 2 prepared.store := Exec.seq (.action _ _) (.action _ _)
  have core : Exec ClauseQuery.reverseLoop prepared.core.core.store (4 * bits.length + 1)
      (ready n k map [] bits).core.core.store := by
    simpa only [prepared, ready, idle, base, List.length_reverse,
      List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec (base (k + 1) []) bits.reverse
  have reversed := small_exec ClauseQuery.reverseLoop prepared _ _ core
  have cost : 4 * bits.length + 3 = 2 + (4 * bits.length + 1) := by omega
  simpa only [reorder, cost, before, prepared, ready, idle] using Exec.seq header reversed

def block : Block 18 := .seq loop reorder
def fuel {n : Nat} (F : Family n) (s : Space n) : Nat :=
  loopFuel s.parameters F + (4 * (matrixBits (polarRows F s)).length + 3)

theorem block_exec {n : Nat} (F : Family n) (s : Space n) :
    Exec block (ready n s.parameters (mapBits s.forms) (familyBits F) []).store
      (fuel F s) (ready n s.parameters (mapBits s.forms) [] (matrixBits (polarRows F s))).store := by
  have rows := loop_exec F s []
  rw [sourceRows_eq] at rows
  simp only [List.append_nil] at rows
  exact Exec.seq rows (reorder_exec n s.parameters (mapBits s.forms) (matrixBits (polarRows F s)))

theorem fuel_bound {n : Nat} (F : Family n) (s : Space n) :
    fuel F s ≤ (130 * (s.parameters + 2) * (n + 1) + 1) * F.length + 1 +
      (4 * ((n + 1) * (F.length * s.parameters)) + 3) := by
  unfold fuel
  rw [matrixBits_length, polarRows_length]
  exact Nat.add_le_add_right (loopFuel_bound s.parameters F) _

def program : Program 18 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (s : Space n) :
    BitRegister.run program (fuel F s + 1)
      ⟨.running 0, (ready n s.parameters (mapBits s.forms) (familyBits F) []).store⟩ =
      ⟨.accepted, (ready n s.parameters (mapBits s.forms) [] (matrixBits (polarRows F s))).store⟩ :=
  (block_exec F s).program_run 0 8

end PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions
