import PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions
import PNP.Concrete.ResidualReduction.MatrixPivotMapInstructions

/-! Consume both computed pullback coefficient words in lockstep and emit
every direction-constraint row. The loop is uniform in the parameter count;
neither the selected coefficients nor the emitted rows are supplied as proof
certificates. Its caller must construct the two pullbacks and their source map. -/

namespace PNP.Concrete.ResidualReduction.SourcePolarPairInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra

structure State where
  core : Registers
  width : BitString
  left : BitString
  right : BitString
  leftCoefficients : BitString
  rightCoefficients : BitString
  pending : BitString
  map : BitString
  savedOutput : BitString

def State.frame (r : State) : Store 8 := .cons r.width <| .cons r.left <| .cons r.right <|
  .cons r.leftCoefficients <| .cons r.rightCoefficients <| .cons r.pending <|
  .cons r.map (.cons r.savedOutput .nil)
def State.store (r : State) : Store 17 := Frame.join r.core.store r.frame
def lift (body : Block 9) : Block 17 := Frame.block 8 body
theorem lift_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame

def working {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (map output saved : BitString) : State :=
  ⟨{base width [] with output := output}, List.replicate n true,
    affineWord row.left, affineWord row.right, affineWord f, affineWord g,
    List.replicate k true, map, saved⟩

def readLeft (next : Bool → Block 17) : Block 17 :=
  .branch 12 .skip (.seq (.action (.pop 12)) (next false))
    (.seq (.action (.pop 12)) (next true))
theorem readLeft_exec (r : State) (b : Bool) (next : Bool → Block 17)
    (fuel : Nat) (after : State) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readLeft next) ({r with leftCoefficients := b :: r.leftCoefficients}).store
      (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (12 : Fin 17)))
      ({r with leftCoefficients := b :: r.leftCoefficients}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (12 : Fin 17)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (12 : Fin 17)) rfl (Exec.seq popped checked)

def readRight (next : Bool → Block 17) : Block 17 :=
  .branch 13 .skip (.seq (.action (.pop 13)) (next false))
    (.seq (.action (.pop 13)) (next true))
theorem readRight_exec (r : State) (b : Bool) (next : Bool → Block 17)
    (fuel : Nat) (after : State) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readRight next) ({r with rightCoefficients := b :: r.rightCoefficients}).store
      (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (13 : Fin 17)))
      ({r with rightCoefficients := b :: r.rightCoefficients}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (13 : Fin 17)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (13 : Fin 17)) rfl (Exec.seq popped checked)

def prepare : Block 17 := .seq (.action (.copy 0 10)) <|
  .seq (.action (.copy 5 11)) (.action (.copy 2 9))
def assemble (a b : Bool) : Block 17 := .seq prepare <|
  .seq (lift (MatrixLinearCombinationInstructions.block b a)) (.action (.pop 14))

theorem assemble_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (a b : Bool) (map output saved : BitString) :
    Exec (assemble a b)
      ({working width row f g map output saved with pending := true :: List.replicate k true}).store
      (7 * n + 8)
      (working width row f g map ((affineWord (combine b a row.left row.right)).reverse ++ output) saved).store := by
  let before := {working width row f g map output saved with pending := true :: List.replicate k true}
  let prepared := {before with core := {before.core with input := affineWord row.left, mode := affineWord row.right, remaining := List.replicate n true}}
  let combined := {before with core := {base width [] with output := (affineWord (combine b a row.left row.right)).reverse ++ output}}
  have seed : Exec prepare before.store 3 prepared.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have core : Exec (MatrixLinearCombinationInstructions.block b a) prepared.core.store
      (7 * n + 4) combined.core.store := by
    simpa only [before, prepared, combined, working, base, List.append_nil,
      MatrixLinearCombinationInstructions.fuel] using
      MatrixLinearCombinationInstructions.block_exec {base width [] with output := output}
        b a row.left row.right [] []
  have checked := lift_exec (MatrixLinearCombinationInstructions.block b a) prepared _ combined.core core
  have popped : Exec (.action (.pop (14 : Fin 17))) combined.store 1
      (working width row f g map ((affineWord (combine b a row.left row.right)).reverse ++ output) saved).store :=
    .action _ _
  have cost : 7 * n + 8 = 3 + ((7 * n + 4) + 1) := by omega
  simpa only [assemble, cost] using Exec.seq seed (Exec.seq checked popped)

def body : Block 17 := readLeft fun a => readRight fun b => assemble a b
theorem body_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (a b : Bool) (map output saved : BitString) :
    Exec body (working (k := k + 1) width row (a, f) (b, g) map output saved).store (7 * n + 12)
      (working width row f g map ((affineWord (combine b a row.left row.right)).reverse ++ output) saved).store := by
  let tail := {working width row f g map output saved with pending := true :: List.replicate k true}
  have checked := readLeft_exec {tail with rightCoefficients := b :: tail.rightCoefficients} a
    (fun x => readRight fun y => assemble x y) _ _
    (readRight_exec tail b (assemble a) _ _ (assemble_exec width row f g a b map output saved))
  have cost : 7 * n + 12 = 2 + (2 + (7 * n + 8)) := by omega
  simpa only [body, cost, tail, working, affineWord_cons, List.replicate_succ] using checked

def loop : Block 17 := .loop 14 body
def fuel (n k : Nat) : Nat := (7 * n + 13) * k + 1

theorem loop_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (map output saved : BitString) :
    Exec loop (working width row f g map output saved).store (fuel n k)
      (working (k := 0) width row (aConstant f) (aConstant g) map
        ((matrixBits (pairRows row f g)).reverse ++ output) saved).store := by
  induction k generalizing output with
  | zero => exact Exec.loopStop rfl
  | succ k ih =>
    rcases f with ⟨a, f⟩; rcases g with ⟨b, g⟩
    have first := body_exec width row f g a b map output saved
    have rest := ih f g ((affineWord (combine b a row.left row.right)).reverse ++ output)
    have checked := Exec.loopStep (source := (14 : Fin 17)) rfl first rest
    have cost : fuel n (k + 1) = 1 + ((7 * n + 12) + fuel n k) := by
      unfold fuel
      rw [Nat.mul_succ]
      omega
    simpa only [loop, cost, pairRows, matrixBits, List.reverse_append,
      List.append_assoc, aConstant] using checked

end PNP.Concrete.ResidualReduction.SourcePolarPairInstructions
