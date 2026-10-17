import PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
import PNP.Concrete.ResidualReduction.SourcePolarPairInstructions

/-! Literal activity coefficients from two computed pullbacks. Both original
factor constants are read from the stored source words; then one finite loop
visits every coefficient pair. No activity bits or constants are supplied by
a semantic callback. The caller still has to compute the two pullbacks. -/

namespace PNP.Concrete.ResidualReduction.SourceActivityCoefficientInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarPairInstructions

def readInput (next : Bool → Block 17) : Block 17 :=
  .branch 0 .skip (.seq (.action (.pop 0)) (next false)) (.seq (.action (.pop 0)) (next true))
theorem readInput_exec (r : State) (b : Bool) (next : Bool → Block 17)
    (fuel : Nat) (after : State) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readInput next) ({r with core := {r.core with input := b :: r.core.input}}).store
      (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (0 : Fin 17)))
      ({r with core := {r.core with input := b :: r.core.input}}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (0 : Fin 17)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (0 : Fin 17)) rfl (Exec.seq popped checked)

def readConstant (source : Fin 17) (next : Bool → Block 17) : Block 17 :=
  .seq (.action (.copy 0 source)) <| .seq (.action (.copy 2 9)) <|
    .seq (lift dropLoop) (readInput next)
theorem readConstant_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (map output saved : BitString) (source : Fin 17) (a : Affine n)
    (word : (working width row f g map output saved).store.get source = affineWord a)
    (next : Bool → Block 17) (fuel : Nat) (after : State)
    (checked : Exec (next (aConstant a)) (working width row f g map output saved).store fuel after.store) :
    Exec (readConstant source next) (working width row f g map output saved).store
      (3 * n + 5 + fuel) after.store := by
  let before := working width row f g map output saved
  let copied := {before with core := {before.core with input := affineWord a}}
  let loaded := {copied with core := {copied.core with remaining := List.replicate n true}}
  let constant := {before with core := {before.core with input := [aConstant a]}}
  have copiedRaw : Exec (.action (.copy (0 : Fin 17) source)) before.store 1
      ({before with core := {before.core with input := before.store.get source}}).store := .action _ _
  have copy : Exec (.action (.copy (0 : Fin 17) source)) before.store 1 copied.store := by
    simpa only [before, word] using copiedRaw
  have count : Exec (.action (.copy (2 : Fin 17) 9)) copied.store 1 loaded.store := .action _ _
  have droppedCore : Exec dropLoop loaded.core.store (3 * n + 1) constant.core.store := by
    simpa only [loaded, copied, constant, before, working, base,
      normalWord_length, ← word_split] using
      drop_exec {base width [] with output := output} (normalWord a) [aConstant a]
  have dropped := lift_exec dropLoop loaded _ constant.core droppedCore
  have read := readInput_exec before (aConstant a) next fuel after checked
  have cost : 3 * n + 5 + fuel = 1 + (1 + ((3 * n + 1) + (2 + fuel))) := by omega
  simpa only [readConstant, cost, before, copied, loaded, constant] using
    Exec.seq copy (Exec.seq count (Exec.seq dropped read))

def emit (a0 b0 a b : Bool) : Block 17 :=
  .seq (.action (.push 8 (value a0 b0 a b))) (.action (.pop 14))
def body (a0 b0 : Bool) : Block 17 := readLeft fun a => readRight fun b => emit a0 b0 a b
theorem body_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (a0 b0 a b : Bool) (map output saved : BitString) :
    Exec (body a0 b0) (working (k := k + 1) width row (a, f) (b, g) map output saved).store 6
      (working width row f g map (value a0 b0 a b :: output) saved).store := by
  let tail := {working width row f g map output saved with pending := true :: List.replicate k true}
  have emitted : Exec (emit a0 b0 a b) tail.store 2
      (working width row f g map (value a0 b0 a b :: output) saved).store :=
    Exec.seq (.action _ _) (.action _ _)
  have checked := readLeft_exec {tail with rightCoefficients := b :: tail.rightCoefficients} a
    (fun x => readRight fun y => emit a0 b0 x y) _ _
    (readRight_exec tail b (fun y => emit a0 b0 a y) _ _ emitted)
  simpa only [body, tail, working, affineWord_cons, List.replicate_succ] using checked

def loop (a0 b0 : Bool) : Block 17 := .loop 14 (body a0 b0)
theorem loop_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (a0 b0 : Bool) (map output saved : BitString) :
    Exec (loop a0 b0) (working width row f g map output saved).store (7 * k + 1)
      (working (k := 0) width row (aConstant f) (aConstant g) map
        ((bits a0 b0 f g).reverse ++ output) saved).store := by
  induction k generalizing output with
  | zero => exact Exec.loopStop rfl
  | succ k ih =>
    rcases f with ⟨a, f⟩; rcases g with ⟨b, g⟩
    have first := body_exec width row f g a0 b0 a b map output saved
    have rest := ih f g (value a0 b0 a b :: output)
    have checked := Exec.loopStep (source := (14 : Fin 17)) rfl first rest
    have cost : 7 * (k + 1) + 1 = 1 + (6 + (7 * k + 1)) := by omega
    simpa only [loop, cost, bits, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, aConstant] using checked

def block : Block 17 := readConstant 10 fun a0 => readConstant 11 fun b0 => loop a0 b0
def fuel (n k : Nat) : Nat := 6 * n + 7 * k + 11
theorem block_exec {n k : Nat} (width : Nat) (row : Row n) (f g : Affine k)
    (map output saved : BitString) :
    Exec block (working width row f g map output saved).store (fuel n k)
      (working (k := 0) width row (aConstant f) (aConstant g) map
        ((bits (aConstant row.left) (aConstant row.right) f g).reverse ++ output) saved).store := by
  have sweep := loop_exec width row f g (aConstant row.left) (aConstant row.right) map output saved
  have right := readConstant_exec width row f g map output saved 11 row.right rfl
    (fun b0 => loop (aConstant row.left) b0) _ _ sweep
  have left := readConstant_exec width row f g map output saved 10 row.left rfl
    (fun a0 => readConstant 11 fun b0 => loop a0 b0) _ _ right
  have cost : fuel n k = 3 * n + 5 + (3 * n + 5 + (7 * k + 1)) := by unfold fuel; omega
  simpa only [block, cost] using left

end PNP.Concrete.ResidualReduction.SourceActivityCoefficientInstructions
