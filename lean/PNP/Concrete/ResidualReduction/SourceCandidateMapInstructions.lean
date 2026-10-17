import PNP.Concrete.ResidualReduction.SourceActivityInstructions
import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

/-! Literal zero/unit evaluation of the encoded affine solution map. Both
the coefficient and its affine constant are charged reads, and every map
coordinate is consumed. These are the exact candidates of affineTestPairs,
not arbitrary caller-supplied candidate weights. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceCoefficientInstructions
open PNP.Concrete.ResidualReduction.SourcePolarInstructions
open PNP.Concrete.ResidualReduction.SourceActivityInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def parameter {k : Nat} : Option (Fin k) → Point k
  | none => zeroPoint k
  | some j => unitPoint k j
def cursor {k : Nat} : Option (Fin k) → Nat
  | none => 0
  | some j => j.val
def marker {k : Nat} : Option (Fin k) → Nat
  | none => 0
  | some _ => 1
def selectedIndex {k : Nat} : Option (Fin k) → Nat
  | none => k
  | some j => j.val
def ready (k : Nat) (q : Option (Fin k)) (saved input stack output : BitString) : State :=
  working k (cursor q) (marker q) saved input stack output

theorem source_field {k : Nat} (a : Affine k) (suffix : BitString) (i : Nat) (bound : i ≤ k) :
    bitAt (affineWord a ++ suffix) i = bitAt (affineWord a) i :=
  bitAt_append _ _ _ (by rw [affineWord_length]; omega)

def emitHead : Block 9 := readBit fun b => .action (.push 8 b)
theorem emitHead_exec (r : Registers) (b : Bool) :
    Exec emitHead ({r with excess := b :: r.excess}).store 3
      ({r with output := b :: r.output}).store := by
  exact readBit_exec r b _ 1 _ (.action _ _)
def emitXor : Block 9 := readBit fun b => readBit fun c => .action (.push 8 (Bool.xor b c))
theorem emitXor_exec (r : Registers) (b c : Bool) :
    Exec emitXor ({r with excess := b :: c :: r.excess}).store 5
      ({r with output := Bool.xor b c :: r.output}).store := by
  refine readBit_exec {r with excess := c :: r.excess} b _ 3 _ ?_
  exact readBit_exec r c _ 1 _ (.action _ _)

def constantRead : Block 12 := .seq (.action (.copy 2 9)) (lift read)
theorem constantRead_exec (k : Nat) (q : Option (Fin k)) (saved input stack output : BitString) :
    Exec constantRead (ready k q saved input stack output).store (3 * k + 4)
      (ready k q saved (input.drop k) (bitAt input k :: stack) output).store := by
  let r := ready k q saved input stack output
  let prepared : State := {r with core := {r.core with remaining := List.replicate k true}}
  let after := ready k q saved (input.drop k) (bitAt input k :: stack) output
  have copied : Exec (.action (.copy (2 : Fin 12) 9)) r.store 1 prepared.store := .action _ _
  have body : Exec (lift read) prepared.store (3 * k + 3) after.store :=
    lift_exec read prepared _ after.core (read_exec r.core k)
  have cost : 3 * k + 4 = 1 + (3 * k + 3) := by omega
  simpa only [constantRead, cost] using Exec.seq copied body

def seed : Block 12 := .seq (.action (.copy 7 0)) constantRead
theorem seed_exec {k : Nat} (a : Affine k) (q : Option (Fin k)) (suffix stack output : BitString) :
    Exec seed (ready k q [] (affineWord a ++ suffix) stack output).store (3 * k + 5)
      (ready k q (affineWord a ++ suffix) ((affineWord a ++ suffix).drop k)
        (aConstant a :: stack) output).store := by
  have saved : Exec (.action (.copy (7 : Fin 12) 0))
      (ready k q [] (affineWord a ++ suffix) stack output).store 1
      (ready k q (affineWord a ++ suffix) (affineWord a ++ suffix) stack output).store := .action _ _
  have read := constantRead_exec k q (affineWord a ++ suffix) (affineWord a ++ suffix) stack output
  have cost : 3 * k + 5 = 1 + (3 * k + 4) := by omega
  simpa only [seed, cost, source_field a suffix k (Nat.le_refl k), constant_bit] using Exec.seq saved read

def unitRead : Block 12 := .seq (.action (.copy 0 7)) (.seq (readCurrent false) (lift emitXor))
def select : Block 12 := .branch 11 (lift emitHead) (lift emitHead) unitRead
def selectFuel {k : Nat} : Option (Fin k) → Nat
  | none => 4
  | some j => 3 * j.val + 11

theorem select_exec {k : Nat} (a : Affine k) (q : Option (Fin k)) (suffix stack output : BitString) :
    Exec select
      (ready k q (affineWord a ++ suffix) ((affineWord a ++ suffix).drop k) (aConstant a :: stack) output).store
      (selectFuel q)
      (ready k q (affineWord a ++ suffix) ((affineWord a ++ suffix).drop (selectedIndex q))
        stack (aEval a (parameter q) :: output)).store := by
  cases q with
  | none =>
    let r := ready k none (affineWord a ++ suffix) ((affineWord a ++ suffix).drop k) stack output
    have body := lift_exec emitHead {r with core := {r.core with excess := aConstant a :: stack}} 3
      ({r.core with output := aConstant a :: output}) (emitHead_exec r.core (aConstant a))
    simpa only [select, selectFuel, parameter, selectedIndex, eval_zero_constant, r, ready, working, base] using
      (Exec.empty (source := (11 : Fin 12)) rfl body)
  | some j =>
    let r0 := ready k (some j) (affineWord a ++ suffix) ((affineWord a ++ suffix).drop k) (aConstant a :: stack) output
    let r1 := ready k (some j) (affineWord a ++ suffix) (affineWord a ++ suffix) (aConstant a :: stack) output
    let r2 := readAfter r1 j.val
    let r3 := ready k (some j) (affineWord a ++ suffix) ((affineWord a ++ suffix).drop j.val) stack output
    have copied : Exec (.action (.copy (0 : Fin 12) 7)) r0.store 1 r1.store := .action _ _
    have scanned : Exec (readCurrent false) r1.store (3 * j.val + 4) r2.store :=
      readCurrent_exec r1 false j.val rfl
    have emitted : Exec (lift emitXor) r2.store 5
        ({r3 with core := {r3.core with output := aEval a (unitPoint k j) :: output}}).store := by
      have checked := lift_exec emitXor
        {r3 with core := {r3.core with excess := (bitAt (affineWord a) j.val :: aConstant a :: stack)}}
        5 ({r3.core with output := Bool.xor (bitAt (affineWord a) j.val) (aConstant a) :: output})
        (emitXor_exec r3.core (bitAt (affineWord a) j.val) (aConstant a))
      simpa only [r2, r1, r3, ready, readAfter, working, base,
        source_field a suffix j.val (Nat.le_of_lt j.isLt), eval_unit_value] using checked
    have cost : selectFuel (some j) = 1 + (1 + ((3 * j.val + 4) + 5)) := by
      simp only [selectFuel]; omega
    simpa only [select, unitRead, cost, selectedIndex, parameter, r0, r3, ready, working, base] using
      (Exec.one (source := (11 : Fin 12)) rfl (Exec.seq copied (Exec.seq scanned emitted)))

def advance : Block 12 := .seq (.action (.copy 0 7)) (.seq skipFactor (.action (.clear 7)))
theorem advance_exec {k : Nat} (a : Affine k) (q : Option (Fin k)) (input suffix stack output : BitString) :
    Exec advance (ready k q (affineWord a ++ suffix) input stack output).store (3 * (k + 1) + 5)
      (ready k q [] suffix stack output).store := by
  let r := ready k q (affineWord a ++ suffix) (affineWord a ++ suffix) stack output
  have copied : Exec (.action (.copy (0 : Fin 12) 7))
      (ready k q (affineWord a ++ suffix) input stack output).store 1 r.store := .action _ _
  have skipped := skipFactor_exec r k rfl
  have cleared : Exec (.action (.clear (7 : Fin 12))) (SourcePolarInstructions.skipped r k).store 1
      (ready k q [] ((affineWord a ++ suffix).drop (k + 1)) stack output).store := .action _ _
  have tail : (affineWord a ++ suffix).drop (k + 1) = suffix := by
    rw [← affineWord_length a, List.drop_left]
  have cost : 3 * (k + 1) + 5 = 1 + ((3 * (k + 1) + 3) + 1) := by omega
  simpa only [advance, cost, tail] using Exec.seq copied (Exec.seq skipped cleared)

def rowBlock : Block 12 := .seq seed (.seq select advance)
def rowFuel (k : Nat) (q : Option (Fin k)) : Nat := (3 * k + 5) + (selectFuel q + (3 * (k + 1) + 5))
theorem rowBlock_exec {k : Nat} (a : Affine k) (q : Option (Fin k)) (suffix stack output : BitString) :
    Exec rowBlock (ready k q [] (affineWord a ++ suffix) stack output).store (rowFuel k q)
      (ready k q [] suffix stack (aEval a (parameter q) :: output)).store := by
  exact Exec.seq (seed_exec a q suffix stack output)
    (Exec.seq (select_exec a q suffix stack output)
      (advance_exec a q _ suffix stack (aEval a (parameter q) :: output)))

theorem rowFuel_bound (k : Nat) (q : Option (Fin k)) : rowFuel k q ≤ 9 * k + 24 := by
  cases q with
  | none => simp only [rowFuel, selectFuel]; omega
  | some j => simp only [rowFuel, selectFuel]; omega

end PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions
