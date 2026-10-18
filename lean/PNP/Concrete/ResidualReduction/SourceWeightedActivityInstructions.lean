import PNP.Concrete.ResidualReduction.SourceActivityInstructions

/-! The weighted activity test reads every source row and its actual weight.
Both true and false weights take bounded literal branches. The accumulator
is updated by finite Boolean instructions, not a semantic evaluation oracle. -/

namespace PNP.Concrete.ResidualReduction.SourceWeightedActivityInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceActivityInstructions

structure State where
  core : MatrixReconstruction.State
  weights : BitString

def State.frame (r : State) : Store 1 := .cons r.weights .nil
def State.store (r : State) : Store 13 := Frame.join r.core.store r.frame
def lifted (body : Block 12) : Block 13 := Frame.block 1 body
theorem lifted_exec (body : Block 12) (r : State) (fuel : Nat) (after : MatrixReconstruction.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame

def withOutput (r : State) (output : BitString) : State :=
  {r with core := {r.core with core := {r.core.core with output := output}}}

def readWeight (next : Bool → Block 13) : Block 13 :=
  .branch 12 .skip (.seq (.action (.pop 12)) (next false))
    (.seq (.action (.pop 12)) (next true))
theorem readWeight_exec (r : State) (b : Bool) (next : Bool → Block 13)
    (fuel : Nat) (after : State) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readWeight next) ({r with weights := b :: r.weights}).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (12 : Fin 13)))
      ({r with weights := b :: r.weights}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (12 : Fin 13)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (12 : Fin 13)) rfl (Exec.seq popped checked)

def readOutput (next : Bool → Block 13) : Block 13 :=
  .branch 8 .skip (.seq (.action (.pop 8)) (next false))
    (.seq (.action (.pop 8)) (next true))
theorem readOutput_exec (r : State) (b : Bool) (next : Bool → Block 13)
    (fuel : Nat) (after : State) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readOutput next) (withOutput r (b :: r.core.core.output)).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (8 : Fin 13)))
      (withOutput r (b :: r.core.core.output)).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (8 : Fin 13)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (8 : Fin 13)) rfl (Exec.seq popped checked)

def absorb : Block 13 :=
  readWeight fun w => readOutput fun a => readOutput fun c =>
    .action (.push 8 (Bool.xor (w && a) c))
theorem absorb_exec (r : State) (w a c : Bool) :
    Exec absorb (withOutput {r with weights := w :: r.weights} (a :: c :: r.core.core.output)).store 7
      (withOutput r (Bool.xor (w && a) c :: r.core.core.output)).store := by
  unfold absorb
  refine readWeight_exec (withOutput r (a :: c :: r.core.core.output)) w _ 5 _ ?_
  refine readOutput_exec (withOutput r (c :: r.core.core.output)) a _ 3 _ ?_
  refine readOutput_exec r c _ 1 _ ?_
  exact .action _ _

def ready (n j : Nat) (input weights output : BitString) : State :=
  ⟨SourcePolarInstructions.working n j n [] input [] output, weights⟩
def rowStep : Block 13 := .seq (lifted rowBlock) absorb

theorem rowStep_exec {n : Nat} (row : Row n) (j : Fin n) (b acc : Bool)
    (suffix weights output : BitString) :
    Exec rowStep (ready n j.val (rowWord row ++ suffix) (b :: weights) (acc :: output)).store
      (rowFuel n j.val + 7)
      (ready n j.val suffix weights (Bool.xor (b && activity row (unitPoint n j)) acc :: output)).store := by
  let before := ready n j.val (rowWord row ++ suffix) (b :: weights) (acc :: output)
  let middle := ready n j.val suffix (b :: weights) (activity row (unitPoint n j) :: acc :: output)
  have evaluated : Exec (lifted rowBlock) before.store (rowFuel n j.val) middle.store :=
    lifted_exec rowBlock before _ middle.core (rowBlock_exec row j suffix [] (acc :: output))
  have folded : Exec absorb middle.store 7
      (ready n j.val suffix weights (Bool.xor (b && activity row (unitPoint n j)) acc :: output)).store :=
    absorb_exec (ready n j.val suffix weights output) b (activity row (unitPoint n j)) acc
  exact Exec.seq evaluated folded

def loop : Block 13 := .loop 0 rowStep
def fuel (n j rows : Nat) : Nat := (rowFuel n j + 8) * rows + 1

private theorem xor_fold (a b c : Bool) : Bool.xor b (Bool.xor a c) = Bool.xor (Bool.xor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem point_encode_cons {m : Nat} (b : Bool) (w : Point m) :
    (SourceEncoding.pointCodec (m + 1)).encode (b, w) =
      b :: (SourceEncoding.pointCodec m).encode w := rfl

theorem loop_exec {n : Nat} (F : Family n) (w : Point F.length) (j : Fin n)
    (suffix : BitString) (acc : Bool) (output : BitString) :
    Exec loop
      (ready n j.val (familyBits F) ((SourceEncoding.pointCodec F.length).encode w ++ suffix) (acc :: output)).store
      (fuel n j.val F.length)
      (ready n j.val [] suffix (Bool.xor (weightedActivity F w (unitPoint n j)) acc :: output)).store := by
  induction F generalizing acc with
  | nil =>
    simp only [weightedActivity, Bool.false_xor]
    exact Exec.loopStop rfl
  | cons row F ih =>
    rcases w with ⟨b, w⟩
    let remaining := (SourceEncoding.pointCodec F.length).encode w ++ suffix
    have first := rowStep_exec row j b acc (familyBits F) remaining output
    have rest := ih w (Bool.xor (b && activity row (unitPoint n j)) acc)
    have checked := Exec.loopStep (source := (0 : Fin 13)) rfl first rest
    have cost : fuel n j.val (F.length + 1) =
        1 + ((rowFuel n j.val + 7) + fuel n j.val F.length) := by
      simp only [fuel, Nat.mul_add, Nat.mul_one]; omega
    simpa only [loop, cost, familyBits, weightedActivity, xor_fold, remaining,
      List.length_cons, point_encode_cons, List.cons_append] using checked

theorem fuel_bound {n : Nat} (F : Family n) (j : Fin n) :
    fuel n j.val F.length ≤ (24 * n + 69) * F.length + 1 := by
  have one := rowFuel_bound j
  have all := Nat.mul_le_mul_right F.length (show rowFuel n j.val + 8 ≤ 24 * n + 69 by omega)
  unfold fuel
  omega

/-- The outer caller provides actual encoded weights, not an activity or
coverage certificate. Their construction is a separate, charged phase. -/
def test : Block 13 := .seq (.action (.push 8 false)) loop
theorem test_exec {n : Nat} (F : Family n) (w : Point F.length) (j : Fin n) (output : BitString) :
    Exec test (ready n j.val (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) output).store
      (fuel n j.val F.length + 1)
      (ready n j.val [] [] (weightedActivity F w (unitPoint n j) :: output)).store := by
  have seed : Exec (.action (.push (8 : Fin 13) false))
      (ready n j.val (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) output).store 1
      (ready n j.val (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) (false :: output)).store := .action _ _
  have body := loop_exec F w j [] false output
  simp only [List.append_nil, Bool.xor_false] at body
  have cost : fuel n j.val F.length + 1 = 1 + fuel n j.val F.length := by omega
  simpa only [test, cost, List.append_nil, Bool.xor_false] using Exec.seq seed body

end PNP.Concrete.ResidualReduction.SourceWeightedActivityInstructions
