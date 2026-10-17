import PNP.Concrete.ResidualReduction.SourcePolarInstructions

/-! Literal activity evaluation from an original source row. The two linear
coefficients and both affine constants are read by finite-word instructions.
This is the inner test used by the ordered affine-witness search; it does not
claim that the complete search or contraction loop has a runtime bound. -/

namespace PNP.Concrete.ResidualReduction.SourceActivityInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceCoefficientInstructions
open PNP.Concrete.ResidualReduction.SourcePolarInstructions
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections

theorem constant_bit {n : Nat} (a : Affine n) : bitAt (affineWord a) n = aConstant a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    simpa only [affineWord_cons, bitAt, aConstant] using ih a

theorem eval_unit_value {n : Nat} (a : Affine n) (j : Fin n) :
    aEval a (unitPoint n j) = Bool.xor (bitAt (affineWord a) j.val) (aConstant a) := by
  have h := congrArg (fun b => Bool.xor b (aConstant a)) (eval_unit_coefficient a j)
  simpa only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] using h

def activityBit {n : Nat} (r : Row n) (j : Nat) : Bool :=
  Bool.xor
    (Bool.xor (bitAt (affineWord r.left) j) (bitAt (affineWord r.left) n) &&
      Bool.xor (bitAt (affineWord r.right) j) (bitAt (affineWord r.right) n))
    (bitAt (affineWord r.left) n && bitAt (affineWord r.right) n)

theorem activity_units {n : Nat} (r : Row n) (j : Fin n) :
    activity r (unitPoint n j) = activityBit r j.val := by
  simp only [activity, Row.eval, eval_zero_constant, activityBit, constant_bit,
    eval_unit_value]

theorem left_source_field {n : Nat} (r : Row n) (suffix : BitString) (k : Nat) (bound : k ≤ n) :
    bitAt ((rowWord r ++ suffix).tail) k = bitAt (affineWord r.left) k := by
  change bitAt ((affineWord r.left ++ affineWord r.right) ++ suffix) k = _
  rw [List.append_assoc]
  exact bitAt_append _ _ _ (by rw [affineWord_length]; omega)

theorem right_source_field {n : Nat} (r : Row n) (suffix : BitString) (k : Nat) (bound : k ≤ n) :
    bitAt (((rowWord r ++ suffix).tail).drop (n + 1)) k = bitAt (affineWord r.right) k := by
  rw [right_source_tail]
  exact bitAt_append _ _ _ (by rw [affineWord_length]; omega)

def emitActivity : Block 9 :=
  readBit fun d => readBit fun c => readBit fun b => readBit fun a =>
    .action (.push 8 (Bool.xor (Bool.xor a b && Bool.xor c d) (b && d)))

theorem emitActivity_exec (r : Registers) (a b c d : Bool) :
    Exec emitActivity ({r with excess := d :: c :: b :: a :: r.excess}).store 9
      ({r with output := Bool.xor (Bool.xor a b && Bool.xor c d) (b && d) :: r.output}).store := by
  unfold emitActivity
  refine readBit_exec {r with excess := c :: b :: a :: r.excess} d _ 7 _ ?_
  refine readBit_exec {r with excess := b :: a :: r.excess} c _ 5 _ ?_
  refine readBit_exec {r with excess := a :: r.excess} b _ 3 _ ?_
  refine readBit_exec r a _ 1 _ ?_
  exact .action _ _

def evaluate : Block 12 := .seq (readLeft false) <| .seq (readLeft true) <|
  .seq (readRight false) <| .seq (readRight true) (lift emitActivity)

theorem evaluate_exec {n : Nat} (row : Row n) (j : Fin n)
    (input suffix stack output : BitString) :
    Exec evaluate (working n j.val n (rowWord row ++ suffix) input stack output).store
      (6 * j.val + 6 * n + 6 * (n + 1) + 39)
      (working n j.val n (rowWord row ++ suffix)
        ((((rowWord row ++ suffix).tail).drop (n + 1)).drop n)
        stack (activityBit row j.val :: output)).store := by
  let r0 := working n j.val n (rowWord row ++ suffix) input stack output
  let r1 := readAfter (leftReady r0) j.val
  let r2 := readAfter (leftReady r1) n
  let r3 := readAfter (rightReady r2 n) j.val
  let r4 := readAfter (rightReady r3 n) n
  have first : Exec (readLeft false) r0.store (3 * j.val + 6) r1.store :=
    readLeft_exec r0 false j.val rfl
  have second : Exec (readLeft true) r1.store (3 * n + 6) r2.store :=
    readLeft_exec r1 true n rfl
  have third : Exec (readRight false) r2.store (3 * (n + 1) + 3 * j.val + 9) r3.store :=
    readRight_exec r2 false n j.val rfl rfl
  have fourth : Exec (readRight true) r3.store (3 * (n + 1) + 3 * n + 9) r4.store :=
    readRight_exec r3 true n n rfl rfl
  let tail := (((rowWord row ++ suffix).tail).drop (n + 1)).drop n
  let done := working n j.val n (rowWord row ++ suffix) tail stack (activityBit row j.val :: output)
  have finish : Exec (lift emitActivity) r4.store 9 done.store := by
    let before := working n j.val n (rowWord row ++ suffix) tail stack output
    have core := emitActivity_exec before.core (bitAt (affineWord row.left) j.val)
      (bitAt (affineWord row.left) n) (bitAt (affineWord row.right) j.val)
      (bitAt (affineWord row.right) n)
    have lifted := lift_exec emitActivity
      {before with core := {before.core with excess := (bitAt (affineWord row.right) n :: bitAt (affineWord row.right) j.val :: bitAt (affineWord row.left) n :: bitAt (affineWord row.left) j.val :: stack)}}
      9 done.core core
    simpa only [r4, r3, r2, r1, r0, before, done, tail, readAfter, leftReady, rightReady,
      skipped, working, base, left_source_field row suffix j.val (Nat.le_of_lt j.isLt),
      left_source_field row suffix n (Nat.le_refl n),
      right_source_field row suffix j.val (Nat.le_of_lt j.isLt),
      right_source_field row suffix n (Nat.le_refl n), activityBit] using lifted
  have cost : 6 * j.val + 6 * n + 6 * (n + 1) + 39 =
      (3 * j.val + 6) + ((3 * n + 6) +
        ((3 * (n + 1) + 3 * j.val + 9) + ((3 * (n + 1) + 3 * n + 9) + 9))) := by omega
  simpa only [evaluate, cost] using
    Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth finish)))

def rowBlock : Block 12 := .seq (.action (.copy 7 0)) (.seq evaluate SourcePolarInstructions.advance)
def rowFuel (n j : Nat) : Nat := 6 * j + 6 * n + 12 * (n + 1) + 49

theorem rowBlock_exec {n : Nat} (row : Row n) (j : Fin n) (suffix stack output : BitString) :
    Exec rowBlock (working n j.val n [] (rowWord row ++ suffix) stack output).store
      (rowFuel n j.val)
      (working n j.val n [] suffix stack (activity row (unitPoint n j) :: output)).store := by
  let saved := working n j.val n (rowWord row ++ suffix) (rowWord row ++ suffix) stack output
  have save : Exec (.action (.copy (7 : Fin 12) 0))
      (working n j.val n [] (rowWord row ++ suffix) stack output).store 1 saved.store := .action _ _
  let emitted := working n j.val n (rowWord row ++ suffix)
    ((((rowWord row ++ suffix).tail).drop (n + 1)).drop n) stack (activityBit row j.val :: output)
  have finish : Exec SourcePolarInstructions.advance emitted.store (6 * (n + 1) + 9)
      (working n j.val n [] suffix stack (activityBit row j.val :: output)).store := by
    simpa only [advanced, skipped, rightReady, leftReady, emitted, working, base, source_end] using
      advance_exec emitted n rfl
  have cost : rowFuel n j.val =
      1 + ((6 * j.val + 6 * n + 6 * (n + 1) + 39) + (6 * (n + 1) + 9)) := by
    unfold rowFuel; omega
  rw [activity_units]
  simpa only [rowBlock, cost] using Exec.seq save
    (Exec.seq (evaluate_exec row j (rowWord row ++ suffix) suffix stack output) finish)

theorem rowFuel_bound {n : Nat} (j : Fin n) : rowFuel n j.val ≤ 24 * n + 61 := by
  unfold rowFuel
  omega

end PNP.Concrete.ResidualReduction.SourceActivityInstructions
