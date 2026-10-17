import PNP.Concrete.NormalizerBlockExecution
import PNP.Concrete.ResidualReduction.SourceReductionEncoding

/-! A finite coefficient-order routine. The executable block scans binary
digits directly; it never constructs the numeric coefficient rank. Its exact
register-instruction count is proved for all operand words. This is a routine
for the complete search implementation, not a complete solver/runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

def store (xs ys : BitString) (flag : Bool) : Store 3 :=
  .cons xs (.cons ys (.cons [flag] .nil))

def emit (flag : Bool) : Block 3 := .seq (.action (.clear 2)) (.action (.push 2 flag))

theorem emit_exec (xs ys : BitString) (before after : Bool) :
    Exec (emit after) (store xs ys before) 2 (store xs ys after) :=
  Exec.seq (.action _ _) (.action _ _)

def updateFlag : Bool → Bool → Bool → Bool
  | false, true, _ => true
  | true, false, _ => false
  | _, _, flag => flag

def bodyFuel : Bool → Bool → Nat
  | false, false | true, true => 5
  | _, _ => 6

def popPair : Block 3 := .seq (.action (.pop 0)) (.action (.pop 1))

theorem popPair_exec (xs ys : BitString) (flag : Bool) :
    Exec popPair (store xs ys flag) 2 (store xs.tail ys.tail flag) :=
  Exec.seq (.action _ _) (.action _ _)

def leftBody : Block 3 :=
  .seq (.branch 0 .skip
    (.branch 1 .skip .skip (emit true))
    (.branch 1 (emit false) (emit false) .skip)) popPair

def leftLoop : Block 3 := .loop 0 leftBody

theorem leftBody_exec (a : Bool) (xs ys : BitString) (flag : Bool) :
    Exec leftBody (store (a :: xs) ys flag) (bodyFuel a (ys.headD false))
      (store xs ys.tail (updateFlag a (ys.headD false) flag)) := by
  cases a with
  | false =>
    cases ys with
    | nil =>
      exact Exec.seq (.zero rfl (.empty rfl (.skip _))) (popPair_exec _ _ _)
    | cons b ys =>
      cases b with
      | false =>
        exact Exec.seq (.zero rfl (.zero rfl (.skip _))) (popPair_exec _ _ _)
      | true =>
        exact Exec.seq (.zero rfl (.one rfl (emit_exec _ _ _ true))) (popPair_exec _ _ _)
  | true =>
    cases ys with
    | nil =>
      exact Exec.seq (.one rfl (.empty rfl (emit_exec _ _ _ false))) (popPair_exec _ _ _)
    | cons b ys =>
      cases b with
      | false =>
        exact Exec.seq (.one rfl (.zero rfl (emit_exec _ _ _ false))) (popPair_exec _ _ _)
      | true =>
        exact Exec.seq (.one rfl (.one rfl (.skip _))) (popPair_exec _ _ _)

def leftResult : BitString → BitString → Bool → BitString × Bool
  | [], ys, flag => (ys, flag)
  | a :: xs, ys, flag => leftResult xs ys.tail (updateFlag a (ys.headD false) flag)

def leftFuel : BitString → BitString → Nat
  | [], _ => 1
  | a :: xs, ys => 1 + (bodyFuel a (ys.headD false) + leftFuel xs ys.tail)

theorem leftLoop_exec (xs ys : BitString) (flag : Bool) :
    Exec leftLoop (store xs ys flag) (leftFuel xs ys)
      (store [] (leftResult xs ys flag).1 (leftResult xs ys flag).2) := by
  induction xs generalizing ys flag with
  | nil => exact Exec.loopStop rfl
  | cons a xs ih =>
    exact Exec.loopStep rfl (leftBody_exec a xs ys flag)
      (ih ys.tail (updateFlag a (ys.headD false) flag))

theorem bodyFuel_bound (a b : Bool) : bodyFuel a b ≤ 6 := by
  cases a <;> cases b <;> decide

theorem leftFuel_bound (xs ys : BitString) : leftFuel xs ys ≤ 7 * xs.length + 1 := by
  induction xs generalizing ys with
  | nil => exact Nat.le_refl 1
  | cons a xs ih =>
    have body := bodyFuel_bound a (ys.headD false)
    have rest := ih ys.tail
    simp only [leftFuel, List.length_cons]
    omega

theorem leftResult_length (xs ys : BitString) (flag : Bool) :
    (leftResult xs ys flag).1.length ≤ ys.length := by
  induction xs generalizing ys flag with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    have rest := ih ys.tail (updateFlag a (ys.headD false) flag)
    have tail : ys.tail.length ≤ ys.length := by
      cases ys <;> simp only [List.tail, List.length_nil, List.length_cons] <;> omega
    exact Nat.le_trans rest tail

def rightBody : Block 3 :=
  .seq (.branch 1 .skip .skip (emit true)) (.action (.pop 1))
def rightLoop : Block 3 := .loop 1 rightBody

def rightBodyFuel : Bool → Nat
  | false => 3
  | true => 4

theorem rightBody_exec (b : Bool) (ys : BitString) (flag : Bool) :
    Exec rightBody (store [] (b :: ys) flag) (rightBodyFuel b)
      (store [] ys (updateFlag false b flag)) := by
  cases b with
  | false => exact Exec.seq (.zero rfl (.skip _)) (.action _ _)
  | true => exact Exec.seq (.one rfl (emit_exec _ _ _ true)) (.action _ _)

def rightResult : BitString → Bool → Bool
  | [], flag => flag
  | b :: ys, flag => rightResult ys (updateFlag false b flag)

def rightFuel : BitString → Nat
  | [] => 1
  | b :: ys => 1 + (rightBodyFuel b + rightFuel ys)

theorem rightLoop_exec (ys : BitString) (flag : Bool) :
    Exec rightLoop (store [] ys flag) (rightFuel ys) (store [] [] (rightResult ys flag)) := by
  induction ys generalizing flag with
  | nil => exact Exec.loopStop rfl
  | cons b ys ih =>
    exact Exec.loopStep rfl (rightBody_exec b ys flag) (ih (updateFlag false b flag))

theorem rightFuel_bound (ys : BitString) : rightFuel ys ≤ 5 * ys.length + 1 := by
  induction ys with
  | nil => exact Nat.le_refl 1
  | cons b ys ih =>
    have body : rightBodyFuel b ≤ 4 := by cases b <;> decide
    simp only [rightFuel, List.length_cons]
    omega

def compareCarry (xs ys : BitString) (flag : Bool) : Bool :=
  let r := leftResult xs ys flag
  rightResult r.1 r.2

/-- Numeric values occur only in the specification, not in the block code. -/
def bitValue : Bool → Nat
  | false => 0
  | true => 1

def binaryValue : BitString → Nat
  | [] => 0
  | b :: bs => bitValue b + 2 * binaryValue bs

def tieValue : Bool → Nat
  | false => 1
  | true => 0

theorem binaryValue_split (ys : BitString) :
    binaryValue ys = bitValue (ys.headD false) + 2 * binaryValue ys.tail := by
  cases ys <;> rfl

private theorem carry_step (a b flag : Bool) (x y : Nat) :
    decide (2 * x + tieValue (updateFlag a b flag) ≤ 2 * y) =
      decide (2 * (bitValue a + 2 * x) + tieValue flag ≤ 2 * (bitValue b + 2 * y)) := by
  cases a <;> cases b <;> cases flag <;> apply Bool.eq_iff_iff.mpr
  all_goals simp only [updateFlag, bitValue, tieValue, decide_eq_true_eq]
  all_goals constructor <;> intro h <;> omega

theorem rightResult_correct (ys : BitString) (flag : Bool) :
    rightResult ys flag = decide (tieValue flag ≤ 2 * binaryValue ys) := by
  induction ys generalizing flag with
  | nil => cases flag <;> rfl
  | cons b ys ih =>
    rw [rightResult, ih]
    cases b <;> cases flag <;> apply Bool.eq_iff_iff.mpr
    all_goals simp only [updateFlag, bitValue, tieValue, binaryValue, decide_eq_true_eq]
    all_goals constructor <;> intro h <;> omega

theorem carry_cons (a : Bool) (xs ys : BitString) (flag : Bool) :
    compareCarry (a :: xs) ys flag = compareCarry xs ys.tail (updateFlag a (ys.headD false) flag) := rfl

theorem carry_correct (xs ys : BitString) (flag : Bool) :
    compareCarry xs ys flag = decide (2 * binaryValue xs + tieValue flag ≤ 2 * binaryValue ys) := by
  induction xs generalizing ys flag with
  | nil =>
    simpa only [compareCarry, leftResult, binaryValue, Nat.mul_zero, Nat.zero_add] using
      rightResult_correct ys flag
  | cons a xs ih =>
    rw [carry_cons, ih]
    change decide (2 * binaryValue xs + tieValue (updateFlag a (ys.headD false) flag) ≤
      2 * binaryValue ys.tail) =
      decide (2 * (bitValue a + 2 * binaryValue xs) + tieValue flag ≤ 2 * binaryValue ys)
    rw [binaryValue_split ys]
    exact carry_step a (ys.headD false) flag (binaryValue xs) (binaryValue ys.tail)

theorem compare_correct (xs ys : BitString) :
    compareCarry xs ys true = decide (binaryValue xs ≤ binaryValue ys) := by
  rw [carry_correct]
  apply Bool.eq_iff_iff.mpr
  simp only [tieValue, decide_eq_true_eq]
  constructor <;> intro h <;> omega

def comparison : Block 3 := .seq (emit true) (.seq leftLoop rightLoop)
def fuel (xs ys : BitString) : Nat :=
  2 + (leftFuel xs ys + rightFuel (leftResult xs ys true).1)

theorem comparison_exec (xs ys : BitString) (initial : Bool) :
    Exec comparison (store xs ys initial) (fuel xs ys)
      (store [] [] (decide (binaryValue xs ≤ binaryValue ys))) := by
  have execution := Exec.seq (emit_exec xs ys initial true)
    (Exec.seq (leftLoop_exec xs ys true)
      (rightLoop_exec (leftResult xs ys true).1 (leftResult xs ys true).2))
  change Exec comparison (store xs ys initial) (fuel xs ys)
    (store [] [] (compareCarry xs ys true)) at execution
  rw [compare_correct] at execution
  exact execution

theorem fuel_bound (xs ys : BitString) : fuel xs ys ≤ 7 * (xs.length + ys.length) + 4 := by
  have left := leftFuel_bound xs ys
  have right := rightFuel_bound (leftResult xs ys true).1
  have remaining := leftResult_length xs ys true
  unfold fuel
  omega

def program : Program 3 := comparison.program 0 2

/-- Exact compiled finite instructions, starting with the two operand registers.
The enclosing source parser and the complete search must still be integrated. -/
theorem program_run (xs ys : BitString) (initial : Bool) :
    BitRegister.run program (fuel xs ys + 1) ⟨.running 0, store xs ys initial⟩ =
      ⟨.accepted, store [] [] (decide (binaryValue xs ≤ binaryValue ys))⟩ :=
  (comparison_exec xs ys initial).program_run 0 2

def normalBits : {n : Nat} → Affine n → BitString
  | 0, _ => []
  | _ + 1, (b, rest) => b :: normalBits rest

theorem normalBits_length {n : Nat} (a : Affine n) : (normalBits a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    exact congrArg Nat.succ (ih a)

theorem normalBits_encoded {n : Nat} (a : Affine n) :
    normalBits a = ((SourceEncoding.affineCodec n).encode a).take n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    change b :: normalBits a = b :: ((SourceEncoding.affineCodec n).encode a).take n
    rw [ih a]

theorem binaryValue_normalBits {n : Nat} (a : Affine n) :
    binaryValue (normalBits a) = normalCode a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    change bitValue b + 2 * binaryValue (normalBits a) =
      (if b then 1 else 0) + 2 * normalCode a
    rw [ih a]
    cases b <;> rfl

theorem normal_comparison_exec {n : Nat} (a b : Affine n) (initial : Bool) :
    Exec comparison (store (normalBits a) (normalBits b) initial)
      (fuel (normalBits a) (normalBits b))
      (store [] [] (decide (normalCode a ≤ normalCode b))) := by
  have execution := comparison_exec (normalBits a) (normalBits b) initial
  rw [binaryValue_normalBits, binaryValue_normalBits] at execution
  exact execution

theorem normal_fuel_bound {n : Nat} (a b : Affine n) :
    fuel (normalBits a) (normalBits b) ≤ 14 * n + 4 := by
  have bound := fuel_bound (normalBits a) (normalBits b)
  rw [normalBits_length, normalBits_length] at bound
  omega

end PNP.Concrete.ResidualReduction.CoefficientComparison
