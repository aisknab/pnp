import PNP.Concrete.NormalizerClausePack
import PNP.Concrete.ResidualReduction.SourceReductionEncoding

/-! Counted finite-word operations used by the complete matrix column pass.
The input prefix is read by literal bit instructions; neither an affine map nor
a row operation is a primitive machine callback. Existing registers and output
reversal are reused. These are source-instruction costs, not raw-machine costs. -/

namespace PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction

/-- Register 1 is the saved width, 2 the countdown, 3 the reverse accumulator,
4 the pivot, 5 its working copy, 6 the found flag, and 7 the saved matrix.
The existing reversal block moves register 3 into output register 8. -/
def dropBody : Block 9 := .seq (.action (.pop 0)) (.action (.pop 2))
def dropLoop : Block 9 := .loop 2 dropBody

theorem drop_exec (r : Registers) (front suffix : BitString) :
    Exec dropLoop
      ({r with input := front ++ suffix, remaining := List.replicate front.length true}).store
      (3 * front.length + 1)
      ({r with input := suffix, remaining := []}).store := by
  induction front generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
    have step : Exec dropBody
        ({r with input := (bit :: rest) ++ suffix, remaining := List.replicate (bit :: rest).length true}).store 2
        ({r with input := rest ++ suffix, remaining := List.replicate rest.length true}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step (ih r)
    have cost : 3 * (bit :: rest).length + 1 =
        1 + (2 + (3 * rest.length + 1)) := by
      simp only [List.length_cons]; omega
    simpa only [dropLoop, cost] using checked

def copyBody : Block 9 :=
  .seq (.branch 0 .skip (.action (.push 3 false)) (.action (.push 3 true)))
    dropBody
def copyLoop : Block 9 := .loop 2 copyBody

theorem copy_step (r : Registers) (bit tick : Bool) (rest ticks : BitString) :
    Exec copyBody ({r with input := bit :: rest, remaining := tick :: ticks}).store 4
      ({r with input := rest, remaining := ticks, excess := bit :: r.excess}).store := by
  cases bit
  · exact Exec.seq (Exec.zero rfl (.action _ _))
      (Exec.seq (.action _ _) (.action _ _))
  · exact Exec.seq (Exec.one rfl (.action _ _))
      (Exec.seq (.action _ _) (.action _ _))

theorem copy_exec (r : Registers) (front suffix : BitString) :
    Exec copyLoop
      ({r with input := front ++ suffix, remaining := List.replicate front.length true}).store
      (5 * front.length + 1)
      ({r with input := suffix, remaining := [], excess := front.reverse ++ r.excess}).store := by
  induction front generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
    have step := copy_step r bit true (rest ++ suffix) (List.replicate rest.length true)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step
      (ih {r with excess := bit :: r.excess})
    have cost : 5 * (bit :: rest).length + 1 =
        1 + (4 + (5 * rest.length + 1)) := by
      simp only [List.length_cons]; omega
    rw [cost]
    simpa only [copyLoop, List.length_cons, List.replicate_succ,
      List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append] using checked

def xorBody : Block 9 :=
  .seq (.branch 0 .skip
      (.branch 5 .skip (.action (.push 3 false)) (.action (.push 3 true)))
      (.branch 5 .skip (.action (.push 3 true)) (.action (.push 3 false))))
    (.seq (.action (.pop 5)) dropBody)
def xorLoop : Block 9 := .loop 2 xorBody

theorem xor_step (r : Registers) (bit other tick : Bool)
    (rest others ticks : BitString) :
    Exec xorBody
      ({r with input := bit :: rest, mode := other :: others, remaining := tick :: ticks}).store 6
      ({r with input := rest, mode := others, remaining := ticks, excess := Bool.xor bit other :: r.excess}).store := by
  cases bit <;> cases other
  · exact Exec.seq (Exec.zero rfl (Exec.zero rfl (.action _ _)))
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  · exact Exec.seq (Exec.zero rfl (Exec.one rfl (.action _ _)))
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  · exact Exec.seq (Exec.one rfl (Exec.zero rfl (.action _ _)))
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  · exact Exec.seq (Exec.one rfl (Exec.one rfl (.action _ _)))
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

theorem xor_exec (r : Registers) (front other suffix : BitString)
    (sameLength : front.length = other.length) :
    Exec xorLoop
      ({r with input := front ++ suffix, mode := other, remaining := List.replicate front.length true}).store
      (7 * front.length + 1)
      ({r with input := suffix, mode := [], remaining := [], excess := (List.zipWith Bool.xor front other).reverse ++ r.excess}).store := by
  induction front generalizing r other with
  | nil =>
    cases other with
    | nil => exact Exec.loopStop rfl
    | cons bit rest =>
      exfalso; simp only [List.length_nil, List.length_cons] at sameLength; omega
  | cons bit rest ih =>
    cases other with
    | nil =>
      exfalso; simp only [List.length_nil, List.length_cons] at sameLength; omega
    | cons head tail =>
      have lengths : rest.length = tail.length := by
        simp only [List.length_cons] at sameLength; omega
      have step := xor_step r bit head true (rest ++ suffix) tail
        (List.replicate rest.length true)
      have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step
        (ih {r with excess := Bool.xor bit head :: r.excess} tail lengths)
      have cost : 7 * (bit :: rest).length + 1 =
          1 + (6 + (7 * rest.length + 1)) := by
        simp only [List.length_cons]; omega
      rw [cost]
      simpa only [xorLoop, List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append] using checked

def affineWord {n : Nat} (a : Affine n) : BitString :=
  (SourceEncoding.affineCodec n).encode a

theorem affineWord_length {n : Nat} (a : Affine n) :
    (affineWord a).length = n + 1 := SourceEncoding.affine_length a

theorem affineWord_cons {n : Nat} (b : Bool) (a : Affine n) :
    affineWord (n := n + 1) (b, a) = b :: affineWord a := rfl

def matrixBits {n : Nat} : BinaryLinear.System n → BitString
  | [] => []
  | a :: rows => affineWord a ++ matrixBits rows

theorem matrixBits_length {n : Nat} (rows : BinaryLinear.System n) :
    (matrixBits rows).length = (n + 1) * rows.length := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    simp only [matrixBits, List.length_append, affineWord_length, ih,
      List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem substitute_false {n : Nat} (p a : Affine n) :
    affineWord (BinaryLinear.substitute p (false, a)) = affineWord a := by
  induction n with
  | zero => cases p <;> cases a <;> rfl
  | succ n ih =>
    rcases p with ⟨b, p⟩; rcases a with ⟨c, a⟩
    change (Bool.xor (false && b) c :: affineWord (aAdd (aScale false p) a)) =
      c :: affineWord a
    simpa only [BinaryLinear.substitute, Bool.false_and, Bool.false_xor] using congrArg (List.cons c) (ih p a)

theorem substitute_true {n : Nat} (p a : Affine n) :
    affineWord (BinaryLinear.substitute p (true, a)) =
      List.zipWith Bool.xor (affineWord a) (affineWord p) := by
  induction n with
  | zero => cases p <;> cases a <;> rfl
  | succ n ih =>
    rcases p with ⟨b, p⟩; rcases a with ⟨c, a⟩
    change Bool.xor (true && b) c :: affineWord (aAdd (aScale true p) a) =
      Bool.xor c b :: List.zipWith Bool.xor (affineWord a) (affineWord p)
    simpa only [BinaryLinear.substitute, Bool.true_and, Bool.xor_comm] using
      congrArg (List.cons (Bool.xor c b)) (ih p a)

end PNP.Concrete.ResidualReduction.MatrixInstructions
