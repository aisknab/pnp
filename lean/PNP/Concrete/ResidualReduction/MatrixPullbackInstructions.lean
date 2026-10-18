import PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
import PNP.Concrete.ResidualReduction.MatrixPivotInstructions

/-! A fixed finite-register row scan for pivot reconstruction. Each coefficient
selects a counted skip or counted XOR of the corresponding complete map row.
The accumulated coefficients are computed by instructions, not supplied by a
caller. The affine constant is retained for the final one-bit operation. -/

namespace PNP.Concrete.ResidualReduction.MatrixPullbackInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

def selecting {n k : Nat} (p : Affine n) (m : AffineMap n k)
    (acc : Affine k) (saved : BitString) : Registers :=
  {base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := affineWord p}

def skip : Block 9 :=
  .seq (.action (.copy 2 1)) (.seq dropLoop (.action (.pop 6)))

theorem skip_exec {n k : Nat} (p : Affine n) (f : Affine k) (m : AffineMap n k)
    (acc : Affine k) (saved : BitString) :
    Exec skip (selecting (n := n + 1) (false, p) (f, m) acc saved).store
      (3 * (k + 1) + 3) (selecting p m acc saved).store := by
  have ready : Exec (.action (.copy 2 1))
      (selecting (n := n + 1) (false, p) (f, m) acc saved).store 1
      ({selecting (n := n + 1) (false, p) (f, m) acc saved with remaining := List.replicate (k + 1) true}).store :=
    .action _ _
  have dropped := drop_exec
    {base (k + 1) saved with sign := affineWord acc, active := false :: affineWord p}
    (affineWord f) (mapBits m)
  rw [affineWord_length] at dropped
  have finished : Exec (.action (.pop 6))
      ({base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := false :: affineWord p}).store 1
      (selecting p m acc saved).store := .action _ _
  have checked := Exec.seq ready (Exec.seq dropped finished)
  have cost : 3 * (k + 1) + 3 = 1 + ((3 * (k + 1) + 1) + 1) := by omega
  simpa only [skip, cost] using checked

def prepareAdd : Block 9 := .seq (.action (.copy 2 1)) (.action (.copy 5 4))
def finishAdd : Block 9 :=
  .seq (.action (.copy 4 8)) (.seq (.action (.clear 8)) (.action (.pop 6)))
def add : Block 9 :=
  .seq prepareAdd (.seq xorLoop (.seq ClauseQuery.reverseLoop finishAdd))

theorem add_exec {n k : Nat} (p : Affine n) (f : Affine k) (m : AffineMap n k)
    (acc : Affine k) (saved : BitString) :
    Exec add (selecting (n := n + 1) (true, p) (f, m) acc saved).store
      (11 * (k + 1) + 7) (selecting p m (aAdd f acc) saved).store := by
  have ready : Exec prepareAdd
      (selecting (n := n + 1) (true, p) (f, m) acc saved).store 2
      ({selecting (n := n + 1) (true, p) (f, m) acc saved with remaining := List.replicate (k + 1) true, mode := affineWord acc}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have xored : Exec xorLoop
      ({selecting (n := n + 1) (true, p) (f, m) acc saved with remaining := List.replicate (k + 1) true, mode := affineWord acc}).store
      (7 * (k + 1) + 1)
      ({base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := true :: affineWord p, excess := (affineWord (aAdd f acc)).reverse}).store := by
    simpa only [selecting, mapBits_cons, affineWord_cons, affineWord_length, base,
      word_add, List.append_nil] using
      xor_exec {base (k + 1) saved with sign := affineWord acc, active := true :: affineWord p}
        (affineWord f) (affineWord acc) (mapBits m)
        (by rw [affineWord_length, affineWord_length])
  have reversed : Exec ClauseQuery.reverseLoop
      ({base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := true :: affineWord p, excess := (affineWord (aAdd f acc)).reverse}).store
      (4 * (k + 1) + 1)
      ({base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := true :: affineWord p, output := affineWord (aAdd f acc)}).store := by
    simpa only [base, List.length_reverse, affineWord_length, List.reverse_reverse,
      List.append_nil] using
      ClauseQuery.reverse_exec
        {base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := true :: affineWord p}
        (affineWord (aAdd f acc)).reverse
  have finished : Exec finishAdd
      ({base (k + 1) saved with input := mapBits m, sign := affineWord acc, active := true :: affineWord p, output := affineWord (aAdd f acc)}).store 3
      (selecting p m (aAdd f acc) saved).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have checked := Exec.seq ready (Exec.seq xored (Exec.seq reversed finished))
  have cost : 11 * (k + 1) + 7 =
      2 + ((7 * (k + 1) + 1) + ((4 * (k + 1) + 1) + 3)) := by omega
  simpa only [add, cost] using checked

def body : Block 9 := .branch 6 .skip skip add
def loop : Block 9 := .loop 0 body

def fuel (k : Nat) : {n : Nat} → Affine n → Nat
  | 0, _ => 1
  | _ + 1, (false, p) => 3 * (k + 1) + 5 + fuel k p
  | _ + 1, (true, p) => 11 * (k + 1) + 9 + fuel k p

theorem loop_exec {n k : Nat} (p : Affine n) (m : AffineMap n k)
    (acc : Affine k) (saved : BitString) :
    Exec loop (selecting p m acc saved).store (fuel k p)
      ({base (k + 1) saved with sign := affineWord (selectedSum p m acc), active := [aConstant p]}).store := by
  induction n generalizing acc with
  | zero => cases m; exact Exec.loopStop rfl
  | succ n ih =>
    rcases p with ⟨b, p⟩; rcases m with ⟨f, m⟩
    obtain ⟨head, tail, word⟩ := affineWord_nonempty f
    have nonempty : (selecting (n := n + 1) (b, p) (f, m) acc saved).store.get 0 =
        head :: (tail ++ mapBits m) := by
      change affineWord f ++ mapBits m = _
      rw [word]
      rfl
    cases b with
    | false =>
      have step : Exec body (selecting (n := n + 1) (false, p) (f, m) acc saved).store
          (1 + (3 * (k + 1) + 3)) (selecting p m acc saved).store :=
        Exec.zero rfl (skip_exec p f m acc saved)
      have checked := Exec.loopStep nonempty step (ih p m acc)
      have cost : fuel k (n := n + 1) (false, p) =
          1 + ((1 + (3 * (k + 1) + 3)) + fuel k p) := by
        simp only [fuel]; omega
      rw [cost]
      simpa only [loop, selectedSum, Bool.false_eq_true, if_false, aConstant] using checked
    | true =>
      have step : Exec body (selecting (n := n + 1) (true, p) (f, m) acc saved).store
          (1 + (11 * (k + 1) + 7)) (selecting p m (aAdd f acc) saved).store :=
        Exec.one rfl (add_exec p f m acc saved)
      have checked := Exec.loopStep nonempty step (ih p m (aAdd f acc))
      have cost : fuel k (n := n + 1) (true, p) =
          1 + ((1 + (11 * (k + 1) + 7)) + fuel k p) := by
        simp only [fuel]; omega
      rw [cost]
      simpa only [loop, selectedSum, if_true, aConstant] using checked

theorem fuel_bound {n : Nat} (k : Nat) (p : Affine n) :
    fuel k p ≤ (11 * (k + 1) + 9) * n + 1 := by
  induction n with
  | zero => simp only [fuel, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | succ n ih =>
    rcases p with ⟨b, p⟩
    have bound := ih p
    simp only [Nat.mul_add, Nat.mul_one] at bound
    cases b <;> simp only [fuel, Nat.mul_add, Nat.mul_one] <;> omega

end PNP.Concrete.ResidualReduction.MatrixPullbackInstructions
