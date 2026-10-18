import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
import PNP.Concrete.ResidualReduction.MatrixPivotInstructions

/-! Literal construction of the free-variable branch of the exact affine
solution map. Every existing row is read and extended, and the new independent
form is built bit by bit. The map constructor is finite instruction code with
an explicit unbounded source cost. Register copies are source instructions;
their word-level costs are accounted for by the separate literal compiler. -/

namespace PNP.Concrete.ResidualReduction.MatrixFreeInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def raising {n k : Nat} (m : AffineMap n k) (saved acc : BitString) : Registers :=
  {base (k + 1) saved with input := mapBits m, excess := acc}

def prepareRaisedRow : Block 9 :=
  .seq (.action (.copy 2 1)) (.action (.push 3 false))
def copyRaisedRow : Block 9 := .seq prepareRaisedRow copyLoop
def raisingLoop : Block 9 := .loop 0 copyRaisedRow

theorem copyRaisedRow_exec {n k : Nat} (f : Affine k) (m : AffineMap n k)
    (saved acc : BitString) :
    Exec copyRaisedRow (raising (n := n + 1) (f, m) saved acc).store
      (5 * (k + 1) + 3)
      (raising m saved ((false :: affineWord f).reverse ++ acc)).store := by
  have ready : Exec prepareRaisedRow (raising (n := n + 1) (f, m) saved acc).store 2
      ({base (k + 1) saved with input := affineWord f ++ mapBits m, remaining := List.replicate (k + 1) true, excess := false :: acc}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have copied := copy_exec {base (k + 1) saved with excess := false :: acc}
    (affineWord f) (mapBits m)
  rw [affineWord_length] at copied
  have checked := Exec.seq ready copied
  have cost : 5 * (k + 1) + 3 = 2 + (5 * (k + 1) + 1) := by omega
  rw [cost]
  simpa only [copyRaisedRow, raising, base, List.reverse_cons,
    List.append_assoc, List.cons_append, List.nil_append] using checked

theorem raisingLoop_exec {n k : Nat} (m : AffineMap n k) (saved acc : BitString) :
    Exec raisingLoop (raising m saved acc).store
      ((5 * (k + 1) + 4) * n + 1)
      ({base (k + 1) saved with excess := (mapBits (raiseMap m)).reverse ++ acc}).store := by
  induction n generalizing acc with
  | zero => cases m; exact Exec.loopStop rfl
  | succ n ih =>
    rcases m with ⟨f, m⟩
    obtain ⟨b, rest, word⟩ := affineWord_nonempty f
    have nonempty : (raising (n := n + 1) (f, m) saved acc).store.get 0 =
        b :: (rest ++ mapBits m) := by
      change affineWord f ++ mapBits m = _
      rw [word]
      rfl
    have checked := Exec.loopStep nonempty (copyRaisedRow_exec f m saved acc)
      (ih m ((false :: affineWord f).reverse ++ acc))
    have cost : (5 * (k + 1) + 4) * (n + 1) + 1 =
        1 + ((5 * (k + 1) + 3) + ((5 * (k + 1) + 4) * n + 1)) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    rw [cost]
    simpa only [raisingLoop, raised_cons, List.reverse_append, List.append_assoc] using checked

def zeroPrefixBody : Block 9 := .seq (.action (.push 8 false)) (.action (.pop 2))
def zeroPrefixLoop : Block 9 := .loop 2 zeroPrefixBody
private theorem replicate_snoc (width : Nat) (bit : Bool) (output : BitString) :
    List.replicate width bit ++ bit :: output =
      List.replicate (width + 1) bit ++ output := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simpa only [List.replicate_succ, List.cons_append] using
      congrArg (List.cons bit) ih


theorem zeroPrefix_exec (r : Registers) (width : Nat) :
    Exec zeroPrefixLoop ({r with remaining := List.replicate width true}).store
      (3 * width + 1)
      ({r with remaining := [], output := List.replicate width false ++ r.output}).store := by
  induction width generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ width ih =>
    have step : Exec zeroPrefixBody
        ({r with remaining := List.replicate (width + 1) true}).store 2
        ({r with remaining := List.replicate width true, output := false :: r.output}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step
      (ih {r with output := false :: r.output})
    have word := replicate_snoc width false r.output
    have cost : 3 * (width + 1) + 1 = 1 + (2 + (3 * width + 1)) := by omega
    rw [cost]
    simpa only [zeroPrefixLoop, word] using checked

def finish : Block 9 :=
  .seq (.action (.copy 2 1)) <| .seq zeroPrefixLoop <|
    .seq (.action (.push 8 true)) (.action (.push 1 true))

theorem finish_exec (k : Nat) (saved output : BitString) :
    Exec finish ({base (k + 1) saved with output := output}).store (3 * (k + 1) + 4)
      ({base (k + 2) saved with output := (true :: List.replicate (k + 1) false) ++ output}).store := by
  have ready : Exec (.action (.copy 2 1))
      ({base (k + 1) saved with output := output}).store 1
      ({base (k + 1) saved with remaining := List.replicate (k + 1) true, output := output}).store :=
    .action _ _
  have zeroed := zeroPrefix_exec {base (k + 1) saved with output := output} (k + 1)
  have marked : Exec (.seq (.action (.push 8 true)) (.action (.push 1 true)))
      ({base (k + 1) saved with output := List.replicate (k + 1) false ++ output}).store 2
      ({base (k + 2) saved with output := (true :: List.replicate (k + 1) false) ++ output}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have checked := Exec.seq ready (Exec.seq zeroed marked)
  have cost : 3 * (k + 1) + 4 = 1 + ((3 * (k + 1) + 1) + 2) := by omega
  simpa only [finish, base, cost] using checked

def block : Block 9 := .seq raisingLoop (.seq ClauseQuery.reverseLoop finish)
def fuel (n k : Nat) : Nat :=
  ((5 * (k + 1) + 4) * n + 1) + ((4 * ((k + 2) * n) + 1) + (3 * (k + 1) + 4))

theorem block_exec {n k : Nat} (m : AffineMap n k) (saved : BitString) :
    Exec block (raising m saved []).store (fuel n k)
      ({base (k + 2) saved with output := mapBits (freeMap m)}).store := by
  have raised : Exec raisingLoop (raising m saved []).store
      ((5 * (k + 1) + 4) * n + 1)
      ({base (k + 1) saved with excess := (mapBits (raiseMap m)).reverse}).store := by
    simpa only [List.append_nil] using raisingLoop_exec m saved []
  have reversed : Exec ClauseQuery.reverseLoop
      ({base (k + 1) saved with excess := (mapBits (raiseMap m)).reverse}).store
      (4 * ((k + 2) * n) + 1)
      ({base (k + 1) saved with output := mapBits (raiseMap m)}).store := by
    have lengths : (mapBits (raiseMap m)).length = (k + 2) * n := by
      rw [mapBits_length, Nat.mul_comm]
    simpa only [base, List.length_reverse, lengths, List.reverse_reverse,
      List.append_nil] using
      ClauseQuery.reverse_exec (base (k + 1) saved) (mapBits (raiseMap m)).reverse
  have checked := Exec.seq raised (Exec.seq reversed (finish_exec k saved (mapBits (raiseMap m))))
  simpa only [block, fuel, free_bits] using checked

theorem fuel_bound (n k : Nat) : fuel n k ≤ 20 * (k + 2) * (n + 1) := by
  simp only [fuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
  omega

def program : Program 9 := block.program 0 8

theorem program_run {n k : Nat} (m : AffineMap n k) (saved : BitString) :
    BitRegister.run program (fuel n k + 1) ⟨.running 0, (raising m saved []).store⟩ =
      ⟨.accepted, ({base (k + 2) saved with output := mapBits (freeMap m)}).store⟩ :=
  (block_exec m saved).program_run 0 8

end PNP.Concrete.ResidualReduction.MatrixFreeInstructions
