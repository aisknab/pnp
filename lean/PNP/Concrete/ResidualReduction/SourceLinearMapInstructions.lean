import PNP.Concrete.ResidualReduction.SourceLinearMapRowInstructions

/-! Complete literal application of an encoded affine map's homogeneous
part to an arbitrary parameter vector. Every row is processed, including
constant-only rows. This supplies the original-coordinate direction lift. -/

namespace PNP.Concrete.ResidualReduction.SourceLinearMap
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def ready {k : Nat} (z : Point k) (input output : BitString) : Registers :=
  {base k ((SourceEncoding.pointCodec k).encode z) with input := input, output := output}
def loop : Block 9 := .loop 0 row
def loopFuel (n k : Nat) : Nat := (9 * k + 10) * n + 1
theorem loop_exec {n k : Nat} (forms : AffineMap n k) (z : Point k) (output : BitString) :
    Exec loop (ready z (mapBits forms) output).store (loopFuel n k)
      (ready z [] (((SourceEncoding.pointCodec n).encode (linearMapEval forms z)).reverse ++ output)).store := by
  induction n generalizing output with
  | zero => cases forms; exact Exec.loopStop rfl
  | succ n ih =>
    rcases forms with ⟨f, fs⟩
    obtain ⟨head, tail, word⟩ := affineWord_nonempty f
    have nonempty : (ready z (mapBits (n := n + 1) (f, fs)) output).store.get 0 =
        head :: (tail ++ mapBits fs) := by
      change affineWord f ++ mapBits fs = _
      rw [word]
      rfl
    have first : Exec row (ready z (mapBits (n := n + 1) (f, fs)) output).store (rowFuel k)
        (ready z (mapBits fs) (value f z :: output)).store := row_exec (ready z [] output) f z (mapBits fs)
    have checked := Exec.loopStep nonempty first (ih fs (value f z :: output))
    have cost : loopFuel (n + 1) k = 1 + (rowFuel k + loopFuel n k) := by
      simp only [loopFuel, rowFuel, Nat.mul_add, Nat.mul_one]
      omega
    simpa only [loop, cost, linearMap_cons, point_bits_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append] using checked

def reorder : Block 9 := .seq
  (.seq (.action (.copy 3 8)) (.action (.clear 8))) ClauseQuery.reverseLoop
theorem reorder_exec {k : Nat} (z : Point k) (word : BitString) :
    Exec reorder (ready z [] word.reverse).store (4 * word.length + 3) (ready z [] word).store := by
  let staged := {ready z [] [] with excess := word.reverse}
  have copied : Exec (.seq (.action (.copy (3 : Fin 9) 8)) (.action (.clear 8)))
      (ready z [] word.reverse).store 2 staged.store := Exec.seq (.action _ _) (.action _ _)
  have reversed : Exec ClauseQuery.reverseLoop staged.store (4 * word.length + 1) (ready z [] word).store := by
    simpa only [staged, ready, base, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec (ready z [] []) word.reverse
  have cost : 4 * word.length + 3 = 2 + (4 * word.length + 1) := by omega
  simpa only [reorder, cost] using Exec.seq copied reversed

def block : Block 9 := .seq loop reorder
def fuel (n k : Nat) : Nat := (9 * k + 14) * n + 4
theorem block_exec {n k : Nat} (forms : AffineMap n k) (z : Point k) :
    Exec block (ready z (mapBits forms) []).store (fuel n k)
      (ready z [] ((SourceEncoding.pointCodec n).encode (linearMapEval forms z))).store := by
  have computed := loop_exec forms z []
  simp only [List.append_nil] at computed
  have reordered := reorder_exec z ((SourceEncoding.pointCodec n).encode (linearMapEval forms z))
  rw [SourceEncoding.point_length] at reordered
  have cost : fuel n k = loopFuel n k + (4 * n + 3) := by
    simp only [fuel, loopFuel, Nat.add_mul]
    omega
  simpa only [block, cost] using Exec.seq computed reordered
theorem space_exec {n : Nat} (s : Space n) (z : Point s.parameters) :
    Exec block (ready z (mapBits s.forms) []).store (fuel n s.parameters)
      (ready z [] ((SourceEncoding.pointCodec n).encode (s.direction z))).store := block_exec s.forms z
theorem fuel_mono (n k N K : Nat) (hn : n ≤ N) (hk : k ≤ K) : fuel n k ≤ fuel N K :=
  Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hk) 14) hn) 4
def costPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.constant 9) .variable) (.constant 14)) .variable) (.constant 4)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = fuel L L := rfl
theorem bounded_cost (n k L : Nat) (hn : n ≤ L) (hk : k ≤ L) : fuel n k ≤ costPolynomial.eval L :=
  fuel_mono n k L L hn hk
def program : Program 9 := block.program 0 8
theorem program_run {n k : Nat} (forms : AffineMap n k) (z : Point k) :
    BitRegister.run program (fuel n k + 1) ⟨.running 0, (ready z (mapBits forms) []).store⟩ =
      ⟨.accepted, (ready z [] ((SourceEncoding.pointCodec n).encode (linearMapEval forms z))).store⟩ :=
  (block_exec forms z).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceLinearMap
