import PNP.Concrete.ResidualReduction.SourceLineOutputState

/-! Literal direction lifting and canonical output emission. One reversed joint
prefix is retained across the map loop, followed by one reversal and a tag. -/

namespace PNP.Concrete.ResidualReduction.SourceLineOutput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceWitnessLift (store)

def pairBytes {j n k : Nat} (joint : Point j) (forms : AffineMap n k) (z : Point k) : BitString :=
  (SourceEncoding.pointCodec j).encode joint ++ (SourceEncoding.pointCodec n).encode (linearMapEval forms z)
def finished {j n k : Nat} (joint : Point j) (forms : AffineMap n k) (z : Point k) : Registers :=
  SourceLinearMap.ready z [] (true :: pairBytes joint forms z)
def success : Block 38 := .seq seed <| .seq (Frame.block 29 ClauseQuery.reverseLoop) <|
  .seq (Frame.block 29 SourceLinearMap.loop) <| .seq (Frame.block 29 SourceLinearMap.reorder)
    (Frame.block 29 (.action (.push (8 : Fin 9) true)))
def successFuel (j n k : Nat) : Nat := 8 * j + (9 * k + 14) * n + 15
theorem success_exec (r : Registers) (data : Store 29) {j n k : Nat}
    (joint : Point j) (forms : AffineMap n k) (z : Point k)
    (input : r.output = (SourceEncoding.pointCodec k).encode z)
    (jointWord : data.get 11 = (SourceEncoding.pointCodec j).encode joint)
    (mapWord : data.get 19 = mapBits forms) (width : data.get 20 = List.replicate k true) :
    Exec success (store r data) (successFuel j n k) (store (finished joint forms z) data) := by
  let jointBits := (SourceEncoding.pointCodec j).encode joint
  let ready := SourceLinearMap.ready z (mapBits forms) []
  let reversed := SourceLinearMap.ready z (mapBits forms) jointBits.reverse
  let output := pairBytes joint forms z
  have initial : seeded r data = {ready with excess := jointBits} := by
    simp only [seeded, cleared, loaded, ready, SourceLinearMap.ready, base, input, jointWord, mapWord, width, jointBits]
  have seedRun := seed_exec r data
  rw [initial] at seedRun
  have reverseRun : Exec (Frame.block 29 ClauseQuery.reverseLoop)
      (store {ready with excess := jointBits} data) (4 * j + 1) (store reversed data) := by
    apply Frame.execution
    simpa only [ready, reversed, jointBits, SourceLinearMap.ready, base, SourceEncoding.point_length, List.append_nil] using
      ClauseQuery.reverse_exec ready jointBits
  have mapRun : Exec (Frame.block 29 SourceLinearMap.loop) (store reversed data)
      (SourceLinearMap.loopFuel n k) (store (SourceLinearMap.ready z [] output.reverse) data) := by
    apply Frame.execution
    simpa only [reversed, output, pairBytes, jointBits, List.reverse_append] using
      SourceLinearMap.loop_exec forms z jointBits.reverse
  have reorderRun : Exec (Frame.block 29 SourceLinearMap.reorder)
      (store (SourceLinearMap.ready z [] output.reverse) data) (4 * (j + n) + 3)
      (store (SourceLinearMap.ready z [] output) data) := by
    apply Frame.execution
    simpa only [output, pairBytes, List.length_append, SourceEncoding.point_length] using
      SourceLinearMap.reorder_exec z output
  have tagRun : Exec (Frame.block 29 (.action (.push (8 : Fin 9) true)))
      (store (SourceLinearMap.ready z [] output) data) 1 (store (finished joint forms z) data) :=
    Frame.execution (Exec.action (.push (8 : Fin 9) true) (SourceLinearMap.ready z [] output).store) data
  have cost : successFuel j n k =
      9 + ((4 * j + 1) + (SourceLinearMap.loopFuel n k + ((4 * (j + n) + 3) + 1))) := by
    simp only [successFuel, SourceLinearMap.loopFuel, Nat.mul_add, Nat.add_mul]
    omega
  simpa only [success, cost] using Exec.seq seedRun (Exec.seq reverseRun (Exec.seq mapRun (Exec.seq reorderRun tagRun)))

def reject : Block 38 := .seq (.action (.clear 8)) (.action (.push 8 false))
def rejected (s : Store 38) : Store 38 := (s.set 8 []).set 8 [false]
theorem reject_exec (s : Store 38) : Exec reject s 2 (rejected s) := by
  have second : Exec (.action (.push (8 : Fin 38) false)) (s.set 8 []) 1 (rejected s) := by
    simpa only [rejected, Action.update, Action.instruction, Instruction.update, Store.get_set_same] using
      Exec.action (.push (8 : Fin 38) false) (s.set 8 [])
  exact Exec.seq (Exec.action (.clear (8 : Fin 38)) s) second
theorem rejected_output (s : Store 38) : (rejected s).get 8 = [false] := Store.get_set_same _ _ _
def block : Block 38 := .branch 4 reject reject success

def costPolynomial : NatPolynomial := .add (.add (.mul (.constant 16) .variable)
  (.mul (.add (.mul (.constant 9) .variable) (.constant 14)) .variable)) (.constant 16)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = successFuel (2 * L) L L + 1 := by
  change 16 * L + (9 * L + 14) * L + 16 = 8 * (2 * L) + (9 * L + 14) * L + 15 + 1
  omega
theorem bounded_cost (j n k L : Nat) (hj : j ≤ 2 * L) (hn : n ≤ L) (hk : k ≤ L) :
    successFuel j n k + 1 ≤ costPolynomial.eval L := by
  rw [costPolynomial_eval]
  have prefixBound := Nat.mul_le_mul_left 8 hj
  have mapped := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hk) 14) hn
  unfold successFuel
  omega

end PNP.Concrete.ResidualReduction.SourceLineOutput
