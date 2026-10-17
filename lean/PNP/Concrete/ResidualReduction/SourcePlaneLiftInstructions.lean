import PNP.Concrete.ResidualReduction.SourcePlaneLiftState

/-! Optional witness translation by literal instructions. The weights are
copied exactly, the direction is multiplied by the homogeneous coefficient
map, and the canonical output is emitted. An absent witness remains absent. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneLift
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePlanePipeline (Saved)

def pairBytes {m n : Nat} (w : Point m) (v : Point n) : BitString :=
  (SourceEncoding.pointCodec m).encode w ++ (SourceEncoding.pointCodec n).encode v
def translated {m n k : Nat} (forms : AffineMap n k) (p : Point m × Point k) : Point m × Point n :=
  (p.1, linearMapEval forms p.2)
def finished {m n k : Nat} (forms : AffineMap n k) (w : Point m) (z : Point k) : Registers :=
  SourceLinearMap.ready z [] ((SourceAffineOutput.witnessCodec m n).encode (some (translated forms (w, z))))
def success : Block 29 := .seq seed <| .seq (lift copyLoop) <| .seq prepare <|
  .seq (lift SourceLinearMap.loop) <| .seq (lift SourceLinearMap.reorder) (lift (.action (.push 8 true)))
def successFuel (m n k : Nat) : Nat := 9 * m + (9 * k + 14) * n + 19

theorem success_exec (r : Registers) (tail : Store 13) (data : Saved) {m n k : Nat}
    (forms : AffineMap n k) (w : Point m) (z : Point k)
    (output : r.output = (SourceAffineOutput.witnessCodec m k).encode (some (w, z)))
    (map : data.directionMap = mapBits forms) (width : data.directionWidth = List.replicate k true)
    (rows : data.rows = List.replicate m true) :
    Exec success (store r tail data) (successFuel m n k) (store (finished forms w z) tail data) := by
  let before := SourceLinearMap.ready z (mapBits forms) ((SourceEncoding.pointCodec m).encode w).reverse
  let word := pairBytes w (linearMapEval forms z)
  let reversed := SourceLinearMap.ready z [] word.reverse
  let reordered := SourceLinearMap.ready z [] word
  have prepare := prepare_exec (copiedWeights r w z) tail data
  rw [prepared_weights r data w z forms map width] at prepare
  have mappedCore : Exec SourceLinearMap.loop before.store (SourceLinearMap.loopFuel n k) reversed.store := by
    simpa only [before, reversed, word, pairBytes, List.reverse_append] using
      SourceLinearMap.loop_exec forms z ((SourceEncoding.pointCodec m).encode w).reverse
  have reorderedCore : Exec SourceLinearMap.reorder reversed.store (4 * (m + n) + 3) reordered.store := by
    have checked := SourceLinearMap.reorder_exec z word
    have size : word.length = m + n := by simp only [word, pairBytes, List.length_append, SourceEncoding.point_length]
    simpa only [size] using checked
  have taggedCore : Exec (.action (.push (8 : Fin 9) true)) reordered.store 1 (finished forms w z).store := .action _ _
  have checked := Exec.seq (seed_exec r tail data) <|
    Exec.seq (copyWeights_exec r tail data w z output rows) <| Exec.seq prepare <|
      Exec.seq (lift_exec SourceLinearMap.loop before tail data _ reversed mappedCore) <|
        Exec.seq (lift_exec SourceLinearMap.reorder reversed tail data _ reordered reorderedCore)
          (lift_exec (.action (.push 8 true)) reordered tail data 1 (finished forms w z) taggedCore)
  have cost : successFuel m n k =
      5 + ((5 * m + 1) + (8 + (SourceLinearMap.loopFuel n k + ((4 * (m + n) + 3) + 1)))) := by
    simp only [successFuel, SourceLinearMap.loopFuel, Nat.mul_add, Nat.add_mul]
    omega
  simpa only [success, cost, before] using checked

def block : Block 29 := .branch 8 .skip .skip success
theorem block_exec (r : Registers) (tail : Store 13) (data : Saved) {m n k : Nat}
    (forms : AffineMap n k) (witness : Option (Point m × Point k))
    (output : r.output = (SourceAffineOutput.witnessCodec m k).encode witness)
    (map : data.directionMap = mapBits forms) (width : data.directionWidth = List.replicate k true)
    (rows : data.rows = List.replicate m true) :
    ∃ used after, Exec block (store r tail data) used (store after tail data) ∧
      after.output = (SourceAffineOutput.witnessCodec m n).encode (witness.map (translated forms)) ∧
      used ≤ successFuel m n k + 1 := by
  cases witness with
  | none =>
    have tag : (store r tail data).get 8 = [false] := output
    exact ⟨2, r, Exec.zero (source := (8 : Fin 29)) tag (.skip _), output, by unfold successFuel; omega⟩
  | some pair =>
    rcases pair with ⟨w, z⟩
    have tag : (store r tail data).get 8 = true :: pairBytes w z := output
    exact ⟨1 + successFuel m n k, finished forms w z,
      Exec.one (source := (8 : Fin 29)) tag (success_exec r tail data forms w z output map width rows), rfl, by omega⟩

def costPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 9) .variable)
    (.mul (.add (.mul (.constant 9) .variable) (.constant 14)) .variable)) (.constant 20)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = successFuel L L L + 1 := by
  change 9 * L + (9 * L + 14) * L + 20 = (9 * L + (9 * L + 14) * L + 19) + 1
  omega
theorem bounded_cost (m n k L : Nat) (hm : m ≤ L) (hn : n ≤ L) (hk : k ≤ L) :
    successFuel m n k + 1 ≤ costPolynomial.eval L := by
  rw [costPolynomial_eval]
  have rows := Nat.mul_le_mul_left 9 hm
  have product := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hk) 14) hn
  unfold successFuel
  omega

end PNP.Concrete.ResidualReduction.SourcePlaneLift
