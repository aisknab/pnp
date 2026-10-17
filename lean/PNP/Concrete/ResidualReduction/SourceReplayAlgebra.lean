import PNP.Concrete.ResidualReduction.SourceReductionReplay
import PNP.Concrete.ResidualReduction.SourceChartAffine

/-! Direct reconstruction from stored source rows. The eliminated bit equals
a weighted evaluation at the zero-pivot point, so replay need not construct
the charted quadratic. These identities hold for arbitrary stored fields;
they do not assert that an arbitrary history is a valid reduction. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayAlgebra
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance

private theorem zero_head {n : Nat} (q : Quadratic (n + 1)) (z : Point n) :
    qEval q.2 z = qEval q (false,z) := by
  rcases q with ⟨head,tail⟩
  simp only [qEval,Bool.and_false,Bool.false_xor]

theorem tail_value {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    qEval (scalar (chartRows (markSource F w) k v)).2 z =
      weightedValue F w (insert n k (false,z)) := by
  calc
    _ = qEval (scalar (chartRows (markSource F w) k v)) (false,z) := zero_head _ z
    _ = qEval (scalar (markSource F w)) (unchart k v (false,z)) :=
      scalar_chart_eval (markSource F w) k v (false,z)
    _ = weightedValue F w (insert n k (false,z)) := by
      rw [markSource_scalar_eval]
      rfl

/-- A direct evaluator preserves the exact intended reconstruction function. -/
theorem decode_direct {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    decode (markSource F w) k v z =
      unchart k v (weightedValue F w (insert n k (false,z)),z) := by
  rw [decode,tail_value]

theorem insert_split {n : Nat} (k : Fin (n + 1)) (b : Bool) (z : Point n) :
    ∃ front suffix : BitString, front.length = k.val ∧
      (SourceEncoding.pointCodec n).encode z = front ++ suffix ∧
      (SourceEncoding.pointCodec (n + 1)).encode (insert n k (b,z)) = front ++ b :: suffix := by
  obtain ⟨front,suffix,width,whole,tail⟩ :=
    SourceChartAffine.cut_words SourceEncoding.unitCodec n k (insert n k (b,z))
  refine ⟨front,suffix,width,?_,?_⟩
  · simpa only [SourceEncoding.pointCodec,cut_insert] using tail
  · simpa only [SourceEncoding.pointCodec,cut_insert] using whole

theorem xor_bytes {n : Nat} (x y : Point n) :
    (SourceEncoding.pointCodec n).encode (pXor x y) =
      List.zipWith Bool.xor ((SourceEncoding.pointCodec n).encode x)
        ((SourceEncoding.pointCodec n).encode y) := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    rcases y with ⟨b,y⟩
    change Bool.xor a b :: (SourceEncoding.pointCodec n).encode (pXor x y) =
      Bool.xor a b :: List.zipWith Bool.xor ((SourceEncoding.pointCodec n).encode x)
        ((SourceEncoding.pointCodec n).encode y)
    exact congrArg (List.cons (Bool.xor a b)) (ih x y)

theorem unchart_false {n : Nat} (k : Fin (n + 1)) (v z : Point n) :
    unchart k v (false,z) = insert n k (false,z) := rfl
theorem unchart_true {n : Nat} (k : Fin (n + 1)) (v z : Point n) :
    unchart k v (true,z) = insert n k (true,pXor z v) := rfl

end PNP.Concrete.ResidualReduction.SourceReplayAlgebra
