import PNP.Concrete.ResidualReduction.SourceCandidateChoiceAlgebra
import PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions

/-! The selected support is an XOR sum, not a set union. In particular, two
equal selected indices cancel. These byte identities are the witness boundary
for the literal instruction implementation. -/

namespace PNP.Concrete.ResidualReduction.SourceAxisWitness
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceCandidateChoice (Axis)

def point {n : Nat} (i k : Fin n) : Axis → Point n
  | .first => unitPoint n i
  | .second => unitPoint n k
  | .both => pXor (unitPoint n i) (unitPoint n k)

theorem point_exact {n : Nat} (i k : Fin n) (a : Axis) :
    point i k a = sumUnits (SourceCandidateChoice.support i k a) := by
  cases a <;> simp only [point, SourceCandidateChoice.support, sumUnits, point_xor_zero]

theorem point_xor_bytes {n : Nat} (x y : Point n) :
    (SourceEncoding.pointCodec n).encode (pXor x y) =
      List.zipWith Bool.xor ((SourceEncoding.pointCodec n).encode x)
        ((SourceEncoding.pointCodec n).encode y) := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    rcases x with ⟨a, x⟩
    rcases y with ⟨b, y⟩
    exact congrArg (List.cons (Bool.xor a b)) (ih x y)

theorem xor_reversed_bytes {n : Nat} (x y : Point n) :
    (List.zipWith Bool.xor ((SourceEncoding.pointCodec n).encode x).reverse
      ((SourceEncoding.pointCodec n).encode y).reverse).reverse =
        (SourceEncoding.pointCodec n).encode (pXor x y) := by
  rw [List.reverse_zipWith (by rw [List.length_reverse, List.length_reverse,
    SourceEncoding.point_length, SourceEncoding.point_length])]
  simp only [List.reverse_reverse, point_xor_bytes]

theorem repeated_both {n : Nat} (i : Fin n) :
    point i i .both = zeroPoint n := point_xor_self _
theorem repeated_both_bytes {n : Nat} (i : Fin n) :
    (SourceEncoding.pointCodec n).encode (point i i .both) = List.replicate n false := by
  rw [repeated_both, SourceUnitDirectionInstructions.zero_bytes]

end PNP.Concrete.ResidualReduction.SourceAxisWitness
