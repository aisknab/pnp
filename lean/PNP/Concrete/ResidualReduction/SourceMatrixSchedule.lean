import PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions

/-! The exact natural-counter schedule of the existing unit-pair query.
These identities connect incrementing instruction counters to the original
Fin enumeration; they do not replace its equation set or ordering. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixSchedule
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

def equationBytes {n : Nat} (F : Family n) (i j : Nat) : BitString :=
  F.map (fun r => polarBit r i j) ++ [false]
def columnBytes {n : Nat} (F : Family n) (i start count : Nat) : BitString :=
  (List.range' start count).flatMap (equationBytes F i)
def matrixBytes {n : Nat} (F : Family n) (start count : Nat) : BitString :=
  (List.range' start count).flatMap (fun i => columnBytes F i 0 n)

theorem columnBytes_zero {n : Nat} (F : Family n) (i start : Nat) :
    columnBytes F i start 0 = [] := rfl
theorem columnBytes_succ {n : Nat} (F : Family n) (i start count : Nat) :
    columnBytes F i start (count + 1) = equationBytes F i start ++ columnBytes F i (start + 1) count := by
  simp only [columnBytes, List.range'_succ, List.flatMap_cons]
theorem matrixBytes_zero {n : Nat} (F : Family n) (start : Nat) : matrixBytes F start 0 = [] := rfl
theorem matrixBytes_succ {n : Nat} (F : Family n) (start count : Nat) :
    matrixBytes F start (count + 1) = columnBytes F start 0 n ++ matrixBytes F (start + 1) count := by
  simp only [matrixBytes, List.range'_succ, List.flatMap_cons]

theorem finite_range_values (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range']
  · intro i left right
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range', Nat.one_mul, Nat.zero_add]
    rfl

theorem matrixBytes_exact {n : Nat} (F : Family n) :
    matrixBytes F 0 n = MatrixInstructions.matrixBits (SourceClosure.affineMaskRows F) := by
  rw [SourceMatrixEncoding.affineMask_bytes]
  unfold matrixBytes columnBytes
  rw [← finite_range_values n]
  simp only [List.flatMap_map, equationBytes]

theorem matrixBytes_length {n : Nat} (F : Family n) :
    (matrixBytes F 0 n).length = (F.length + 1) * (n * n) := by
  rw [matrixBytes_exact, MatrixInstructions.matrixBits_length]
  rw [SourceClosure.affineMaskRows, SourcePlane.planeRows_length]

end PNP.Concrete.ResidualReduction.SourceMatrixSchedule
