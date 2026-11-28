import PNP.ClauseSquare.Framed

namespace PNP.ClauseSquare.Regression

open PNP.Concrete

-- Source literals below are fixed words in the strict grammar. The expected columns
-- are independent constants, not recomputed by the construction under test.
private def bits (s : String) : BitString := s.toList.map (· == '1')
private def cols (s : Raw) (a : Nat) : List Nat :=
  (List.range s.d).map (chosen s (numberedHead s.n a))

private def pos := compile (bits "110001110010100")
private def neg := compile (bits "110001000010100")
private def bad := compile ([] : BitString)
private def vacuous := compile (bits "00100")
private def emptyClause := compile (bits "000110100")

#guard pos.n == 1 && pos.d == 4
#guard cols pos 0 == [7,6,12,9] && cols pos 1 == [5,6,12,9]
#guard cols neg 0 == [5,6,12,9] && cols neg 1 == [7,6,12,9]
#guard action pos (numberedHead pos.n 1) 13 == 0
#guard action pos (numberedHead pos.n 0) 13 != 0
#guard action neg (numberedHead neg.n 0) 13 == 0
#guard action neg (numberedHead neg.n 1) 13 != 0
#guard bad.n == 0 && bad.d == 1 && cols bad 0 == [1]
#guard action bad (numberedHead bad.n 0) 1 == 1
#guard cols vacuous 0 == [3,3] && action vacuous (numberedHead vacuous.n 0) 3 == 0
#guard cols emptyClause 0 == [1,6,5]

-- All-zero tail and out-of-width masks must not make a singularity witness.
example (s : Raw) (a : Nat) (h : 2^s.n ≤ a) : ¬ NumberedKernel s a :=
  reject_high_mask s a h
example (x : Head (parsed none).n) : ¬ MaskWitness (parsed none) x := by
  intro h
  exact reject_singleton x ((mask_witness _ _).mpr h)

end PNP.ClauseSquare.Regression

namespace PNP.ClauseSquare.Regression.Targets
open PNP.ClauseSquare.Framed
open PNP.Concrete

-- n=1,d=2; dense C=I, D has bits in the SECOND column, not the second row.
def independentlyWritten : BitString :=
  [true,false,true,true,false, true,false,false,true, false,false,true,true]
def exampleBank : Bank :=
  ⟨1,2,[true,false,false,true, false,false,true,true],rfl⟩

theorem coefficients :
    decode independentlyWritten=some exampleBank ∧
    product exampleBank 0 3=3 ∧ product exampleBank 1 3=0 ∧
    product exampleBank 1 2=1 ∧ product exampleBank 1 1=1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem opposed : accept independentlyWritten=true ∧
    accept [true,false,true,true,false, true,false,false,true, false,false,false,false]=false :=
  ⟨rfl,rfl⟩

theorem tails :
    decode [true,true]=none ∧ decode [false,true]=none ∧
    decode (independentlyWritten.dropLast)=none ∧
    decode (independentlyWritten ++ [false])=none ∧
    accept (independentlyWritten ++ [true])=false :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

-- A nonzero tail is required but a zero head is legitimate.
theorem zero_shapes : accept [false,false]=false ∧
    accept [false,true,false,false]=true ∧ accept [false,true,false,true]=false :=
  ⟨rfl,rfl,rfl⟩

theorem raw_empty : accept (emit (encodeCNF ⟨0,[]⟩))=true ∧
    accept (emit (encodeCNF ⟨0,[[]]⟩))=false := ⟨rfl,rfl⟩

theorem raw_bad : emit []=[false,true,false,true] ∧ accept (emit [])=false ∧
    accept (emit (encodeCNF ⟨0,[[⟨false,0⟩]]⟩))=false := ⟨rfl,rfl,rfl⟩

theorem raw_unit : accept (emit (encodeCNF ⟨1,[[⟨true,0⟩]]⟩))=true ∧
    accept (emit (encodeCNF ⟨1,[[⟨true,0⟩],[⟨false,0⟩]]⟩))=false := ⟨rfl,rfl⟩

end PNP.ClauseSquare.Regression.Targets
