import PNP.ClauseSquare.Numbered

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete

def literalOccurrences (n : Nat) : List (List CNFLiteral) → Nat
  | [] => 0
  | c::cs => used n c + literalOccurrences n cs

theorem after_length (n s : Nat) (cs : List (List CNFLiteral)) :
    (afterClauses n s cs).length = cs.length+literalOccurrences n cs := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [afterClauses,List.length_append,block_length,ih,List.length_cons,literalOccurrences]
    omega

/-- One auxiliary per retained occurrence and clause, initial auxiliary, final column. -/
theorem exact_dimension (F : CNFFormula) : (parsed (some F)).d =
    2+F.clauses.length+literalOccurrences F.variableCount F.clauses := by
  change (afterClauses F.variableCount 0 F.clauses).length+1+1=_
  rw [after_length]; omega

/-- An exact entry width bound for *each* packed constant or individual slope column;
this is not a theorem about the runtime of a machine producing those columns. -/
theorem column_bound {n : Nat} (f : Term n → Bool) (j : Nat) (rs : List (List (Term n))) :
    packedColumn f j rs < 2^rs.length := by
  induction rs with
  | nil => exact Nat.zero_lt_one
  | cons r rs ih =>
    rw [packedColumn,List.length_cons,Nat.pow_succ]
    cases e : entry f r j with
    | false => change 2*packedColumn f j rs+0 < _; omega
    | true => change 2*packedColumn f j rs+1 < _; omega

theorem raw_column_bound (q : Option CNFFormula) (f : Term (parsed q).n → Bool) (j : Nat) :
    packedColumn f j (parsed q).rows < 2^(parsed q).d := by
  have hb := column_bound f j (parsed q).rows
  rw [always_square] at hb; exact hb

end PNP.ClauseSquare
