import PNP.Concrete.NormalizerClauseSemantics

namespace PNP.Concrete.NormalizerBlocks

open Occurrence

example (clauses : List (List CNFLiteral)) (index : Nat) (buffer : BitString) (r : Registers) :
    (ClauseQuery.tokenScan (encodeClauseListTokens clauses ++ [.finish])
      (ClauseQuery.selectionState index buffer false r)).excess =
      (encodeTokenPairs (encodeLiteralListTokens (clauses[index]?.getD []))).reverse ++ buffer :=
  ClauseQuery.tokenScan_clauseList clauses index buffer r
example (index : Nat) (r : Registers) :
    (ClauseQuery.tokenScan [.finish] (ClauseQuery.selectionState index [true] false r)).excess = [true] := rfl
example : (ClauseQuery.tokenScan (encodeClauseListTokens [[⟨false, 1⟩], [⟨true, 0⟩], [⟨true, 0⟩]] ++ [.finish])
    (ClauseQuery.selectionState 2 [] false ⟨[], [], [], [], [], [], [], [], []⟩)).excess =
    [false, false, true, true] := rfl
example : (ClauseQuery.tokenScan (encodeClauseListTokens [[⟨false, 1⟩], [⟨true, 0⟩]] ++ [.finish])
    (ClauseQuery.selectionState 2 [true, false] false ⟨[], [], [], [], [], [], [], [], []⟩)).excess =
    [true, false] := rfl

#print axioms ClauseQuery.tokenScan_skip_data
#print axioms ClauseQuery.tokenScan_copy_data
#print axioms ClauseQuery.tokenScan_select_zero
#print axioms ClauseQuery.tokenScan_select_succ
#print axioms ClauseQuery.tokenScan_finish_buffer
#print axioms ClauseQuery.tokenScan_skip_finish
#print axioms ClauseQuery.tokenScan_clauseList

end PNP.Concrete.NormalizerBlocks
