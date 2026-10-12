import PNP.Concrete.NormalizerClauseTokens

namespace PNP.Concrete.NormalizerBlocks

open Occurrence

example (values : List CNFToken) (r : Registers) :
    ∃ fuel, Exec ClauseQuery.loop ({r with input := encodeTokenPairs values}).store fuel
      (ClauseQuery.tokenScan values r).store := ClauseQuery.tokenScan_exec values r
example (clause : List CNFLiteral) : ClauseQuery.DataTokens (encodeLiteralListTokens clause) :=
  ClauseQuery.clause_data clause
example (index : Nat) : ClauseQuery.DataTokens (encodeUnaryTokens index) := ClauseQuery.unary_data index
example : (ClauseQuery.tokenScan [.sep, .t, .f, .finish]
    ⟨[], [], [], [], [], [], [true], [], []⟩).excess = [false, false, true, true] := rfl

#print axioms ClauseQuery.pair_token_exec
#print axioms ClauseQuery.tokenScan_exec
#print axioms ClauseQuery.tokenScan_inactive
#print axioms ClauseQuery.DataTokens.append
#print axioms ClauseQuery.unary_data
#print axioms ClauseQuery.literal_data
#print axioms ClauseQuery.clause_data

end PNP.Concrete.NormalizerBlocks
