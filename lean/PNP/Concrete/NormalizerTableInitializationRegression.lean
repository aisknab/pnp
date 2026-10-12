import PNP.Concrete.NormalizerTableInitialization

namespace PNP.Concrete.NormalizerBlocks

example (word : BitString) (r : Occurrence.Registers) :
    Exec TableInit.loop ({r with target := word}).store (6 * word.length + 1) (TableInit.built word r).store :=
  TableInit.loop_exec word r
example (count : Nat) : (TableInit.emptyData count).length = 4 * count := TableInit.emptyData_length count
example (count : Nat) :
    (encodeTokenPairs (encodeClauseListTokens (MatchingTable.clauses (List.replicate count none)))).reverse =
      TableInit.emptyData count := TableInit.emptyData_encoding count
example : TableInit.emptyData 2 = [false, true, true, false, false, true, true, false] := rfl

#print axioms TableInit.loop_exec
#print axioms TableInit.emptyData_length
#print axioms TableInit.emptyData_encoding
#print axioms TableInit.built_input
#print axioms TableInit.built_target

end PNP.Concrete.NormalizerBlocks
