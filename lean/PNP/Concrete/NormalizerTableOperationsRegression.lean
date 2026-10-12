import PNP.Concrete.NormalizerTableOperations

namespace PNP.Concrete.NormalizerBlocks

example (token : CNFToken) (r : Occurrence.Registers) :
    Exec (TableWrite.token token) r.store (TableWrite.tokenResult token r).fuel
      (TableWrite.tokenResult token r).state.store := TableWrite.token_exec token r
example (token : CNFToken) (r : Occurrence.Registers) :
    (TableWrite.tokenResult token r).fuel ≤ 4 * r.target.length + 13 :=
  TableWrite.token_fuel_bound token r
example (token : CNFToken) (r : Occurrence.Registers) :
    (TableWrite.tokenResult token r).state.input = r.input := TableWrite.token_input token r
example (token : CNFToken) (r : Occurrence.Registers) :
    (TableWrite.tokenResult token r).state.target = r.target := TableWrite.token_target token r

#print axioms TableWrite.separator_exec
#print axioms TableWrite.token_exec
#print axioms TableWrite.token_fuel_bound
#print axioms TableWrite.token_input
#print axioms TableWrite.token_target
#print axioms TableWrite.token_result_input

end PNP.Concrete.NormalizerBlocks
