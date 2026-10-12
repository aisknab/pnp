import PNP.Concrete.NormalizerOwnerOperations

namespace PNP.Concrete.NormalizerBlocks

example (value : CNFToken) (r : Occurrence.Registers) :
    Exec (TableOwner.token value) r.store (TableOwner.tokenResult value r).fuel
      (TableOwner.tokenResult value r).state.store := TableOwner.token_exec value r
example (value : CNFToken) (r : Occurrence.Registers) : (TableOwner.tokenResult value r).fuel ≤ 7 :=
  TableOwner.token_fuel_bound value r
example (r : Occurrence.Registers) :
    (TableOwner.tokenResult .finish r).state.reserved = true :: r.reserved := rfl
example (r : Occurrence.Registers) : (TableOwner.foundState r).output = true :: r.reserved := rfl

#print axioms TableOwner.found_exec
#print axioms TableOwner.nextEntry_exec
#print axioms TableOwner.token_exec
#print axioms TableOwner.token_fuel_bound
#print axioms TableOwner.token_input
#print axioms TableOwner.token_target
#print axioms TableOwner.token_result_input

end PNP.Concrete.NormalizerBlocks
