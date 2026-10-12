import PNP.Concrete.NormalizerOccurrenceOperations

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (positive : Bool) (r : Occurrence.Registers) :
    Exec (Occurrence.startLiteral positive) r.store 6 (Occurrence.startState positive r).store :=
  Occurrence.start_exec positive r
example (r : Occurrence.Registers) :
    Exec Occurrence.found r.store 3 (Occurrence.foundState r).store := Occurrence.found_exec r
example (r : Occurrence.Registers) :
    Exec Occurrence.unit r.store 2 (Occurrence.unitState r).store := Occurrence.unit_exec r
example (value : CNFToken) (r : Occurrence.Registers) :
    Exec (Occurrence.token value) r.store (Occurrence.tokenResult value r).fuel
      (Occurrence.tokenResult value r).state.store := Occurrence.token_exec value r
example (value : CNFToken) (r : Occurrence.Registers) :
    (Occurrence.tokenResult value r).fuel ≤ 7 := Occurrence.token_fuel_bound value r
example (value : CNFToken) (r : Occurrence.Registers) :
    (Occurrence.tokenResult value r).state.input = r.input := Occurrence.token_input value r

#print axioms Exec.nonempty
#print axioms Occurrence.start_exec
#print axioms Occurrence.found_exec
#print axioms Occurrence.unit_exec
#print axioms Occurrence.token_exec
#print axioms Occurrence.token_fuel_bound
#print axioms Occurrence.token_input

end PNP.Concrete.NormalizerBlocks
