import PNP.Concrete.NormalizerOccurrenceHeader

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    Exec Occurrence.headerBody ({r with input := []}).store 2
      ({r with input := [], active := []}).store := Occurrence.header_empty_exec r
example (r : Occurrence.Registers) (rest : BitString) :
    Exec Occurrence.headerBody ({r with input := false :: rest}).store 3
      ({r with input := rest, active := []}).store := Occurrence.header_false_exec r rest
example (r : Occurrence.Registers) (rest : BitString) :
    Exec Occurrence.headerBody ({r with input := true :: rest}).store 3
      ({r with input := rest, target := true :: r.target}).store := Occurrence.header_true_exec r rest
example (input : BitString) (r : Occurrence.Registers) :
    Exec Occurrence.headerLoop ({r with input := input}).store
      (Occurrence.headerResult input r).fuel (Occurrence.headerResult input r).state.store :=
  Occurrence.header_exec input r
example (input : BitString) (r : Occurrence.Registers) :
    (Occurrence.headerResult input r).fuel ≤ 4 * input.length + 5 := Occurrence.header_fuel_bound input r
example (input : BitString) (r : Occurrence.Registers) :
    (Occurrence.headerResult input r).state.input.length ≤ input.length := Occurrence.header_input_bound input r
example (input : BitString) (r : Occurrence.Registers) :
    (Occurrence.headerResult input r).state.active = [] := Occurrence.header_stopped input r

#print axioms Occurrence.header_empty_exec
#print axioms Occurrence.header_false_exec
#print axioms Occurrence.header_true_exec
#print axioms Occurrence.header_exec
#print axioms Occurrence.header_fuel_bound
#print axioms Occurrence.header_input_bound
#print axioms Occurrence.header_stopped

end PNP.Concrete.NormalizerBlocks
