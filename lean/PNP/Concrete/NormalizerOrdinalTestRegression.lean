import PNP.Concrete.NormalizerOrdinalTest
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Registers) : (OrdinalTest.result 1 {r with output := TableOwner.answer (some 1)}).output = [true] :=
  OrdinalTest.canonical 1 _ (some 1) rfl
example (r : Registers) : (OrdinalTest.result 2 {r with output := TableOwner.answer (some 1)}).output = [false] :=
  OrdinalTest.canonical 2 _ (some 1) rfl
example (r : Registers) : (OrdinalTest.result 0 {r with output := TableOwner.answer none}).output = [false] :=
  OrdinalTest.canonical 0 _ none rfl
#print axioms OrdinalTest.fill_exec
#print axioms OrdinalTest.prepare_exec
#print axioms OrdinalTest.compare_exec
#print axioms OrdinalTest.compared_output
#print axioms OrdinalTest.compareFuel_bound
#print axioms OrdinalTest.read_exec
#print axioms OrdinalTest.result_output
#print axioms OrdinalTest.fuel_bound
#print axioms OrdinalTest.canonical
end PNP.Concrete.NormalizerBlocks
