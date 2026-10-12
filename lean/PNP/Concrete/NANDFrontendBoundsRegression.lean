import PNP.Concrete.NANDFrontendBounds

namespace PNP.Concrete.NANDFrontend

example (r : Registers) (b : Nat) (h : r.store.Bounded b) :
    frontendFuel r ≤ frontendBudget b := frontendFuel_bound r b h
example (input : BitString) :
    frontendFuel (initialRegisters input) ≤ frontendBudget input.length := frontend_input_bound input
example (input : BitString) : (initialRegisters input).store.Bounded input.length :=
  initial_registers_bounded input
example (b : Nat) : headerBudget b = 6 * b + 19 := rfl
example (b : Nat) :
    traversalBudget b = 128 * (preLoopBound b + 1) * (3 * preLoopBound b + 1) := rfl

#print axioms registers_fields_bounded
#print axioms registers_bounded_of_run
#print axioms frontendFuel_bound
#print axioms initial_registers_bounded
#print axioms frontend_input_bound

end PNP.Concrete.NANDFrontend
