import PNP.Concrete.NANDFrontendLoopResult

namespace PNP.Concrete.NANDFrontend

example (p : BitRegister.Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment p base (gateLoopCode base next failure)) :
    BitRegister.run p (gateLoopResult r).fuel (r.state base) =
      (gateLoopResult r).state.state (readerExit (gateLoopResult r).valid next failure) :=
  gateLoop_result_run p base next failure r placed
example (r : Registers) :
    (gateLoopResult r).fuel ≤ 128 * (r.input.length + 1) *
      (r.inputs.length + r.gate.length + r.input.length + 1) := gateLoop_result_bound r
example (r : Registers) (h : r.input = []) : (gateLoopResult r).fuel = 1 := by
  rw [gateLoopResult_empty r h]
example (r : Registers) (h : (gateReadResult r).valid = true) :
    loopPotential (gateReadResult r).state ≤ loopPotential r := gateRead_result_potential r h

#print axioms gateLoopResult_empty
#print axioms gateLoopResult_end
#print axioms gateLoopResult_failure
#print axioms gateLoopResult_continue
#print axioms gateLoop_result_run
#print axioms loopPotential_positive
#print axioms loopBudget_minimum
#print axioms loopBudget_step
#print axioms gateRead_result_potential
#print axioms gateLoop_result_bound

end PNP.Concrete.NANDFrontend
