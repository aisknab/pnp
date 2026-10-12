import PNP.Concrete.NANDFrontendGateResult

namespace PNP.Concrete.NANDFrontend

example (p : BitRegister.Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment p base (gateReadCode base next failure)) :
    BitRegister.run p (gateReadResult r).fuel (r.state base) =
      (gateReadResult r).state.state (readerExit (gateReadResult r).valid next failure) :=
  gateRead_result_run p base next failure r placed
example (r : Registers) :
    (gateReadResult r).fuel ≤ 127 * (r.inputs.length + r.gate.length + r.input.length + 1) :=
  gateRead_result_bound r
example (r : Registers) (h : (gateReadResult r).valid = true) :
    (gateReadResult r).state.input.length < r.input.length :=
  (gateRead_result_progress r h).1
example (r : Registers) (h : (gateReadResult r).valid = true) :
    (gateReadResult r).state.inputs = r.inputs :=
  (gateRead_result_progress r h).2.1
example (r : Registers) (h : (gateReadResult r).valid = true) :
    (gateReadResult r).state.gate.length = r.gate.length + 1 :=
  (gateRead_result_progress r h).2.2

#print axioms gateRead_result_run
#print axioms gateRead_result_bound
#print axioms gateRead_result_progress

end PNP.Concrete.NANDFrontend
