import PNP.Concrete.NANDFrontendClosed

namespace PNP.Concrete.NANDFrontend

example : program.code.length = 669 := program_code_length
example (r : Registers) :
    BitRegister.run program (frontendFuel r) (r.state 0) =
      ⟨.accepted, (frontendFinal r).store⟩ := frontend_run r
example (input : BitString) :
    (BitRegister.run program (frontendFuel (initialRegisters input))
      (BitRegister.initial program input)).control = .accepted := frontend_accepts input
example (input : BitString) :
    (BitRegister.run program (frontendFuel (initialRegisters input))
      (BitRegister.initial program input)).store.get 8 = (frontendFinal (initialRegisters input)).output :=
  frontend_output input

#print axioms program_code_length
#print axioms program_segments
#print axioms frontend_result_run
#print axioms frontend_run
#print axioms initial_registers
#print axioms frontend_accepts
#print axioms frontend_output

end PNP.Concrete.NANDFrontend
