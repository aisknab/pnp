import PNP.Concrete.BitRegisterCopyProgram

open PNP.Concrete
open PNP.Concrete.BitRegister

example :
    BitRegister.run (CopyProgram.program (0 : Fin 2) (1 : Fin 2)) 19
      ⟨.running 0, Store.cons [] (Store.cons [false] (Store.cons [true, false] .nil))⟩ =
    ⟨.accepted, Store.cons [] (Store.cons [true, false] (Store.cons [true, false] .nil))⟩ :=
  CopyProgram.run 0 1 (Store.cons [false] (Store.cons [true, false] .nil))
example :
    BitRegister.run (CopyProgram.program (1 : Fin 2) (0 : Fin 2)) 5
      ⟨.running 0, Store.cons [] (Store.cons [] (Store.cons [true, false] .nil))⟩ =
    ⟨.accepted, Store.cons [] (Store.cons [] (Store.cons [] .nil))⟩ :=
  CopyProgram.run 1 0 (Store.cons [] (Store.cons [true, false] .nil))
example :
    BitRegister.run (CopyProgram.program (0 : Fin 2) (0 : Fin 2)) 1
      ⟨.running 0, Store.cons [] (Store.cons [true] (Store.cons [false] .nil))⟩ =
    ⟨.accepted, Store.cons [] (Store.cons [true] (Store.cons [false] .nil))⟩ :=
  CopyProgram.run 0 0 (Store.cons [true] (Store.cons [false] .nil))
example (source other destination : BitString) :
    BitRegister.run (CopyProgram.program (2 : Fin 3) (0 : Fin 3)) (7 * source.length + 5)
      ⟨.running 0, Store.cons [] (Store.cons source (Store.cons other (Store.cons destination .nil)))⟩ =
    ⟨.accepted, Store.cons [] (Store.cons source (Store.cons other (Store.cons source .nil)))⟩ :=
  CopyProgram.run 2 0 (Store.cons source (Store.cons other (Store.cons destination .nil)))
example (destination source : Fin 5) :
    ∀ instruction, instruction ∈ (CopyProgram.program destination source).code →
      CopyProgram.CopyFree instruction :=
  CopyProgram.program_copyFree destination source
example {count bound : Nat} (destination source : Fin count) (store : Store count)
    (bounded : store.Bounded bound) :
    CopyProgram.instructionSteps destination source store ≤ 7 * bound + 5 :=
  CopyProgram.instructionSteps_le destination source store bounded

#print axioms Store.ext
#print axioms Store.get_set
#print axioms Store.set_get
#print axioms Store.set_set_same
#print axioms CopyProgram.initialize_run
#print axioms CopyProgram.reverse_step
#print axioms CopyProgram.reverse_loop
#print axioms CopyProgram.restore_step
#print axioms CopyProgram.restore_loop
#print axioms CopyProgram.body_run
#print axioms CopyProgram.run
#print axioms CopyProgram.program_copyFree
#print axioms CopyProgram.instructionSteps_le
