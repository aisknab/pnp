import PNP.Concrete.NormalizerSystemAssemblyState
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : SystemAssembly.State) : (SystemAssembly.saveB.result r).b = r.registers.output := rfl
example (r : SystemAssembly.State) : (SystemAssembly.saveA.result r).a = r.registers.output := rfl
example (iteration : SystemRows.Iteration) (r : SystemAssembly.State) :
    ((SystemAssembly.listRoutine iteration).result r).recovery = r.recovery :=
  (SystemAssembly.phase_recovery iteration r).2.1
#print axioms SystemAssembly.liftRows_exec
#print axioms SystemAssembly.frame_core_bounded
#print axioms SystemAssembly.frame_set
#print axioms SystemAssembly.saved_b_store
#print axioms SystemAssembly.saved_a_store
#print axioms SystemAssembly.Routine.seq
#print axioms SystemAssembly.bRoutine
#print axioms SystemAssembly.listRoutine
#print axioms SystemAssembly.saveB
#print axioms SystemAssembly.saveA
#print axioms SystemAssembly.b_shared
#print axioms SystemAssembly.list_shared
#print axioms SystemAssembly.phase_recovery
end PNP.Concrete.NormalizerBlocks
