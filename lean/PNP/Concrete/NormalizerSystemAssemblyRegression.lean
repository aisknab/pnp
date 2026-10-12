import PNP.Concrete.NormalizerSystemAssembly
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : SystemAssembly.State) (n : Nat) (bounded : r.store.Bounded n) :
    SystemAssembly.fuel r ≤ SystemAssembly.bound.eval n := SystemAssembly.fuel_bound r n bounded
example (r : SystemAssembly.State) : (SystemAssembly.result r).recovery = r.recovery :=
  SystemAssembly.result_recovery r
example (r : SystemAssembly.State) :
    (SystemAssembly.joinPackets.result r).registers.output = r.b ++ (r.a ++ r.registers.output) :=
  SystemAssembly.joinPackets_output r
#print axioms SystemAssembly.construction_result
#print axioms SystemAssembly.afterB_shared
#print axioms SystemAssembly.afterA_shared
#print axioms SystemAssembly.afterE_packets
#print axioms SystemAssembly.joinPackets_output
#print axioms SystemAssembly.block_exec
#print axioms SystemAssembly.fuel_bound
#print axioms SystemAssembly.result_bounded
#print axioms SystemAssembly.result_recovery
#print axioms SystemAssembly.result_shared
#print axioms SystemAssembly.result_output
end PNP.Concrete.NormalizerBlocks
