import PNP.Concrete.NormalizerOutputPackets
namespace PNP.Concrete.NormalizerBlocks
example (r : SystemAssembly.State) :
    (OutputBranches.loadCount.result r).registers.excess = r.core.rows := rfl
example (r : SystemAssembly.State) : (OutputBranches.modelPacket.result r).b = r.b := rfl
example (r : SystemAssembly.State) : (OutputBranches.frameSystem.result r).recovery = r.recovery := rfl
#print axioms OutputBranches.liftPacket_exec
#print axioms OutputBranches.modelPacket_output
#print axioms OutputBranches.frameSystem_output
#print axioms OutputBranches.assembly_rows
#print axioms OutputBranches.failure_rows
#print axioms OutputBranches.equation_exec
#print axioms OutputBranches.equation_output
#print axioms OutputBranches.equation_fuel_bound
#print axioms OutputBranches.success_exec
#print axioms OutputBranches.success_output
#print axioms OutputBranches.successFuel_bound
end PNP.Concrete.NormalizerBlocks
