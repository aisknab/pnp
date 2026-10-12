import PNP.Concrete.BitRegisterControl

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.CopyFreeCompiler
open WorkMachineProgramGraph

private def emptyCode : Program 1 :=
  { code := [], entry := 50, input := 0, output := 0 }

private def branchCode : Program 1 :=
  { code := [.branch 0 2 1 3, .jump 0, .accept, .reject], entry := 0, input := 0, output := 0 }

example : (graph emptyCode).nodes.length = 1 := graph_node_count emptyCode
example : addressRef emptyCode 50 = (fallbackNode emptyCode).reference := by rfl
example : (graph branchCode).nodes.length = 9 := graph_node_count branchCode
example : addressRef branchCode 100 = (fallbackNode branchCode).reference := by rfl
example : (mainNode branchCode 0 (.branch 0 2 1 3)).onAccept = target branchCode 2 := by rfl
example : (mainNode branchCode 0 (.branch 0 2 1 3)).onReject =
    .node (auxiliaryRef 0 (.branch (0 : Fin 1) 2 1 3)) := by rfl
example : (auxiliaryNode branchCode 0 (.branch 0 2 1 3)).onAccept = target branchCode 3 := by rfl
example : (auxiliaryNode branchCode 0 (.branch 0 2 1 3)).onReject = target branchCode 1 := by rfl
example : (graph branchCode).WellFormed := graph_wellFormed branchCode
example {count : Nat} (program : Program count) (address : Nat) :
    Endpoint.Resolves (graph program).nodes (target program address) :=
  target_resolves program address
example {count : Nat} (destination source : Fin count) :
    CopyFree (CopyProgram.program destination source) :=
  CopyProgram.program_copyFree destination source
example : ¬ CopyFree ({ code := [.copy 0 0 0], entry := 0, input := 0, output := 0 } : Program 1) := by
  simp [CopyFree, CopyProgram.CopyFree]

#print axioms CopyFreeCompiler.localProgram_wellFormed
#print axioms CopyFreeCompiler.auxiliaryProgram_wellFormed
#print axioms CopyFreeCompiler.nodePairs_length
#print axioms CopyFreeCompiler.nodePairs_member_bounds
#print axioms CopyFreeCompiler.nodePairs_pairwise
#print axioms CopyFreeCompiler.nodePairs_lookup_members
#print axioms CopyFreeCompiler.nodePairs_member_cases
#print axioms CopyFreeCompiler.fallback_member
#print axioms CopyFreeCompiler.instruction_members
#print axioms CopyFreeCompiler.graph_member_cases
#print axioms CopyFreeCompiler.target_resolves
#print axioms CopyFreeCompiler.graph_wellFormed
#print axioms CopyFreeCompiler.machine_wellFormed
#print axioms CopyFreeCompiler.graph_node_count
