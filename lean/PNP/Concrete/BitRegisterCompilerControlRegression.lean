import PNP.Concrete.BitRegisterCompilerControl

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.Compiler
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
private def copyCode : Program 2 := ⟨[.copy 1 0 1, .accept], 0, 0, 1⟩

example : (graph copyCode).WellFormed := graph_wellFormed copyCode
example : (mainNode copyCode 0 (.copy 1 0 1)).onAccept = target copyCode 1 := rfl
example : localProgram (.copy (1 : Fin 2) 0 1) =
    CopyFreeCompiler.machine (CopyProgram.program (1 : Fin 2) 0) := rfl
example : (localProgram (.copy (0 : Fin 1) 0 1)).startState ≠ Operation.idle.startState := by decide
example : liftInstruction (.copy (0 : Fin 2) 1 7) = .copy 1 2 7 := rfl
example : liftInstruction (.branch (0 : Fin 2) 5 6 7) = .branch 1 5 6 7 := rfl

#print axioms Compiler.localProgram_wellFormed
#print axioms Compiler.auxiliaryProgram_wellFormed
#print axioms Compiler.nodePairs_length
#print axioms Compiler.nodePairs_member_bounds
#print axioms Compiler.nodePairs_pairwise
#print axioms Compiler.nodePairs_lookup_members
#print axioms Compiler.nodePairs_member_cases
#print axioms Compiler.fallback_member
#print axioms Compiler.instruction_members
#print axioms Compiler.graph_member_cases
#print axioms Compiler.target_resolves
#print axioms Compiler.graph_wellFormed
#print axioms Compiler.machine_wellFormed
#print axioms Compiler.graph_node_count
