import PNP.Concrete.NormalizerOutputPostprocess
namespace PNP.Concrete.NormalizerBlocks
example : (OutputPostprocess.result []).registers.output = [false,false,false] :=
  OutputPostprocess.malformed_output [] rfl
example (rest : BitString) :
    (OutputPostprocess.result (false::rest)).registers.output = [false,false,false] :=
  OutputPostprocess.malformed_output (false::rest) rfl
example (width : Nat) (F : CNFFormula) :
    OutputPostprocess.result (NANDFrontend.recordData width F) =
      OutputBranches.dispatched (SourceCheck.result (MatchingDriver.encode F.variableCount F.clauses))
        (List.replicate width true) := OutputPostprocess.canonical_result width F
#print axioms OutputPostprocess.check_exec
#print axioms OutputPostprocess.valid_exec
#print axioms OutputPostprocess.invalid_exec
#print axioms OutputPostprocess.initial_registers
#print axioms OutputPostprocess.block_exec
#print axioms OutputPostprocess.closed_run
#print axioms OutputPostprocess.malformed_output
#print axioms OutputPostprocess.canonical_result
end PNP.Concrete.NormalizerBlocks
