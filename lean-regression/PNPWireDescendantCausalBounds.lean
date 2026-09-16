import PNP.NANDWireDescendantCausalBounds

namespace PNP.Regression.WireDescendantCausalBounds

open PNP.DirectWire WireDescendantHistory

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel run.result.candidate labels output ≤
      CausalBound.outputLevel source.candidate labels output :=
  run.output_dependency_bound labels output

example {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    {stages : List RawStage}
    (run : CompiledRun
      (extractTerminalSupport candidate records).extractedCandidate.toImplementation stages) :
    ∃ compiled, ArbitrarySupportSplice.compile candidate records run.result.candidate =
      some compiled :=
  run.extracted_compiles candidate records

#print axioms WireHistoryArbitrarySupport.closedHistory_dependencyInterfaceBound
#print axioms StageCompilation.output_dependency_bound
#print axioms CompiledRun.output_dependency_bound
#print axioms CompiledRun.extracted_causalInterfaceBound
#print axioms CompiledRun.extracted_compiles

end PNP.Regression.WireDescendantCausalBounds
