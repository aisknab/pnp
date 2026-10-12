import PNP.Concrete.NormalizerCutSelections
namespace PNP.Concrete.NormalizerBlocks
example (r : CutDriver.State) (h : r.core.formula = GraphQuery.clauseData [])
    (trace : List TraceData.Row) (ht : r.trace = TraceData.encode trace) :
    (CutDriver.clausesResult r).clauses = [true,false] := by
  rw [CutDriver.clausesResult_canonical r [] trace h ht]
  rfl
example (r : CutDriver.State) (h : r.core.width = [])
    (trace : List TraceData.Row) (ht : r.trace = TraceData.encode trace) :
    (CutDriver.variablesResult r).variables = [true,false] := by
  rw [CutDriver.variablesResult_canonical r 0 trace h ht]
  rfl
#print axioms CutDriver.deriveClauses_exec
#print axioms CutDriver.clausesResult_frame
#print axioms CutDriver.clausesResult_canonical
#print axioms CutDriver.clausesSteps_bound
#print axioms CutDriver.deriveVariables_exec
#print axioms CutDriver.variablesResult_frame
#print axioms CutDriver.variablesResult_canonical
#print axioms CutDriver.variablesSteps_bound
end PNP.Concrete.NormalizerBlocks
