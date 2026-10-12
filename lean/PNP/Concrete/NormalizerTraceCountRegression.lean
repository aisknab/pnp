import PNP.Concrete.NormalizerTraceCount

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) : TraceCount.fuel r ≤ 4 * r.target.length + 5 := TraceCount.fuel_bound r
example (r : Occurrence.Registers) (h : r.excess = []) :
    (TraceCount.result r).output = [r.target.length == r.remaining.length] := TraceCount.result_output r h
example : ((7 - 3 == 0) && (3 - 7 == 0)) = false := by decide
example : ((4 - 4 == 0) && (4 - 4 == 0)) = true := by decide

#print axioms TraceCount.drain_exec
#print axioms TraceCount.finish_exec
#print axioms TraceCount.block_exec
#print axioms TraceCount.fuel_bound
#print axioms TraceCount.empty_length
#print axioms TraceCount.residuals_equal
#print axioms TraceCount.result_output

end PNP.Concrete.NormalizerBlocks
