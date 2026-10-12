import PNP.Concrete.NormalizerExplorationPolynomial

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : (result (encode 3 [[⟨true, 2⟩]] [none])).registers.output =
    TraceData.encode [(⟨false, 2⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide
example : (result (encode 0 [] [])).registers.output = [] := by decide
example : (result (encode 1 [[]] [some 0])).registers.output = [] := by decide
example : (result []).registers.output = [] := by decide

example : (result (encode 2 [[⟨true, 0⟩], [⟨true, 0⟩, ⟨false, 1⟩]] [none, some 0])).registers.output =
    TraceData.encode [(⟨false, 1⟩, some ⟨true, 1⟩), (⟨true, 1⟩, some ⟨false, 0⟩),
      (⟨false, 0⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide

#print axioms Exploration.block_exec
#print axioms Exploration.closed_run
#print axioms Exploration.initialized_loop_bound
#print axioms Exploration.sourceSteps_bound
#print axioms Exploration.padded_run
#print axioms Exploration.acceptsWithin
#print axioms Exploration.polynomial_program
#print axioms Exploration.polynomial_output
#print axioms Exploration.polynomial_accepts
#print axioms Exploration.polynomial_output_length
#print axioms Exploration.polynomial_canonical
#print axioms Exploration.machine_output
#print axioms Exploration.machine_canonical

end PNP.Concrete.NormalizerBlocks
