import PNP.Concrete.NormalizerExplorationBudget

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : (budgeted (loaded (encode 3 [[], []] [none, none]))).remaining =
    [true, true, true, true, true] := by decide
example : (budgeted (loaded (encode 0 [] []))).remaining = [] := by decide
example : (budgeted (loaded (encode 2 [[]] [none]))).core.trace = [] := by decide

#print axioms Exploration.startBudget_exec
#print axioms Exploration.prependCount_exec
#print axioms Exploration.saveBudget_exec
#print axioms Exploration.buildBudget_exec
#print axioms Exploration.budgeted_fields
#print axioms Exploration.budgetFuel_eq

end PNP.Concrete.NormalizerBlocks
