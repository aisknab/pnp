import PNP.Concrete.NormalizerClauseCount

namespace PNP.Concrete.NormalizerBlocks
open ClauseCount
example : count [] = 0 := by decide
example : count [false] = 0 := by decide
example : count [false, true, true, false, false, true] = 2 := by decide
example : (ClauseCount.run [false, true] (Occurrence.initialRegisters [])).state.target = [true] := by decide
example : (ClauseCount.run [false] (Occurrence.initialRegisters [])).state.input = [] := by decide

#print axioms ClauseCount.body_exec
#print axioms ClauseCount.body_fields
#print axioms ClauseCount.bodyFuel_bound
#print axioms ClauseCount.run_exec
#print axioms ClauseCount.run_result
#print axioms ClauseCount.run_fuel_bound
#print axioms ClauseCount.count_bound

end PNP.Concrete.NormalizerBlocks
