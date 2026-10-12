import PNP.Concrete.NormalizerClauseScan

namespace PNP.Concrete.NormalizerBlocks

open Occurrence

example (r : Registers) :
    Exec ClauseQuery.loop r.store (ClauseQuery.queryResult r).fuel (ClauseQuery.queryResult r).state.store :=
  ClauseQuery.query_exec r
example (r : Registers) :
    (ClauseQuery.queryResult r).fuel ≤ 8 * (r.input.length + 1) + 1 := ClauseQuery.query_fuel_bound r
example (r : Registers) : (ClauseQuery.queryResult r).state.active = [] := ClauseQuery.query_stopped r
example : (ClauseQuery.pairResult ⟨[false, true], [], [], [], [], [], [true], [], []⟩).state.mode = [true] := rfl
example : (ClauseQuery.queryResult
    ⟨encodeTokenPairs (encodeClauseListTokens [[], [⟨true, 0⟩]] ++ [.finish]),
      [], [true], [], [], [], [true], [], []⟩).state.excess = [false, false, true, true] := rfl
example : (ClauseQuery.queryResult
    ⟨encodeTokenPairs (encodeClauseListTokens [[], [⟨true, 0⟩]] ++ [.finish]),
      [], [true, true], [], [], [], [true], [], []⟩).state.excess = [] := rfl

#print axioms ClauseQuery.pair_exec
#print axioms ClauseQuery.pair_fuel_bound
#print axioms ClauseQuery.pair_progress
#print axioms ClauseQuery.scan_exec
#print axioms ClauseQuery.scan_fuel_bound
#print axioms ClauseQuery.scan_stopped
#print axioms ClauseQuery.query_exec
#print axioms ClauseQuery.query_fuel_bound
#print axioms ClauseQuery.query_stopped

end PNP.Concrete.NormalizerBlocks
