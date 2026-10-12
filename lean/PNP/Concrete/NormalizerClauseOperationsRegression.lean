import PNP.Concrete.NormalizerClauseOperations

namespace PNP.Concrete.NormalizerBlocks

open Occurrence

example (value : CNFToken) (r : Registers) :
    Exec (ClauseQuery.token value) r.store (ClauseQuery.tokenResult value r).fuel
      (ClauseQuery.tokenResult value r).state.store := ClauseQuery.token_exec value r
example (value : CNFToken) (r : Registers) : (ClauseQuery.tokenResult value r).fuel ≤ 3 :=
  ClauseQuery.token_fuel_bound value r
example : (ClauseQuery.tokenResult .sep ⟨[], [], [], [], [], [], [true], [], []⟩).state.mode = [true] := rfl
example : (ClauseQuery.tokenResult .sep ⟨[], [], [true, true], [], [], [], [true], [], []⟩).state.remaining = [true] := rfl
example : (ClauseQuery.tokenResult .f ⟨[], [], [], [true], [], [true], [true], [], []⟩).state.excess = [false, false, true] := rfl
example : (ClauseQuery.tokenResult .finish ⟨[], [], [], [], [], [true], [true], [], []⟩).state.active = [] := rfl
example : (ClauseQuery.tokenResult .finish ⟨[], [], [], [], [], [], [true], [], []⟩).state.active = [true] := rfl

#print axioms ClauseQuery.emit_exec
#print axioms ClauseQuery.separator_exec
#print axioms ClauseQuery.token_exec
#print axioms ClauseQuery.token_fuel_bound
#print axioms ClauseQuery.token_input
#print axioms ClauseQuery.token_result_input

end PNP.Concrete.NormalizerBlocks
