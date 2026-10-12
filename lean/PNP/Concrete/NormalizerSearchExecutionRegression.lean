import PNP.Concrete.NormalizerSearchExecution
namespace PNP.Concrete.NormalizerBlocks
example : (Search.result (Exploration.encode 0 [] [])).registers.output = Search.answer (.terminal []) := by decide
example : (Search.result (Exploration.encode 1 [[⟨true, 0⟩]] [none])).registers.output =
    Search.answer (.augment 0 [⟨false, 0⟩, ⟨true, 0⟩]) := by decide
example (n : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    (Search.result (Exploration.encode n clauses entries)).registers.output = Search.answer (Search.value n clauses entries) :=
  Search.result_canonical n clauses entries
#print axioms Search.block_exec
#print axioms Search.initial_registers
#print axioms Search.closed_run
#print axioms Search.result_canonical
end PNP.Concrete.NormalizerBlocks
