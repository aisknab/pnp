import PNP.Concrete.NormalizerSelectedFoldCall

namespace PNP.Concrete.NormalizerBlocks

example (op : SelectedFold.Operation) (r : DenseClauses.State) :
    Exec (SelectedFold.call op) r.store (SelectedFold.callSteps op r) (SelectedFold.called op r).store :=
  SelectedFold.call_exec op r

example (op : SelectedFold.Operation) (r : DenseClauses.State) (bound : Nat)
    (bounded : r.store.Bounded bound) :
    SelectedFold.callSteps op r ≤ (SelectedFold.callBound op).eval bound :=
  SelectedFold.callSteps_bound op r bound bounded

example (output : CNFLiteral → BitString) (first : CNFLiteral) (rest : List CNFLiteral) :
    SelectedFold.prefixBits output (first :: rest) = output first ++ SelectedFold.prefixBits output rest :=
  SelectedFold.prefix_cons output first rest

#print axioms SelectedFold.step_canonical
#print axioms SelectedFold.scan_buffer
#print axioms SelectedFold.front_exec
#print axioms SelectedFold.front_buffer
#print axioms SelectedFold.call_exec
#print axioms SelectedFold.called_fields
#print axioms SelectedFold.called_output
#print axioms SelectedFold.callSteps_bound

end PNP.Concrete.NormalizerBlocks
