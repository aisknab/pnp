import PNP.Concrete.NormalizerParentPolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : ParentQuery.sourceSteps input + 1 ≤ ParentQuery.sourceFuel.eval input.length :=
  ParentQuery.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine ParentQuery.program)
      ((BitRegister.CompilerIO.runtimePolynomial 21 ParentQuery.sourceFuel).eval input.length) input = .accept :=
  ParentQuery.polynomial_accepts input
example (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    ParentQuery.polynomial.output (ParentQuery.encode target clauses entries trace) =
      ParentQuery.answer (ParentQuery.value target clauses entries trace) :=
  ParentQuery.polynomial_canonical target clauses entries trace
example : ParentQuery.value ⟨true, 0⟩ [] [none] [(⟨false, 0⟩, none)] = some none := by decide
example : ParentQuery.value ⟨false, 0⟩ [[⟨true, 0⟩]] [none] [(⟨true, 0⟩, some ⟨false, 4⟩)] =
    some (some ⟨true, 0⟩) := by decide
example : ParentQuery.value ⟨false, 0⟩ [[⟨true, 0⟩]] [some 0] [(⟨true, 0⟩, none)] = none := by decide
example : ParentQuery.value ⟨false, 0⟩ [[⟨true, 0⟩], [⟨false, 0⟩]] [none, none]
    [(⟨true, 1⟩, none), (⟨true, 0⟩, none)] = some (some ⟨true, 1⟩) := by decide
example : ParentQuery.value ⟨true, 0⟩ [] [some 1]
    [(⟨false, 0⟩, none), (⟨false, 1⟩, some ⟨true, 7⟩)] = some (some ⟨false, 1⟩) := by decide

#print axioms ParentQuery.block_exec
#print axioms ParentQuery.closed_run
#print axioms ParentQuery.sourceFuel_eval
#print axioms ParentQuery.sourceSteps_bound
#print axioms ParentQuery.padded_run
#print axioms ParentQuery.acceptsWithin
#print axioms ParentQuery.polynomial_program
#print axioms ParentQuery.polynomial_output
#print axioms ParentQuery.polynomial_accepts
#print axioms ParentQuery.polynomial_output_length
#print axioms ParentQuery.polynomial_canonical
#print axioms ParentQuery.machine_canonical

end PNP.Concrete.NormalizerBlocks
