import PNP.Concrete.NormalizerParentLoader

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : ParentQuery.loaderFuel input ≤ 70 * input.length + 120 := ParentQuery.loaderFuel_bound input
example (input : BitString) : (ParentQuery.loaded input).pending.length ≤ input.length := (ParentQuery.loaded_size input).2.2.2
example (v : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    (ParentQuery.loaded (ParentQuery.encode v clauses entries trace)).pending = TraceData.encode trace :=
  (ParentQuery.loaded_canonical v clauses entries trace).2
example (v : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    ParentQuery.Canonical (ParentQuery.loaded (ParentQuery.encode v clauses entries trace)) v clauses entries :=
  (ParentQuery.loaded_canonical v clauses entries trace).1

#print axioms ParentQuery.tags_exec
#print axioms ParentQuery.saveTarget_exec
#print axioms ParentQuery.saveFormula_exec
#print axioms ParentQuery.saveMatching_exec
#print axioms ParentQuery.saveTrace_exec
#print axioms ParentQuery.loader_exec
#print axioms ParentQuery.loader_cursors
#print axioms ParentQuery.loaderFuel_bound
#print axioms ParentQuery.loaded_size
#print axioms ParentQuery.loaded_canonical

end PNP.Concrete.NormalizerBlocks
