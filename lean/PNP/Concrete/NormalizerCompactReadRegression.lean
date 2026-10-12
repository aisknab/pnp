import PNP.Concrete.NormalizerCompactRead

namespace PNP.Concrete.NormalizerBlocks
open Occurrence

example (r : CompactClause.State) (literal : CNFLiteral) (suffix : BitString)
    (pending : r.pending =
      NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) :
    (CompactClause.literalRead r).pending = suffix :=
  (CompactClause.read_canonical r literal suffix pending).2.1

example (r : CompactClause.State) :
    (CompactClause.literalRead r).variables = r.variables ∧
      (CompactClause.literalRead r).buffer = r.buffer :=
  (CompactClause.read_fields r).2.2.2

example : CompactClause.next [true] = [] := rfl

example :
    CompactClause.index (NANDFrontend.literalBits false 3 ++ [true,false]) =
      [true,true,true] :=
  (CompactClause.parsed_canonical ⟨false,3⟩ [true,false]).1

#print axioms CompactClause.index_bound
#print axioms CompactClause.next_shorter
#print axioms CompactClause.parsed_canonical
#print axioms CompactClause.readLiteral_exec
#print axioms CompactClause.readFuel_bound
#print axioms CompactClause.read_fields
#print axioms CompactClause.read_progress
#print axioms CompactClause.read_canonical

end PNP.Concrete.NormalizerBlocks
