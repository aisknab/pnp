import PNP.Concrete.NANDFrontendData

namespace PNP.Concrete.NANDFrontend

example : sourceIndex 3 (.input 2) = 2 := rfl
example : sourceIndex 3 (.constant false) = 3 := rfl
example : sourceIndex 3 (.constant true) = 4 := rfl
example : sourceIndex 3 (.gate 2) = 7 := rfl
example : unitClause 2 false = [⟨false, 2⟩, ⟨false, 2⟩, ⟨false, 2⟩] := rfl
example : (formula ⟨0, [], .constant true⟩).variableCount = 2 := rfl
example : (formula ⟨0, [], .constant true⟩).clauses.length = 3 := rfl
example (circuit : LockedNAND.RawCircuit) :
    (formula circuit).clauses.length = 3 * circuit.gates.length + 3 := formula_clauses_length circuit
example (positive : Bool) (index : Nat) :
    literalBits positive index = encodeTokenPairs (encodeLiteralTokens ⟨positive, index⟩) :=
  literalBits_exact positive index
example (first second third : CNFLiteral) :
    threeBits first second third = encodeTokenPairs (encodeClauseTokens [first, second, third]) :=
  threeBits_exact first second third
example (inputs ordinal : Nat) (left right : LockedNAND.RawSource) :
    gateClauses inputs ordinal ⟨left, right⟩ =
      [[⟨false, sourceIndex inputs left⟩, ⟨false, sourceIndex inputs right⟩, ⟨false, inputs + 2 + ordinal⟩],
       [⟨true, sourceIndex inputs left⟩, ⟨true, inputs + 2 + ordinal⟩, ⟨true, inputs + 2 + ordinal⟩],
       [⟨true, sourceIndex inputs right⟩, ⟨true, inputs + 2 + ordinal⟩, ⟨true, inputs + 2 + ordinal⟩]] := rfl

#print axioms encodeTokenPairs_append
#print axioms twiceUnary_succ
#print axioms unaryTokenBits
#print axioms literalBits_exact
#print axioms literalBits_length
#print axioms literalBits_reverse
#print axioms threeBits_exact
#print axioms threeBits_length
#print axioms gateClauses_length
#print axioms gatesClauses_length
#print axioms formula_width
#print axioms formula_clauses_length

end PNP.Concrete.NANDFrontend
