/-
Copyright (c) 2026 PNP Labs.

Concrete matching-relation query. A complete indexed table query determines
whether its actual stored value equals the requested variable. This is the
reverse alternating-edge condition and the exclusion test for a forward
incidence edge, not a complete graph traversal or supplied edge predicate.
-/

import PNP.Concrete.NormalizerMatchingRoot

namespace PNP.Concrete.NormalizerBlocks.MatchingRelation

theorem entry_matches (entry : Option Nat) (value : Nat) :
    ((MatchingTable.entryClause entry).find? (fun literal => literal.variableIndex == value)).isSome =
      (entry == some value) := by
  cases entry with
  | none => rfl
  | some previous =>
      simp only [MatchingTable.entryClause, List.find?_cons, List.find?_nil, Option.some_beq_some]
      cases same : previous == value <;> rfl

def polynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose ClauseQuery.occurrencePolynomial (BooleanHead.polynomial true)

theorem polynomial_program :
    polynomial.program = .compose ClauseQuery.occurrencePolynomial.program (BooleanHead.polynomial true).program := rfl

private theorem output_projection (input : BitString) :
    polynomial.output input =
      (PolynomialTimeFunction.compose ClauseQuery.occurrencePolynomial (BooleanHead.polynomial true)).output input := rfl

theorem polynomial_output (input : BitString) :
    polynomial.output input = (BooleanHead.polynomial true).output (ClauseQuery.occurrencePolynomial.output input) := by
  rw [output_projection, PolynomialTimeFunction.compose_output]

def encodeQuery (value index : Nat) (entries : MatchingTable.Entries) : BitString :=
  ClauseQuery.encodeQuery value index (MatchingTable.clauses entries)

theorem polynomial_canonical (value index : Nat) (entries : MatchingTable.Entries) :
    polynomial.output (encodeQuery value index entries) = [MatchingTable.read entries index == some value] := by
  rw [polynomial_output]
  change (BooleanHead.polynomial true).output
    (ClauseQuery.occurrencePolynomial.output (ClauseQuery.encodeQuery value index (MatchingTable.clauses entries))) = _
  rw [ClauseQuery.occurrencePolynomial_canonical, BooleanHead.presence_answer, MatchingTable.clauses_read, entry_matches]

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.compose ClauseQuery.occurrenceRawRefinement (BooleanHead.rawRefinement true)

theorem machine_output (input : BitString) :
    machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input =
      polynomial.output input :=
  rawRefinement.output_eq input (polynomial.haltsWithin input)

theorem machine_canonical (value index : Nat) (entries : MatchingTable.Entries) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size (encodeQuery value index entries)))
      (encodeQuery value index entries) = [MatchingTable.read entries index == some value] := by
  rw [machine_output, polynomial_canonical]

theorem machine_halts (input : BitString) :
    boundedDecide rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  rawRefinement.haltsWithin input (polynomial.haltsWithin input)

theorem machine_output_size (input : BitString) :
    BitString.size (machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input) ≤
      polynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le polynomial rawRefinement input

end PNP.Concrete.NormalizerBlocks.MatchingRelation
