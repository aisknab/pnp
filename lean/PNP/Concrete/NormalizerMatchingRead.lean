/-
Copyright (c) 2026 PNP Labs.

Closed indexed matching-table reads. Clause selection and value decoding are
composed as actual polynomial machines. Exact output returns the stored value
at the queried row, including absent and out-of-range entries. The full
matching producer must still construct the table and query packet internally.
-/

import PNP.Concrete.NormalizerMatchingValueCanonical

namespace PNP.Concrete.NormalizerBlocks.MatchingRead

def polynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose ClauseQuery.polynomial MatchingValue.polynomial

theorem polynomial_program :
    polynomial.program = .compose ClauseQuery.polynomial.program MatchingValue.polynomial.program := rfl

private theorem output_projection (input : BitString) :
    polynomial.output input =
      (PolynomialTimeFunction.compose ClauseQuery.polynomial MatchingValue.polynomial).output input := rfl

theorem polynomial_output (input : BitString) :
    polynomial.output input = MatchingValue.polynomial.output (ClauseQuery.polynomial.output input) := by
  rw [output_projection, PolynomialTimeFunction.compose_output]

def encodeQuery (index : Nat) (entries : MatchingTable.Entries) : BitString :=
  ClauseQuery.encodeQuery 0 index (MatchingTable.clauses entries)

theorem polynomial_canonical (index : Nat) (entries : MatchingTable.Entries) :
    polynomial.output (encodeQuery index entries) = TableOwner.answer (MatchingTable.read entries index) := by
  rw [polynomial_output]
  change MatchingValue.polynomial.output
    (ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 0 index (MatchingTable.clauses entries))) = _
  rw [MatchingTable.read_query, MatchingValue.polynomial_canonical]

def decoderRawRefinement : FunctionProgram.RawRefinement MatchingValue.polynomial.program := by
  rw [MatchingValue.polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (BitRegister.CompilerIO.rawMachine MatchingValue.program)
    (BitRegister.CompilerIO.runtimePolynomial 9 MatchingValue.sourceFuel)

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.compose ClauseQuery.queryRawRefinement decoderRawRefinement

theorem machine_output (input : BitString) :
    machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input =
      polynomial.output input :=
  rawRefinement.output_eq input (polynomial.haltsWithin input)

theorem machine_canonical (index : Nat) (entries : MatchingTable.Entries) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size (encodeQuery index entries))) (encodeQuery index entries) =
        TableOwner.answer (MatchingTable.read entries index) := by
  rw [machine_output, polynomial_canonical]

theorem machine_halts (input : BitString) :
    boundedDecide rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  rawRefinement.haltsWithin input (polynomial.haltsWithin input)

theorem machine_output_size (input : BitString) :
    BitString.size (machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input) ≤
      polynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le polynomial rawRefinement input

end PNP.Concrete.NormalizerBlocks.MatchingRead
