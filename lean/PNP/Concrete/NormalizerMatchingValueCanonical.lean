/-
Copyright (c) 2026 PNP Labs.

Exact absence/value output for a selected matching-table entry. The decoder
returns the actual unbounded unary value, rather than an existence bit or
an owner index. The surrounding indexed selector is composed separately.
-/

import PNP.Concrete.NormalizerMatchingValuePolynomial

namespace PNP.Concrete.NormalizerBlocks.MatchingValue

open BitRegister Occurrence

theorem present_encoding (value : Nat) :
    Occurrence.encodeQuery 0 [⟨true, value⟩] =
      false :: true :: true :: (List.replicate (2 * value) true ++ [false, false, true, false]) := by
  simp only [Occurrence.encodeQuery, List.replicate_zero, List.nil_append,
    encodeLiteralListTokens, List.append_nil, NANDFrontend.encodeTokenPairs_append]
  rw [← NANDFrontend.literalBits_exact]
  simp only [NANDFrontend.literalBits, encodeTokenPairs, CNFToken.bits,
    List.append_assoc, List.cons_append, List.nil_append]

theorem polynomial_canonical (value : Option Nat) :
    polynomial.output (Occurrence.encodeQuery 0 (MatchingTable.entryClause value)) = TableOwner.answer value := by
  cases value with
  | none =>
      rw [polynomial_output]
      rfl
  | some value =>
      rw [polynomial_output]
      change (result (Occurrence.encodeQuery 0 [⟨true,value⟩])).output = _
      rw [present_encoding]
      change normalizeWord
        ((scan (List.replicate (2 * value) true ++ false :: [false, true, false])
          {seeded (false :: true :: true :: (List.replicate (2 * value) true ++ [false,false,true,false]))
            with output := [true]}).state.output) = true :: List.replicate value true
      rw [scan_true_pairs]
      change normalizeWord (List.replicate value true ++ [true]) = true :: List.replicate value true
      rw [← List.replicate_succ', List.replicate_succ]
      rfl

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (value : Option Nat) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval
        (Occurrence.encodeQuery 0 (MatchingTable.entryClause value)).length)
      (Occurrence.encodeQuery 0 (MatchingTable.entryClause value)) = TableOwner.answer value :=
  (output_projection (Occurrence.encodeQuery 0 (MatchingTable.entryClause value))).symm.trans
    (polynomial_canonical value)

end PNP.Concrete.NormalizerBlocks.MatchingValue
