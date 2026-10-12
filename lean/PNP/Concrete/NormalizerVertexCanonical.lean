/-
Copyright (c) 2026 PNP Labs.

Exact bytes for the complete two-kind vertex list. The clause range comes
first, followed by the variable range; arbitrary suffix data cannot change
the constructed list. This is the enumeration input to reachability, not an
assumption that a predecessor trace or reachable set has already been given.
-/

import PNP.Concrete.NormalizerVertexPolynomial

namespace PNP.Concrete.NormalizerBlocks.SearchVertices

open BitRegister Occurrence

def vertices (clauses variables : Nat) : List CNFLiteral :=
  rangeData true clauses 0 ++ rangeData false variables 0

def encodeVertices (values : List CNFLiteral) : BitString :=
  encodeTokenPairs (encodeClauseListTokens (values.map (fun v => [v])) ++ [.finish])

def encodeCounts (clauses variables : Nat) (suffix : BitString) : BitString :=
  TableInit.encodeCount clauses (TableInit.encodeCount variables suffix)

theorem clauseList_append (first second : List (List CNFLiteral)) :
    encodeClauseListTokens (first ++ second) = encodeClauseListTokens first ++ encodeClauseListTokens second := by
  induction first with
  | nil => rfl
  | cons clause rest ih =>
      simp only [List.cons_append, encodeClauseListTokens, ih, List.append_assoc]

theorem encoded_vertices (clauses variables : Nat) :
    encodeVertices (vertices clauses variables) =
      (rangeBits true clauses 0 ++ rangeBits false variables 0) ++ [true, false] := by
  simp only [encodeVertices, vertices, List.map_append, clauseList_append,
    NANDFrontend.encodeTokenPairs_append, ← rangeBits_exact, encodeTokenPairs,
    CNFToken.bits, List.append_nil]

theorem front_canonical_excess (clauses variables : Nat) (suffix : BitString) :
    (frontResult (encodeCounts clauses variables suffix)).excess =
      (rangeBits false variables 0).reverse ++ (rangeBits true clauses 0).reverse := by
  have firstInput : (leftResult (encodeCounts clauses variables suffix)).input =
      TableInit.encodeCount variables suffix :=
    phase_canonical_input true clauses (TableInit.encodeCount variables suffix) _ rfl
  have firstBuffer : (leftResult (encodeCounts clauses variables suffix)).excess =
      (rangeBits true clauses 0).reverse ++ [] :=
    phase_canonical_excess true clauses (TableInit.encodeCount variables suffix) _ rfl
  have secondBuffer := phase_canonical_excess false variables suffix
    (leftResult (encodeCounts clauses variables suffix)) firstInput
  change (phaseResult false (leftResult (encodeCounts clauses variables suffix))).excess = _
  rw [secondBuffer, firstBuffer, List.append_nil]

theorem polynomial_canonical (clauses variables : Nat) (suffix : BitString) :
    polynomial.output (encodeCounts clauses variables suffix) = encodeVertices (vertices clauses variables) := by
  rw [polynomial_output, encoded_vertices]
  change (frontResult (encodeCounts clauses variables suffix)).excess.reverse ++ [true, false] = _
  rw [front_canonical_excess, List.reverse_append, List.reverse_reverse, List.reverse_reverse]

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (clauses variables : Nat) (suffix : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encodeCounts clauses variables suffix).length)
      (encodeCounts clauses variables suffix) = encodeVertices (vertices clauses variables) :=
  (output_projection (encodeCounts clauses variables suffix)).symm.trans
    (polynomial_canonical clauses variables suffix)

theorem rangeData_finRange (tag : Bool) (count index : Nat) :
    rangeData tag count index =
      (List.finRange count).map (fun i => (⟨tag, index + i.val⟩ : CNFLiteral)) := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      rw [rangeData, List.finRange_succ]
      simp only [List.map_cons, List.map_map, Function.comp_def, Fin.val_zero, Nat.add_zero]
      rw [ih]
      apply congrArg (List.cons (⟨tag, index⟩ : CNFLiteral))
      apply congrArg (fun f : Fin count → CNFLiteral => (List.finRange count).map f)
      funext i
      congr 1
      simp only [Fin.val_succ]
      omega

theorem rangeData_length (tag : Bool) (count index : Nat) : (rangeData tag count index).length = count := by
  rw [rangeData_finRange, List.length_map, List.length_finRange]

theorem vertices_length (clauses variables : Nat) : (vertices clauses variables).length = clauses + variables := by
  simp only [vertices, List.length_append, rangeData_length]

end PNP.Concrete.NormalizerBlocks.SearchVertices
