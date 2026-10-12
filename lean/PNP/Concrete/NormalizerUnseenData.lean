/-
Copyright (c) 2026 PNP Labs.

Exact ordered-vertex byte layout for extraction. This is the existing
singleton-clause encoding, not the distinct predecessor-trace encoding.
The verified true-pair scanner reads each arbitrary unary index.
-/

import PNP.Concrete.NormalizerEligibilityPolynomial

namespace PNP.Concrete.NormalizerBlocks.UnseenData

open Occurrence

def entry (vertex : CNFLiteral) : BitString :=
  SearchVertices.entryBits vertex.positive vertex.variableIndex
def prefixBits : List CNFLiteral → BitString
  | [] => []
  | first :: rest => entry first ++ prefixBits rest

theorem entry_shape (vertex : CNFLiteral) (suffix : BitString) :
    entry vertex ++ suffix =
      false :: true :: vertex.positive :: vertex.positive ::
        (List.replicate (2 * vertex.variableIndex) true ++ false :: false :: true :: false :: suffix) := by
  simp only [entry, SearchVertices.entryBits, NANDFrontend.literalBits, List.append_assoc,
    List.cons_append, List.nil_append]

theorem encoded_cons (vertex : CNFLiteral) (rest : List CNFLiteral) :
    SearchVertices.encodeVertices (vertex :: rest) = entry vertex ++ SearchVertices.encodeVertices rest := by
  simp only [SearchVertices.encodeVertices, List.map_cons, encodeClauseListTokens, List.append_assoc,
    NANDFrontend.encodeTokenPairs_append, entry, SearchVertices.entryBits_exact]

theorem encoded_prefix (vertices : List CNFLiteral) :
    SearchVertices.encodeVertices vertices = prefixBits vertices ++ [true, false] := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih => rw [encoded_cons, ih, prefixBits, List.append_assoc]

theorem prefix_append (first second : List CNFLiteral) :
    prefixBits (first ++ second) = prefixBits first ++ prefixBits second := by
  induction first with
  | nil => rfl
  | cons vertex rest ih => simp only [List.cons_append, prefixBits, ih, List.append_assoc]

def tail4 (input : BitString) : BitString := input.tail.tail.tail.tail
theorem tail4_le (input : BitString) : (tail4 input).length ≤ input.length :=
  Nat.le_trans (EdgeKinds.tail_length_le input.tail.tail) (EdgeKinds.tail_length_le input)
theorem tail4_shorter (input : BitString) (nonempty : input ≠ []) : (tail4 input).length < input.length := by
  have third := EdgeKinds.tail_length_le input.tail
  have fourth := ParentQuery.input_tail_bound input.tail.tail.tail
  have first : input.tail.length < input.length := by
    cases input with
    | nil => exact False.elim (nonempty rfl)
    | cons bit rest => exact Nat.lt_succ_self _
  change input.tail.tail.tail.tail.length < _
  omega

theorem scan_input_bound (input : BitString) (r : Registers) :
    (MatchingValue.scan input r).state.input.length ≤ input.length := by
  match input with
  | [] => exact Nat.le_refl _
  | false :: rest => exact Nat.le_refl _
  | [true] => change 0 ≤ 1; decide
  | true :: false :: rest => change (false :: rest).length ≤ (true :: false :: rest).length; exact Nat.le_succ _
  | true :: true :: rest =>
      have bound := scan_input_bound rest {r with output := true :: r.output}
      simp only [MatchingValue.scan, List.length_cons]
      omega
termination_by input.length

theorem scan_output_bound (input : BitString) (r : Registers) :
    (MatchingValue.scan input r).state.output.length ≤ r.output.length + input.length := by
  match input with
  | [] | false :: _ | [true] | true :: false :: _ =>
      simp only [MatchingValue.scan, List.length_nil, List.length_cons]
      omega
  | true :: true :: rest =>
      have bound := scan_output_bound rest {r with output := true :: r.output}
      simp only [List.length_cons] at bound
      simp only [MatchingValue.scan, List.length_cons]
      omega
termination_by input.length

theorem scan_true_pairs_input (count : Nat) (suffix : BitString) (r : Registers) :
    (MatchingValue.scan (List.replicate (2 * count) true ++ false :: suffix) r).state.input = false :: suffix := by
  induction count generalizing r with
  | zero => rfl
  | succ count ih =>
      rw [NANDFrontend.twiceUnary_succ]
      simpa only [List.cons_append, MatchingValue.scan] using ih {r with output := true :: r.output}

def parsed (input : BitString) : Result :=
  MatchingValue.scan (tail4 input) (initialRegisters (tail4 input))
def index (input : BitString) : BitString := (parsed input).state.output
def next (input : BitString) : BitString := tail4 (parsed input).state.input
def tag (input : BitString) : Bool := ForwardEdge.present input.tail.tail

theorem index_bound (input : BitString) : (index input).length ≤ input.length := by
  have read := scan_output_bound (tail4 input) (initialRegisters (tail4 input))
  change (index input).length ≤ 0 + (tail4 input).length at read
  have tail := tail4_le input
  omega

theorem next_shorter (input : BitString) (nonempty : input ≠ []) : (next input).length < input.length := by
  have skip := tail4_le (parsed input).state.input
  have read := scan_input_bound (tail4 input) (initialRegisters (tail4 input))
  exact Nat.lt_of_le_of_lt (Nat.le_trans skip read) (tail4_shorter input nonempty)

theorem parsed_canonical (vertex : CNFLiteral) (suffix : BitString) :
    index (entry vertex ++ suffix) = List.replicate vertex.variableIndex true ∧
      next (entry vertex ++ suffix) = suffix ∧ tag (entry vertex ++ suffix) = vertex.positive := by
  rw [entry_shape]
  constructor
  · change (MatchingValue.scan (List.replicate (2 * vertex.variableIndex) true ++ false :: false :: true :: false :: suffix)
      (initialRegisters _)).state.output = _
    rw [MatchingValue.scan_true_pairs]
    exact List.append_nil _
  · constructor
    · change tail4 (MatchingValue.scan (List.replicate (2 * vertex.variableIndex) true ++ false :: false :: true :: false :: suffix)
        (initialRegisters _)).state.input = _
      rw [scan_true_pairs_input]
      rfl
    · rfl

end PNP.Concrete.NormalizerBlocks.UnseenData

namespace PNP.Concrete.NormalizerBlocks.Extraction

abbrev Found := (CNFLiteral × Option CNFLiteral) × List CNFLiteral

def value (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) : List CNFLiteral → Option Found
  | [] => none
  | vertex :: rest =>
      match Eligibility.value vertex clauses entries trace with
      | some parent => some ((vertex, parent), rest)
      | none => (value clauses entries trace rest).map (fun found => (found.1, vertex :: found.2))

def answer : Option Found → BitString
  | none => [false]
  | some found => true :: TraceData.row found.1 (SearchVertices.encodeVertices found.2)

end PNP.Concrete.NormalizerBlocks.Extraction
