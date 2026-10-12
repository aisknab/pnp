/-
Copyright (c) 2026 PNP Labs.

Exact path bytes and suffix-only predecessor semantics. A path is a list
of signed vertices. A missing older predecessor returns none, even if a
matching node occurred earlier in the newer part of the trace.
-/

import PNP.Concrete.NormalizerExplorationPolynomial

namespace PNP.Concrete.NormalizerBlocks.TraceMember

theorem same_true_iff (first second : CNFLiteral) : same first second = true ↔ first = second := by
  constructor
  · intro h
    have fields : (first.variableIndex == second.variableIndex) = true ∧
        (first.positive == second.positive) = true := by
      cases indexTest : first.variableIndex == second.variableIndex with
      | false =>
          have impossible : false = true := by simpa only [same, indexTest, Bool.false_and] using h
          cases impossible
      | true =>
          cases tagTest : first.positive == second.positive with
          | false =>
              have impossible : false = true := by simpa only [same, indexTest, tagTest, Bool.true_and] using h
              cases impossible
          | true => exact ⟨rfl, rfl⟩
    have index : first.variableIndex = second.variableIndex := beq_iff_eq.mp fields.1
    have tag : first.positive = second.positive := beq_iff_eq.mp fields.2
    cases first
    cases second
    cases index
    cases tag
    rfl
  · intro eq
    subst second
    have index : (first.variableIndex == first.variableIndex) = true := beq_iff_eq.mpr rfl
    have tag : (first.positive == first.positive) = true := beq_iff_eq.mpr rfl
    rw [same, index, tag]
    rfl

end PNP.Concrete.NormalizerBlocks.TraceMember

namespace PNP.Concrete.NormalizerBlocks.PathData

def encode : List CNFLiteral → BitString
  | [] => []
  | first :: rest => TraceData.vertex first (encode rest)

def answer : Option (List CNFLiteral) → BitString
  | none => [false]
  | some vertices => true :: encode vertices

theorem vertex_append (vertex : CNFLiteral) (first second : BitString) :
    TraceData.vertex vertex (first ++ second) = TraceData.vertex vertex first ++ second := by
  simp only [TraceData.vertex, TableInit.encodeCount, List.cons_append, List.append_assoc]

theorem encode_append (first second : List CNFLiteral) :
    encode (first ++ second) = encode first ++ encode second := by
  induction first with
  | nil => rfl
  | cons vertex rest ih =>
      rw [List.cons_append, encode, encode, ih, vertex_append]

theorem vertex_reverse (vertex : CNFLiteral) (buffer : BitString) :
    (TraceData.vertex vertex []).reverse ++ buffer =
      false :: (List.replicate vertex.variableIndex true ++ (vertex.positive :: buffer)) := by
  simp only [TraceData.vertex, TableInit.encodeCount, List.reverse_cons, List.reverse_append,
    List.reverse_replicate, List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]

theorem encode_cons_reverse (vertex : CNFLiteral) (rest : List CNFLiteral) :
    (encode (vertex :: rest)).reverse = (encode rest).reverse ++ (TraceData.vertex vertex []).reverse := by
  have split : encode (vertex :: rest) = TraceData.vertex vertex [] ++ encode rest := by
    exact vertex_append vertex [] (encode rest)
  rw [split, List.reverse_append]

theorem answer_none_distinct (vertices : List CNFLiteral) : answer none ≠ answer (some vertices) := by
  intro same
  have head : false = true := List.cons.inj same |>.1
  cases head

end PNP.Concrete.NormalizerBlocks.PathData

namespace PNP.Concrete.NormalizerBlocks.TracePath

def value : List TraceData.Row → CNFLiteral → Option (List CNFLiteral)
  | [], _ => none
  | (vertex, parent) :: rest, target =>
      if TraceMember.same vertex target then
        match parent with
        | none => some [target]
        | some next => (value rest next).map (List.cons target)
      else value rest target

end PNP.Concrete.NormalizerBlocks.TracePath
