/-
Copyright (c) 2026 PNP Labs.

Ordered predecessor-trace records. Each row stores a signed vertex and an
explicit optional signed predecessor. Parent search ignores the predecessor
value but must consume its complete bytes, preserving the following suffix.
-/

import PNP.Concrete.NormalizerEdgePolynomial
import PNP.Concrete.NormalizerRootKinds

namespace PNP.Concrete.NormalizerBlocks.TraceData

abbrev Row := CNFLiteral × Option CNFLiteral

def vertex (value : CNFLiteral) (suffix : BitString) : BitString :=
  value.positive :: TableInit.encodeCount value.variableIndex suffix
def predecessor (parent : Option CNFLiteral) (suffix : BitString) : BitString :=
  match parent with
  | none => false :: suffix
  | some value => true :: vertex value suffix
def row (entry : Row) (suffix : BitString) : BitString := vertex entry.1 (predecessor entry.2 suffix)
def encode : List Row → BitString
  | [] => []
  | entry :: rest => row entry (encode rest)

def skipParent (input : BitString) : BitString :=
  if input.headD false then (TableInit.readCount input.tail.tail).state.input else input.tail

theorem skipParent_canonical (parent : Option CNFLiteral) (suffix : BitString) :
    skipParent (predecessor parent suffix) = suffix := by
  cases parent with
  | none => rfl
  | some value =>
      simp only [skipParent, predecessor, vertex, List.headD, List.tail_cons, ite_true,
        BatchPacket.header_canonical, TableInit.canonicalHeader]

theorem skipParent_length (input : BitString) : (skipParent input).length ≤ input.length := by
  have tail : input.tail.length ≤ input.length := by
    cases input <;> simp only [List.tail_nil, List.tail_cons, List.length_nil, List.length_cons] <;> omega
  have second := EdgeKinds.tail_length_le input
  have read := Occurrence.header_input_bound input.tail.tail (TableInit.seeded input.tail.tail)
  cases tag : input.headD false <;>
    simp only [skipParent, tag, Bool.false_eq_true, ite_false, ite_true]
  · exact tail
  · exact Nat.le_trans read second

def nodeIndex (input : BitString) : BitString := (TableInit.readCount input.tail).state.target
def node (input : BitString) : CNFLiteral := ⟨input.headD false, (nodeIndex input).length⟩
def next (input : BitString) : BitString := skipParent (TableInit.readCount input.tail).state.input

theorem node_canonical (entry : Row) (suffix : BitString) : node (row entry suffix) = entry.1 := by
  cases entry with
  | mk value parent =>
      cases value with
      | mk tag index =>
          simp only [node, nodeIndex, row, vertex, List.headD, List.tail_cons,
            BatchPacket.header_canonical, TableInit.canonicalHeader, List.length_replicate]

theorem nodeIndex_canonical (entry : Row) (suffix : BitString) :
    nodeIndex (row entry suffix) = List.replicate entry.1.variableIndex true := by
  simp only [nodeIndex, row, vertex, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]

theorem next_canonical (entry : Row) (suffix : BitString) : next (row entry suffix) = suffix := by
  simp only [next, row, vertex, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]
  exact skipParent_canonical entry.2 suffix

theorem next_shorter (input : BitString) (nonempty : input ≠ []) : (next input).length < input.length := by
  have skip := skipParent_length (TableInit.readCount input.tail).state.input
  have read := Occurrence.header_input_bound input.tail (TableInit.seeded input.tail)
  have strict : input.tail.length < input.length := by
    cases input with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest => exact Nat.lt_succ_self _
  exact Nat.lt_of_le_of_lt (Nat.le_trans skip read) strict

theorem nodeIndex_length (input : BitString) : (nodeIndex input).length ≤ 5 * input.length + 6 := by
  have count := TableInit.count_length_bound input.tail
  have tail : input.tail.length ≤ input.length := by
    cases input <;> simp only [List.tail_nil, List.tail_cons, List.length_nil, List.length_cons] <;> omega
  change (TableInit.readCount input.tail).state.target.length ≤ _
  omega

end PNP.Concrete.NormalizerBlocks.TraceData

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

def answer : Option (Option CNFLiteral) → BitString
  | none => [false]
  | some none => [true, false]
  | some (some value) => true :: true :: value.positive :: List.replicate value.variableIndex true

def value (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) : Option (Option CNFLiteral) :=
  if RootKinds.value target entries then some none
  else (trace.find? (fun entry => EdgeKinds.value entry.1 target clauses entries)).map (fun entry => some entry.1)

theorem root_before_edges (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (root : RootKinds.value target entries = true) :
    value target clauses entries trace = some none := by
  rw [value, root]
  rfl

theorem absent_distinct_root : answer none ≠ answer (some none) := by decide

end PNP.Concrete.NormalizerBlocks.ParentQuery
