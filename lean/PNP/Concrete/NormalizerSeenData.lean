/-
Copyright (c) 2026 PNP Labs.

Seen-variable tables derived from actual predecessor-trace nodes. Clause
vertices contribute absent entries. Predecessor metadata never contributes
a reached variable. The source trace order is preserved.
-/
import PNP.Concrete.NormalizerPathPolynomial

namespace PNP.Concrete.NormalizerBlocks.SeenTrace

def entry (vertex : CNFLiteral) : Option Nat :=
  if vertex.positive then none else some vertex.variableIndex
def value (trace : List TraceData.Row) : MatchingTable.Entries := trace.map (fun row => entry row.1)
def entryBytes (entry : Option Nat) : BitString :=
  encodeTokenPairs (encodeClauseTokens (MatchingTable.entryClause entry))
def bytes (entries : MatchingTable.Entries) : BitString :=
  encodeTokenPairs (encodeClauseListTokens (MatchingTable.clauses entries))

theorem bytes_cons (entry : Option Nat) (rest : MatchingTable.Entries) :
    bytes (entry :: rest) = entryBytes entry ++ bytes rest := by
  simp only [bytes, entryBytes, MatchingTable.clauses, List.map_cons, encodeClauseListTokens,
    NANDFrontend.encodeTokenPairs_append]

theorem encode_bytes (entries : MatchingTable.Entries) :
    MatchingTable.encode entries = bytes entries ++ [true, false] := by
  rw [MatchingTable.encode, NANDFrontend.encodeTokenPairs_append]
  rfl

theorem entryBytes_none : entryBytes none = [false, true, true, false] := rfl

theorem entryBytes_some (index : Nat) : entryBytes (some index) = SearchVertices.entryBits true index :=
  (SearchVertices.entryBits_exact true index).symm

theorem same_nodes (first second : List TraceData.Row)
    (nodes : first.map Prod.fst = second.map Prod.fst) : value first = value second := by
  have mapped := congrArg (List.map entry) nodes
  simpa only [List.map_map, Function.comp_def, value] using mapped

end PNP.Concrete.NormalizerBlocks.SeenTrace
