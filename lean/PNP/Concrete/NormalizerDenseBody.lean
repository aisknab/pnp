/-
Copyright (c) 2026 PNP Labs.

Complete read-and-compact work for one actual selected clause. Every byte
is derived from the original formula and selected-variable list. The bound
is independent of accumulated output, enabling a polynomial whole-list loop.
-/
import PNP.Concrete.NormalizerDenseAppend

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

def body : Block 16 := .seq readEntry (.seq query appendClause)
def bodyResult (r : State) : State := appended (queried (entryRead r))
def bodyFuel (r : State) : Nat :=
  readFuel r + (queryFuel (entryRead r) + appendFuel (queried (entryRead r)))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (readEntry_exec r) (Exec.seq (query_exec (entryRead r)) (appendClause_exec _))

theorem body_fields (r : State) :
    (bodyResult r).formula = r.formula ∧
    (bodyResult r).remaining = UnseenData.next r.remaining ∧
    (bodyResult r).core.variables = r.core.variables := by
  have read := read_fields r
  have queried := queried_fields (entryRead r)
  have appended := appended_fields (DenseClauses.queried (entryRead r))
  exact ⟨appended.1.trans (queried.1.trans read.2.2.1),
    appended.2.1.trans (queried.2.1.trans read.2.1),
    appended.2.2.2.trans (queried.2.2.2.1.trans read.2.2.2.1)⟩

def bodyBound : NatPolynomial :=
  .add (.mul (.linear 1534 2114) (.linear 210 286)) (.linear 211 335)
theorem bodyBound_eval (bound : Nat) :
    bodyBound.eval bound = (1534 * bound + 2114) * (210 * bound + 286) + (211 * bound + 335) := rfl

theorem bodyFuel_bound (r : State) (bound : Nat)
    (remaining : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    bodyFuel r ≤ bodyBound.eval bound := by
  have read := readFuel_bound r
  have index := read_index_bound r
  have query := queryFuel_bound (entryRead r)
  have output := query_output_bound (entryRead r)
  rw [(read_fields r).2.2.1] at query output
  have append := appendFuel_bound (queried (entryRead r))
  rw [(queried_fields (entryRead r)).2.2.2.1, (read_fields r).2.2.2.1] at append
  have outputSize : (queried (entryRead r)).registers.output.length ≤ 210 * bound + 285 := by omega
  have first : 7 * (queried (entryRead r)).registers.output.length +
      64 * r.core.variables.length + 119 ≤ 1534 * bound + 2114 := by omega
  have second : (queried (entryRead r)).registers.output.length + 1 ≤ 210 * bound + 286 := by omega
  have product := Nat.mul_le_mul first second
  rw [bodyBound_eval]
  unfold bodyFuel appendBound at *
  omega

theorem body_canonical (r : State) (vertex : CNFLiteral)
    (rest vertices : List CNFLiteral) (formula : List (List CNFLiteral))
    (remaining : r.remaining = SearchVertices.encodeVertices (vertex :: rest))
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (bodyResult r).remaining = SearchVertices.encodeVertices rest ∧
    (bodyResult r).core.buffer =
      (clauseBits (CompactClause.value vertices (formula[vertex.variableIndex]?.getD []))).reverse ++
        r.core.buffer := by
  have read := read_canonical r vertex rest remaining
  have query := query_canonical (entryRead r) vertex.variableIndex formula read.1
    ((read_fields r).2.2.1.trans original)
  have buffer := appended_buffer (queried (entryRead r)) vertices
    (formula[vertex.variableIndex]?.getD []) query
    ((queried_fields (entryRead r)).2.2.2.1.trans
      ((read_fields r).2.2.2.1.trans variables))
  rw [(queried_fields (entryRead r)).2.2.2.2, (read_fields r).2.2.2.2] at buffer
  exact ⟨(appended_fields (queried (entryRead r))).2.1.trans
    ((queried_fields (entryRead r)).2.1.trans read.2),buffer⟩

end PNP.Concrete.NormalizerBlocks.DenseClauses
