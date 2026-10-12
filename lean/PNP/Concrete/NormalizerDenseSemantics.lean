/-
Copyright (c) 2026 PNP Labs.

Exact complete dense-clause-list semantics. Each selected index is read
from the original formula, in selected source order, then compacted using
the same variable list. Arbitrary selection lengths and empty clauses are
covered by one theorem, not by fixed schedule prefixes.
-/
import PNP.Concrete.NormalizerDenseLoop

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

def value (formula : List (List CNFLiteral)) (vertices selected : List CNFLiteral) :
    List (List CNFLiteral) :=
  selected.map (fun vertex => CompactClause.value vertices (formula[vertex.variableIndex]?.getD []))
def prefixBits (clauses : List (List CNFLiteral)) : BitString :=
  encodeTokenPairs (encodeClauseListTokens clauses)
theorem prefix_cons (clause : List CNFLiteral) (rest : List (List CNFLiteral)) :
    prefixBits (clause :: rest) = clauseBits clause ++ prefixBits rest := by
  simp only [prefixBits, clauseBits, encodeClauseListTokens, NANDFrontend.encodeTokenPairs_append]
theorem value_cons (formula : List (List CNFLiteral)) (vertices : List CNFLiteral)
    (first : CNFLiteral) (rest : List CNFLiteral) :
    value formula vertices (first :: rest) =
      CompactClause.value vertices (formula[first.variableIndex]?.getD []) ::
        value formula vertices rest := rfl

theorem stepped_cons (r : State) (first : CNFLiteral) (rest : List CNFLiteral)
    (remaining : r.remaining = SearchVertices.encodeVertices (first :: rest)) :
    stepped r = bodyResult r := by
  have bytes := remaining.trans (UnseenData.encoded_cons first rest)
  unfold stepped
  rw [bytes, UnseenData.entry_shape]

theorem step_canonical (r : State) (vertex : CNFLiteral)
    (rest vertices : List CNFLiteral) (formula : List (List CNFLiteral))
    (remaining : r.remaining = SearchVertices.encodeVertices (vertex :: rest))
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (stepped r).remaining = SearchVertices.encodeVertices rest ∧
    (stepped r).core.buffer =
      (clauseBits (CompactClause.value vertices (formula[vertex.variableIndex]?.getD []))).reverse ++
        r.core.buffer := by
  rw [stepped_cons r vertex rest remaining]
  exact body_canonical r vertex rest vertices formula remaining variables original

theorem remaining_nonempty (selected : List CNFLiteral) (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected) : r.remaining ≠ [] := by
  intro empty
  have size := congrArg List.length empty
  rw [remaining, UnseenData.encoded_prefix, List.length_append] at size
  simp only [List.length_cons, List.length_nil] at size
  omega

theorem scan_state_step (fuel : Nat) (r : State) (nonempty : r.remaining ≠ []) :
    (scan (fuel + 1) r).state = (scan fuel (stepped r)).state := by
  cases remaining : r.remaining with
  | nil => exact False.elim (nonempty remaining)
  | cons bit rest => simp only [scan, remaining]

theorem scan_buffer (formula : List (List CNFLiteral)) (vertices selected : List CNFLiteral)
    (fuel : Nat) (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula)
    (enough : r.remaining.length < fuel) :
    (scan fuel r).state.core.buffer =
      (prefixBits (value formula vertices selected)).reverse ++ r.core.buffer := by
  induction selected generalizing fuel r with
  | nil =>
      have nonempty := remaining_nonempty [] r remaining
      change r.remaining = [true,false] at remaining
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have ended : (stepped r).remaining = [] := by
            simp only [stepped, remaining, stopped]
          rw [scan_state_step fuel r nonempty, scan_stopped fuel (stepped r) ended]
          change (stepped r).core.buffer = r.core.buffer
          simp only [stepped, remaining, stopped]
  | cons first selected ih =>
      have nonempty := remaining_nonempty (first :: selected) r remaining
      have canonical := step_canonical r first selected vertices formula remaining variables original
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have enoughNext : (stepped r).remaining.length < fuel :=
            Nat.lt_of_lt_of_le (step_progress r nonempty) (Nat.le_of_lt_succ enough)
          rw [scan_state_step fuel r nonempty,
            ih fuel (stepped r) canonical.1 ((stepped_fields r).2.trans variables)
              ((stepped_fields r).1.trans original) enoughNext,
            canonical.2, value_cons, prefix_cons, List.reverse_append, List.append_assoc]

theorem whole_buffer (formula : List (List CNFLiteral)) (vertices selected : List CNFLiteral)
    (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (whole r).state.core.buffer =
      (prefixBits (value formula vertices selected)).reverse ++ r.core.buffer :=
  scan_buffer formula vertices selected _ r remaining variables original (Nat.lt_succ_self _)

theorem prefix_data (clauses : List (List CNFLiteral)) :
    prefixBits clauses ++ [true,false] = GraphQuery.clauseData clauses := by
  simp only [prefixBits, GraphQuery.clauseData, NANDFrontend.encodeTokenPairs_append,
    encodeTokenPairs, CNFToken.bits, List.append_nil]

end PNP.Concrete.NormalizerBlocks.DenseClauses
