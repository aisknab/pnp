/-
Copyright (c) 2026 PNP Labs.

Exact all-literal semantics for the complete compaction loop. The source
clause may have arbitrary length, repeated variables or either polarity.
The result is the ordered filter-map, not a bounded set of sample clauses.
-/
import PNP.Concrete.NormalizerCompactLoop

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

def bits (literals : List CNFLiteral) : BitString :=
  encodeTokenPairs (encodeLiteralListTokens literals)
def value (vertices literals : List CNFLiteral) : List CNFLiteral :=
  literals.filterMap (compactLiteral vertices)

theorem bits_cons (literal : CNFLiteral) (rest : List CNFLiteral) :
    bits (literal :: rest) =
      NANDFrontend.literalBits literal.positive literal.variableIndex ++ bits rest := by
  cases literal with
  | mk positive index =>
      simp only [bits, encodeLiteralListTokens, NANDFrontend.encodeTokenPairs_append,
        NANDFrontend.literalBits_exact]

theorem value_bits_cons (vertices : List CNFLiteral) (literal : CNFLiteral) (rest : List CNFLiteral) :
    bits (value vertices (literal :: rest)) =
      literalOutput (compactLiteral vertices literal) ++ bits (value vertices rest) := by
  cases found : compactLiteral vertices literal <;>
    simp only [value, List.filterMap_cons, found, literalOutput, bits_cons, List.nil_append]

theorem pending_nonempty (literals : List CNFLiteral) (r : State)
    (pending : r.pending = bits literals ++ [true,false]) : r.pending ≠ [] := by
  intro empty
  have size := congrArg List.length empty
  rw [pending, List.length_append] at size
  simp only [List.length_cons, List.length_nil] at size
  omega

theorem scan_state_step (fuel : Nat) (r : State) (nonempty : r.pending ≠ []) :
    (scan (fuel + 1) r).state = (scan fuel (stepped r)).state := by
  cases pending : r.pending with
  | nil => exact False.elim (nonempty pending)
  | cons bit rest => simp only [scan, pending]

theorem scan_buffer (vertices literals : List CNFLiteral) (fuel : Nat) (r : State)
    (pending : r.pending = bits literals ++ [true,false])
    (variables : r.variables = SearchVertices.encodeVertices vertices)
    (enough : r.pending.length < fuel) :
    (scan fuel r).state.buffer = (bits (value vertices literals)).reverse ++ r.buffer := by
  induction literals generalizing fuel r with
  | nil =>
      have nonempty := pending_nonempty [] r pending
      change r.pending = [true,false] at pending
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have ended : (stepped r).pending = [] := by
            simp only [stepped, pending, stopped]
          rw [scan_state_step fuel r nonempty, scan_stopped fuel (stepped r) ended]
          change (stepped r).buffer = r.buffer
          simp only [stepped, pending, stopped, guarded, State.withCore]
  | cons literal literals ih =>
      have nonempty := pending_nonempty (literal :: literals) r pending
      have read : r.pending =
          NANDFrontend.literalBits literal.positive literal.variableIndex ++
            (bits literals ++ [true,false]) := by
        rw [bits_cons, List.append_assoc] at pending
        exact pending
      have canonical := step_canonical r literal vertices (bits literals ++ [true,false]) read variables
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have remaining : (stepped r).pending.length < fuel :=
            Nat.lt_of_lt_of_le (step_progress r nonempty) (Nat.le_of_lt_succ enough)
          rw [scan_state_step fuel r nonempty,
            ih fuel (stepped r) canonical.1 ((stepped_variables r).trans variables) remaining,
            canonical.2, value_bits_cons, List.reverse_append, List.append_assoc]

theorem whole_buffer (vertices literals : List CNFLiteral) (r : State)
    (pending : r.pending = bits literals ++ [true,false])
    (variables : r.variables = SearchVertices.encodeVertices vertices) :
    (whole r).state.buffer = (bits (value vertices literals)).reverse ++ r.buffer :=
  scan_buffer vertices literals _ r pending variables (Nat.lt_succ_self _)

theorem occurrence_data (literals : List CNFLiteral) :
    (Occurrence.encodeQuery 0 literals).tail = bits literals ++ [true,false] := by
  simp only [Occurrence.encodeQuery, List.replicate_zero, List.nil_append, List.tail_cons,
    NANDFrontend.encodeTokenPairs_append, encodeTokenPairs, CNFToken.bits, List.append_nil, bits]

end PNP.Concrete.NormalizerBlocks.CompactClause
