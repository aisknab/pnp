/-
Copyright (c) 2026 PNP Labs.

Exact encoding and data-copy laws for the finite table writer. Mode transitions
distinguish searching, skipping the old selected payload, and copying the
remainder. The arbitrary payload grammar is inherited from the verified reader.
-/

import PNP.Concrete.NormalizerTableTokens

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open Occurrence

def tableState (index value : Nat) (buffer mode : BitString) (r : Registers) : Registers :=
  ⟨[], List.replicate value true, List.replicate index true, buffer, [],
    mode, [true], r.reserved, r.output⟩

theorem unary_reversed (value : Nat) :
    (encodeTokenPairs (encodeUnaryTokens value)).reverse =
      false :: false :: List.replicate (2 * value) true := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simpa only [encodeUnaryTokens, encodeTokenPairs, CNFToken.bits, List.nil_append,
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
        Nat.mul_succ, List.replicate_succ'] using
        congrArg (fun bits : BitString => bits ++ [true, true]) ih

theorem replacement_bytes (value : Nat) :
    (encodeTokenPairs (encodeClauseTokens [⟨true, value⟩])).reverse =
      false :: true :: false :: false ::
        (List.replicate (2 * value) true ++ [true, true, true, false]) := by
  simp only [encodeClauseTokens, encodeLiteralListTokens, encodeLiteralTokens,
    NANDFrontend.encodeTokenPairs_append, encodeTokenPairs, CNFToken.bits, ite_true,
    List.cons_append, List.nil_append, List.append_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, unary_reversed, List.append_assoc]

theorem tokenScan_skip_data {values : List CNFToken} (data : ClauseQuery.DataTokens values)
    (rest : List CNFToken) (index value : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (values ++ rest) (tableState index value buffer [true] r) =
      tokenScan rest (tableState index value buffer [true] r) := by
  induction data with
  | nil => rfl
  | f _ ih => simpa only [List.cons_append, tokenScan, tableState, tokenResult] using ih
  | t _ ih => simpa only [List.cons_append, tokenScan, tableState, tokenResult] using ih

theorem tokenScan_copy_data {values : List CNFToken} (data : ClauseQuery.DataTokens values)
    (rest : List CNFToken) (index value : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (values ++ rest) (tableState index value buffer [] r) =
      tokenScan rest (tableState index value ((encodeTokenPairs values).reverse ++ buffer) [] r) := by
  induction data generalizing buffer with
  | nil => rfl
  | f _ ih =>
      simpa only [List.cons_append, tokenScan, tableState, tokenResult, ClauseQuery.emitted,
        encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons, List.reverse_nil,
        List.append_assoc] using ih (false :: false :: buffer)
  | t _ ih =>
      simpa only [List.cons_append, tokenScan, tableState, tokenResult, ClauseQuery.emitted,
        encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons, List.reverse_nil,
        List.append_assoc] using ih (true :: true :: buffer)

theorem tokenScan_done (values : List CNFToken) (index value : Nat) (buffer : BitString) (r : Registers) :
    (tokenScan values (tableState index value buffer [false] r)).excess =
      (encodeTokenPairs values).reverse ++ buffer := by
  induction values generalizing buffer with
  | nil => rfl
  | cons token rest ih =>
      cases token with
      | f =>
          simpa only [tokenScan, tableState, tokenResult, ClauseQuery.emitted,
            encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons,
            List.cons_append, List.append_assoc] using ih (false :: false :: buffer)
      | t =>
          simpa only [tokenScan, tableState, tokenResult, ClauseQuery.emitted,
            encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons,
            List.cons_append, List.append_assoc] using ih (true :: true :: buffer)
      | sep =>
          simpa only [tokenScan, tableState, tokenResult, ClauseQuery.emitted,
            encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons,
            List.cons_append, List.append_assoc] using ih (true :: false :: buffer)
      | finish =>
          simpa only [tokenScan, tableState, tokenResult, ClauseQuery.emitted,
            encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons,
            List.cons_append, List.append_assoc] using ih (false :: true :: buffer)

theorem tokenScan_select_zero (rest : List CNFToken) (value : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (.sep :: rest) (tableState 0 value buffer [] r) =
      tokenScan rest (tableState 0 value
        ((encodeTokenPairs (encodeClauseTokens [⟨true, value⟩])).reverse ++ buffer) [true] r) := by
  rw [replacement_bytes]
  simp only [tokenScan, tableState, tokenResult, separatorResult, replaced,
    List.replicate_zero, List.length_replicate, List.cons_append, List.nil_append, List.append_assoc]

theorem tokenScan_select_succ (rest : List CNFToken) (index value : Nat)
    (buffer : BitString) (r : Registers) :
    tokenScan (.sep :: rest) (tableState (index + 1) value buffer [] r) =
      tokenScan rest (tableState index value (true :: false :: buffer) [] r) := by
  simp only [tokenScan, tableState, tokenResult, separatorResult, ClauseQuery.emitted, List.replicate_succ]

theorem tokenScan_finish_selected (rest : List CNFToken) (index value : Nat)
    (buffer : BitString) (r : Registers) :
    tokenScan (.finish :: rest) (tableState index value buffer [true] r) =
      tokenScan rest (tableState index value buffer [false] r) := rfl

theorem tokenScan_finish_before (rest : List CNFToken) (index value : Nat)
    (buffer : BitString) (r : Registers) :
    tokenScan (.finish :: rest) (tableState index value buffer [] r) =
      tokenScan rest (tableState index value (false :: true :: buffer) [] r) := rfl

end PNP.Concrete.NormalizerBlocks.TableWrite
