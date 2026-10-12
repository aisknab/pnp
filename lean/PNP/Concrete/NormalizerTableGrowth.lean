/-
Copyright (c) 2026 PNP Labs.

Additive raw-output growth for the table writer. A scan can replace at most
one entry. The unspent replacement credit disappears when that entry is
emitted, preventing repeated scans from being justified by an exponentially
iterated coarse polynomial bound.
-/

import PNP.Concrete.NormalizerTableCanonical

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open Occurrence

def credit (r : Registers) : Nat :=
  match r.mode with
  | [] => 2 * r.target.length + 8
  | _ :: _ => 0

def potential (r : Registers) : Nat := r.excess.length + r.input.length + credit r

theorem token_growth (value : CNFToken) (r : Registers) :
    (tokenResult value r).state.excess.length + credit (tokenResult value r).state ≤
      r.excess.length + credit r + 2 := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases mode with
      | nil =>
          cases value <;> cases remaining <;>
            simp only [tokenResult, separatorResult, replaced, ClauseQuery.emitted, credit,
              List.length_cons, List.length_append, List.length_replicate] <;> omega
      | cons bit rest =>
          cases bit <;> cases value <;>
            simp only [tokenResult, ClauseQuery.emitted, afterEntry, credit, List.length_cons] <;> omega

theorem pair_potential (r : Registers) : potential (pairResult r).state ≤ potential r := by
  cases input : r.input with
  | nil =>
      simp only [pairResult, input, potential, credit, List.length_nil]
      exact Nat.le_refl _
  | cons first tail =>
      cases tail with
      | nil =>
          simp only [pairResult, input, potential, credit, List.length_cons, List.length_nil]
          omega
      | cons second rest =>
          have bound : (tokenResult (CNFToken.ofBits first second) {r with input := rest}).state.excess.length +
              credit (tokenResult (CNFToken.ofBits first second) {r with input := rest}).state ≤
                r.excess.length + credit r + 2 := by
            have h := token_growth (CNFToken.ofBits first second) {r with input := rest}
            exact h
          simp only [potential, pairResult, input, token_input, List.length_cons]
          omega

theorem scan_potential (fuel : Nat) (r : Registers) : potential (scan fuel r).state ≤ potential r := by
  induction fuel generalizing r with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases active : r.active with
      | nil => simpa only [scan, active] using Nat.le_refl (potential r)
      | cons bit rest =>
          have tail := ih (pairResult r).state
          have first := pair_potential r
          simpa only [scan, active] using Nat.le_trans tail first

theorem query_buffer_bound (r : Registers) :
    (queryResult r).state.excess.length ≤ r.excess.length + r.input.length + credit r := by
  have bound := scan_potential (r.input.length + 1) r
  change (queryResult r).state.excess.length + (queryResult r).state.input.length +
    credit (queryResult r).state ≤ r.excess.length + r.input.length + credit r at bound
  omega

theorem credit_bound (r : Registers) : credit r ≤ 2 * r.target.length + 8 := by
  cases mode : r.mode <;> simp only [credit, mode] <;> omega

theorem query_growth_bound (r : Registers) :
    (queryResult r).state.excess.length ≤ r.excess.length + r.input.length + 2 * r.target.length + 8 := by
  have bound := query_buffer_bound r
  have extra := credit_bound r
  omega

theorem packed_query_growth_bound (r : Registers) :
    (packed (queryResult r).state).output.length ≤
      r.excess.length + r.input.length + 2 * r.target.length + 8 := by
  simpa only [packed, List.length_reverse] using query_growth_bound r

end PNP.Concrete.NormalizerBlocks.TableWrite
