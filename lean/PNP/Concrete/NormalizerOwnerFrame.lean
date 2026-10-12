/-
Copyright (c) 2026 PNP Labs.

Composition facts for the verified owner loop: its target register is
preserved on every raw input, and a prepared canonical table query has the
same earliest-owner output as the closed single-input machine.
-/

import PNP.Concrete.NormalizerOwnerOrder

namespace PNP.Concrete.NormalizerBlocks.TableOwner

open BitRegister Occurrence

theorem pair_target (r : Registers) : (pairResult r).state.target = r.target := by
  cases input : r.input with
  | nil => simp only [pairResult, input]
  | cons first tail =>
      cases tail with
      | nil => simp only [pairResult, input]
      | cons second rest =>
          simp only [pairResult, input, token_target]

theorem scan_target (fuel : Nat) (r : Registers) : (scan fuel r).state.target = r.target := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
      cases active : r.active with
      | nil => simp only [scan, active]
      | cons bit rest =>
          simpa only [scan, active] using (ih (pairResult r).state).trans (pair_target r)

theorem query_target (r : Registers) : (queryResult r).state.target = r.target :=
  scan_target _ r

def prepared (target table : BitString) : Registers :=
  ⟨table, target, [], [], [], [], [true], [], [false]⟩

theorem prepared_canonical (target : Nat) (entries : MatchingTable.Entries) :
    (queryResult (prepared (List.replicate target true) (MatchingTable.encode entries))).state.output =
      answer (owner entries target) := by
  let values := encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish]
  let start := prepared (List.replicate target true) (MatchingTable.encode entries)
  obtain ⟨fuel, canonical⟩ := tokenScan_exec values (waiting target [] [] [] [])
  have actual := query_exec start
  have same := NANDFrontend.accepted_store_unique (loop.program 0 8)
    _ _ ⟨.running 0, start.store⟩
    (queryResult start).state.store (tokenScan values (waiting target [] [] [] [])).store
    (actual.program_run 0 8) (canonical.program_run 0 8)
  exact (congrArg (fun store : Store 9 => store.get 8) same).trans
    (tokenScan_table_correct entries target 0 [] [] [])

end PNP.Concrete.NormalizerBlocks.TableOwner
