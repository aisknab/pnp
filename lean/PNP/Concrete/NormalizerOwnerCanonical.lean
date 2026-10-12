/-
Copyright (c) 2026 PNP Labs.

End-to-end exact byte output of the fixed source-order owner machine. The
unary target is read internally and the theorem covers every finite table,
including duplicate matches and missing values.
-/

import PNP.Concrete.NormalizerOwnerSemantics

namespace PNP.Concrete.NormalizerBlocks.TableOwner

open BitRegister Occurrence

theorem canonical_block_exec (target : Nat) (entries : MatchingTable.Entries) :
    ∃ fuel, Exec block (initialRegisters (encodeQuery target entries)).store fuel
      (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
        (waiting target [] [] [] [])).store := by
  let values := encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish]
  let input := encodeQuery target entries
  obtain ⟨fuel, scanned⟩ := tokenScan_exec values (waiting target [] [] [] [])
  have start : Exec initializeBlock (initialRegisters input).store 2 (seeded input).store :=
    Exec.seq (.action _ _) (.action _ _)
  have header : Exec headerLoop (seeded input).store (4 * target + 5)
      (Registers.store ⟨encodeTokenPairs values, List.replicate target true,
        [], [], [], [], [], [], [false]⟩) := by
    simpa only [seeded, input, encodeQuery, MatchingTable.encode, values,
      List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical target 0 (encodeTokenPairs values) [] [] [] [] [] [false]
  have activate : Exec (.action (.push 6 true))
      (Registers.store ⟨encodeTokenPairs values, List.replicate target true,
        [], [], [], [], [], [], [false]⟩) 1
      ({waiting target [] [] [] [] with input := encodeTokenPairs values}).store := .action _ _
  exact ⟨2 + ((4 * target + 5) + (1 + fuel)),
    Exec.seq start (Exec.seq header (Exec.seq activate scanned))⟩

theorem polynomial_canonical (target : Nat) (entries : MatchingTable.Entries) :
    polynomial.output (encodeQuery target entries) = answer (owner entries target) := by
  obtain ⟨fuel, checked⟩ := canonical_block_exec target entries
  have canonical : BitRegister.run program (fuel + 1)
      (BitRegister.initial program (encodeQuery target entries)) =
        ⟨.accepted, (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
          (waiting target [] [] [] [])).store⟩ := by
    rw [initial_registers]
    exact checked.program_run 0 8
  have stores := NANDFrontend.accepted_store_unique program
    (sourceSteps (encodeQuery target entries) + 1) (fuel + 1)
    (BitRegister.initial program (encodeQuery target entries))
    (result (encodeQuery target entries)).state.store
    (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (waiting target [] [] [] [])).store
    (closed_run (encodeQuery target entries)) canonical
  rw [polynomial_output]
  exact (congrArg (fun store : Store 9 => store.get 8) stores).trans
    (tokenScan_table_correct entries target 0 [] [] [])

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (target : Nat) (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encodeQuery target entries).length)
      (encodeQuery target entries) = answer (owner entries target) :=
  (output_projection (encodeQuery target entries)).symm.trans (polynomial_canonical target entries)

theorem first_entry (target : Nat) (rest : MatchingTable.Entries) :
    polynomial.output (encodeQuery target (some target :: rest)) = [true] := by
  rw [polynomial_canonical]
  have equal : (target == target) = true := by
    change decide (target = target) = true
    exact decide_eq_true rfl
  simp only [owner, ownerFrom, equal, ite_true, answer, List.replicate_zero]

end PNP.Concrete.NormalizerBlocks.TableOwner
