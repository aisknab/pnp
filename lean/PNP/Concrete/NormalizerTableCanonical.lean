/-
Copyright (c) 2026 PNP Labs.

Canonical correctness of the closed table-write machine, uniform in every
finite table, index and value. The concrete machine reads both headers itself.
No caller-supplied transition or correctness premise is accepted.
-/

import PNP.Concrete.NormalizerTableSemantics

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open BitRegister Occurrence

def writeInitial (index value : Nat) : Registers :=
  tableState index value [] [] ⟨[], [], [], [], [], [], [], List.replicate index true, []⟩

theorem canonical_block_exec (entries : MatchingTable.Entries) (index value : Nat) :
    ∃ fuel, Exec block (initialRegisters (encodeWrite index value entries)).store fuel
      (packed (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
        (writeInitial index value))).store := by
  let values := encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish]
  let input := encodeWrite index value entries
  let afterIndex : Registers :=
    ⟨List.replicate value true ++ false :: encodeTokenPairs values, List.replicate index true,
      [], [], [], [], [], [], []⟩
  let afterValue : Registers :=
    ⟨encodeTokenPairs values, List.replicate value true, [], [], [], [], [], List.replicate index true, []⟩
  obtain ⟨fuel, selected⟩ := tokenScan_exec values (writeInitial index value)
  have start : Exec (.action (.push 6 true)) (initialRegisters input).store 1 (seeded input).store :=
    .action _ _
  have first : Exec headerLoop (seeded input).store (4 * index + 5) afterIndex.store := by
    simpa only [seeded, input, encodeWrite, MatchingTable.encode, afterIndex, values,
      List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical index 0
        (List.replicate value true ++ false :: encodeTokenPairs values) [] [] [] [] [] []
  have second : Exec headerLoop (ClauseQuery.saved afterIndex).store (4 * value + 5) afterValue.store := by
    simpa only [ClauseQuery.saved, afterIndex, afterValue, List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical value 0 (encodeTokenPairs values) [] [] [] [] (List.replicate index true) []
  have setup : Exec prepare afterValue.store 2
      ({writeInitial index value with input := encodeTokenPairs values}).store :=
    prepare_exec afterValue
  have headerRun : Exec headers (initialRegisters input).store
      (1 + ((4 * index + 5) + (3 + ((4 * value + 5) + 2))))
      ({writeInitial index value with input := encodeTokenPairs values}).store :=
    Exec.seq start (Exec.seq first (Exec.seq (ClauseQuery.save_exec afterIndex) (Exec.seq second setup)))
  have frontRun := Exec.seq headerRun selected
  exact ⟨_, Exec.seq frontRun (pack_exec (tokenScan values (writeInitial index value)))⟩

theorem packed_canonical (entries : MatchingTable.Entries) (index value : Nat) :
    (packed (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (writeInitial index value))).output = MatchingTable.encode (MatchingTable.write entries index value) := by
  have buffer : (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (writeInitial index value)).excess =
        (MatchingTable.encode (MatchingTable.write entries index value)).reverse ++ [] :=
    tokenScan_table entries index value [] ⟨[], [], [], [], [], [], [], List.replicate index true, []⟩
  change (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
    (writeInitial index value)).excess.reverse = _
  rw [buffer, List.append_nil, List.reverse_reverse]

theorem polynomial_canonical (entries : MatchingTable.Entries) (index value : Nat) :
    polynomial.output (encodeWrite index value entries) = MatchingTable.encode (MatchingTable.write entries index value) := by
  obtain ⟨fuel, checked⟩ := canonical_block_exec entries index value
  have canonical : BitRegister.run program (fuel + 1)
      (BitRegister.initial program (encodeWrite index value entries)) =
        ⟨.accepted, (packed (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
          (writeInitial index value))).store⟩ := by
    rw [initial_registers]
    exact checked.program_run 0 8
  have stores := NANDFrontend.accepted_store_unique program
    (sourceSteps (encodeWrite index value entries) + 1) (fuel + 1)
    (BitRegister.initial program (encodeWrite index value entries))
    (result (encodeWrite index value entries)).store
    (packed (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (writeInitial index value))).store
    (closed_run (encodeWrite index value entries)) canonical
  rw [polynomial_output]
  exact (congrArg (fun store : Store 9 => store.get 8) stores).trans (packed_canonical entries index value)

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (entries : MatchingTable.Entries) (index value : Nat) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encodeWrite index value entries).length)
      (encodeWrite index value entries) = MatchingTable.encode (MatchingTable.write entries index value) :=
  (output_projection (encodeWrite index value entries)).symm.trans (polynomial_canonical entries index value)

theorem repeated_index_last_wins (entries : MatchingTable.Entries) (index first last : Nat) :
    polynomial.output (encodeWrite index last (MatchingTable.write entries index first)) =
      MatchingTable.encode (MatchingTable.write entries index last) := by
  rw [polynomial_canonical, MatchingTable.write_last_wins]

end PNP.Concrete.NormalizerBlocks.TableWrite
