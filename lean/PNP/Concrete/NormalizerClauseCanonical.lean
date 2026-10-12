/-
Copyright (c) 2026 PNP Labs.

Canonical byte-level correctness of the closed full-clause-list query builder.
The selected clause is derived from the encoded list by the finite program;
its index is arbitrary, including indices beyond the end of the list.
-/

import PNP.Concrete.NormalizerClauseSemantics
import PNP.Concrete.NormalizerOccurrenceCanonical

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

open BitRegister Occurrence

def selectionInitial (target index : Nat) : Registers :=
  selectionState index (false :: List.replicate target true) false
    ⟨[], List.replicate index true, [], [], [], [], [], List.replicate target true, []⟩

theorem canonical_block_exec (target index : Nat) (clauses : List (List CNFLiteral)) :
    ∃ fuel, Exec block (Occurrence.initialRegisters (encodeQuery target index clauses)).store fuel
      (packed (tokenScan (encodeClauseListTokens clauses ++ [.finish]) (selectionInitial target index))).store := by
  let values := encodeClauseListTokens clauses ++ [.finish]
  let input := encodeQuery target index clauses
  let afterTarget : Registers :=
    ⟨List.replicate index true ++ false :: encodeTokenPairs values, List.replicate target true,
      [], [], [], [], [], [], []⟩
  let afterIndex : Registers :=
    ⟨encodeTokenPairs values, List.replicate index true, [], [], [], [], [], List.replicate target true, []⟩
  obtain ⟨fuel, selected⟩ := tokenScan_exec values (selectionInitial target index)
  have start : Exec (.action (.push 6 true)) (Occurrence.initialRegisters input).store 1 (seeded input).store :=
    .action _ _
  have first : Exec headerLoop (seeded input).store (4 * target + 5) afterTarget.store := by
    simpa only [seeded, input, encodeQuery, afterTarget, values, List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical target 0
        (List.replicate index true ++ false :: encodeTokenPairs values) [] [] [] [] [] []
  have second : Exec headerLoop (saved afterTarget).store (4 * index + 5) afterIndex.store := by
    simpa only [saved, afterTarget, afterIndex, List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical index 0 (encodeTokenPairs values) [] [] [] [] (List.replicate target true) []
  have setup : Exec prepare afterIndex.store 4
      ({selectionInitial target index with input := encodeTokenPairs values}).store :=
    prepare_exec afterIndex
  have frontRun : Exec front (Occurrence.initialRegisters input).store
      (1 + ((4 * target + 5) + (3 + ((4 * index + 5) + (4 + fuel)))))
      (tokenScan values (selectionInitial target index)).store :=
    Exec.seq start (Exec.seq first (Exec.seq (save_exec afterTarget)
      (Exec.seq second (Exec.seq setup selected))))
  exact ⟨_, Exec.seq frontRun (pack_exec (tokenScan values (selectionInitial target index)))⟩

theorem packed_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    (packed (tokenScan (encodeClauseListTokens clauses ++ [.finish]) (selectionInitial target index))).output =
      Occurrence.encodeQuery target (clauses[index]?.getD []) := by
  have buffer : (tokenScan (encodeClauseListTokens clauses ++ [.finish]) (selectionInitial target index)).excess =
      (encodeTokenPairs (encodeLiteralListTokens (clauses[index]?.getD []))).reverse ++
        (false :: List.replicate target true) :=
    tokenScan_clauseList clauses index (false :: List.replicate target true)
      ⟨[], List.replicate index true, [], [], [], [], [], List.replicate target true, []⟩
  change (tokenScan (encodeClauseListTokens clauses ++ [.finish])
    (selectionInitial target index)).excess.reverse ++ [true, false] = _
  rw [buffer, List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_replicate]
  simp only [Occurrence.encodeQuery, NANDFrontend.encodeTokenPairs_append, encodeTokenPairs,
    CNFToken.bits, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

theorem polynomial_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    polynomial.output (encodeQuery target index clauses) =
      Occurrence.encodeQuery target (clauses[index]?.getD []) := by
  obtain ⟨fuel, checked⟩ := canonical_block_exec target index clauses
  have canonical : BitRegister.run program (fuel + 1)
      (BitRegister.initial program (encodeQuery target index clauses)) =
        ⟨.accepted, (packed (tokenScan (encodeClauseListTokens clauses ++ [.finish])
          (selectionInitial target index))).store⟩ := by
    rw [initial_registers]
    exact checked.program_run 0 8
  have stores := NANDFrontend.accepted_store_unique program
    (sourceSteps (encodeQuery target index clauses) + 1) (fuel + 1)
    (BitRegister.initial program (encodeQuery target index clauses))
    (result (encodeQuery target index clauses)).store
    (packed (tokenScan (encodeClauseListTokens clauses ++ [.finish]) (selectionInitial target index))).store
    (closed_run (encodeQuery target index clauses)) canonical
  rw [polynomial_output]
  exact (congrArg (fun store : Store 9 => store.get 8) stores).trans (packed_canonical target index clauses)

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encodeQuery target index clauses).length)
      (encodeQuery target index clauses) =
        Occurrence.encodeQuery target (clauses[index]?.getD []) :=
  (output_projection (encodeQuery target index clauses)).symm.trans (polynomial_canonical target index clauses)

end PNP.Concrete.NormalizerBlocks.ClauseQuery
