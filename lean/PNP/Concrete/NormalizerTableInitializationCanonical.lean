/-
Copyright (c) 2026 PNP Labs.

Exact canonical output of the closed empty-table initializer. The count is
read from a unary header; any remaining input is preserved internally and
cannot alter the initialized table. No prebuilt table is supplied.
-/

import PNP.Concrete.NormalizerTableInitializationPolynomial

namespace PNP.Concrete.NormalizerBlocks.TableInit

open BitRegister Occurrence

def canonicalHeader (count : Nat) (suffix : BitString) : Registers :=
  ⟨suffix, List.replicate count true, [], [], [], [], [], [], []⟩

def canonicalResult (count : Nat) (suffix : BitString) : Registers :=
  ClauseQuery.packed (built (List.replicate count true) (canonicalHeader count suffix))

theorem canonical_block_exec (count : Nat) (suffix : BitString) :
    ∃ fuel, Exec block (initialRegisters (encodeCount count suffix)).store fuel
      (canonicalResult count suffix).store := by
  have start : Exec (.action (.push 6 true)) (initialRegisters (encodeCount count suffix)).store 1
      (seeded (encodeCount count suffix)).store := .action _ _
  have parsed : Exec headerLoop (seeded (encodeCount count suffix)).store
      (4 * count + 5) (canonicalHeader count suffix).store := by
    simpa only [seeded, encodeCount, canonicalHeader, List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical count 0 suffix [] [] [] [] [] []
  have generated := loop_exec (List.replicate count true) (canonicalHeader count suffix)
  have headRun := Exec.seq start parsed
  have frontRun := Exec.seq headRun generated
  exact ⟨_, Exec.seq frontRun (ClauseQuery.pack_exec
    (built (List.replicate count true) (canonicalHeader count suffix)))⟩

theorem canonical_bytes (count : Nat) (suffix : BitString) :
    (canonicalResult count suffix).output = MatchingTable.encode (List.replicate count none) := by
  have encoded := emptyData_encoding count
  change (emptyData (List.replicate count true).length ++ []).reverse ++ [true, false] = _
  rw [List.length_replicate, List.append_nil, ← encoded, List.reverse_reverse]
  simp only [MatchingTable.encode, NANDFrontend.encodeTokenPairs_append,
    encodeTokenPairs, CNFToken.bits, List.append_nil]

theorem polynomial_canonical (count : Nat) (suffix : BitString) :
    polynomial.output (encodeCount count suffix) = MatchingTable.encode (List.replicate count none) := by
  obtain ⟨fuel, checked⟩ := canonical_block_exec count suffix
  have canonical : BitRegister.run program (fuel + 1)
      (BitRegister.initial program (encodeCount count suffix)) =
        ⟨.accepted, (canonicalResult count suffix).store⟩ := by
    rw [initial_registers]
    exact checked.program_run 0 8
  have stores := NANDFrontend.accepted_store_unique program
    (sourceSteps (encodeCount count suffix) + 1) (fuel + 1)
    (BitRegister.initial program (encodeCount count suffix))
    (result (encodeCount count suffix)).store (canonicalResult count suffix).store
    (closed_run (encodeCount count suffix)) canonical
  rw [polynomial_output]
  exact (congrArg (fun store : Store 9 => store.get 8) stores).trans (canonical_bytes count suffix)

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (count : Nat) (suffix : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encodeCount count suffix).length)
      (encodeCount count suffix) = MatchingTable.encode (List.replicate count none) :=
  (output_projection (encodeCount count suffix)).symm.trans (polynomial_canonical count suffix)

end PNP.Concrete.NormalizerBlocks.TableInit
