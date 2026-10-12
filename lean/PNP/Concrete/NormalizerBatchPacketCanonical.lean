/-
Copyright (c) 2026 PNP Labs.

Exact single-input table-update semantics of the compiled machine. The packet
contains a unary byte-count delimiter, the table bytes and an arbitrary finite
update list. Neither a decoded table boundary nor a successful execution is
supplied as a premise.
-/

import PNP.Concrete.NormalizerBatchPolynomial

namespace PNP.Concrete.NormalizerBlocks.BatchPacket

open BitRegister Occurrence

theorem header_canonical (count : Nat) (suffix : BitString) :
    (TableInit.readCount (TableInit.encodeCount count suffix)).state =
      TableInit.canonicalHeader count suffix := by
  let input := TableInit.encodeCount count suffix
  have start : Exec (.action (.push 6 true)) (initialRegisters input).store 1
      (TableInit.seeded input).store := .action _ _
  have parsed : Exec headerLoop (TableInit.seeded input).store
      (4 * count + 5) (TableInit.canonicalHeader count suffix).store := by
    simpa only [TableInit.seeded, input, TableInit.encodeCount, TableInit.canonicalHeader,
      List.replicate_zero, Nat.zero_add] using
      Occurrence.header_canonical count 0 suffix [] [] [] [] [] []
  have canonical := Exec.seq start parsed
  have actual := TableInit.header_exec input
  exact TableBatch.registers_eq_of_store (NANDFrontend.accepted_store_unique (TableInit.header.program 0 8)
    _ _ ⟨.running 0, (initialRegisters input).store⟩
    (TableInit.readCount input).state.store (TableInit.canonicalHeader count suffix).store
    (actual.program_run 0 8) (canonical.program_run 0 8))

theorem taken_canonical (data suffix : BitString) :
    (taken (TableInit.encodeCount data.length (data ++ suffix))).state =
      Registers.mk suffix [] [] data.reverse [] [] [] [] [] := by
  simp only [taken, header_canonical, TableInit.canonicalHeader]
  simpa only [List.append_nil] using
    take_canonical data suffix (Registers.mk [] (List.replicate data.length true) [] [] [] [] [] [] [])

theorem core_canonical (data suffix : BitString) :
    coreResult (TableInit.encodeCount data.length (data ++ suffix)) =
      Registers.mk suffix [] [] [] [] [] [] [] data := by
  simp only [coreResult, taken_canonical, TableWrite.packed, List.reverse_reverse]

theorem loaded_canonical (data suffix : BitString) :
    (loaded (TableInit.encodeCount data.length (data ++ suffix))).pending = suffix ∧
      (loaded (TableInit.encodeCount data.length (data ++ suffix))).table = data :=
  ⟨congrArg Registers.input (core_canonical data suffix),
    congrArg Registers.output (core_canonical data suffix)⟩

def encode (entries : MatchingTable.Entries) (updates : List (Nat × Nat)) : BitString :=
  TableInit.encodeCount (MatchingTable.encode entries).length
    (MatchingTable.encode entries ++ TableBatch.encodeUpdates updates)

theorem polynomial_canonical (entries : MatchingTable.Entries) (updates : List (Nat × Nat)) :
    polynomial.output (encode entries updates) = MatchingTable.encode (MatchingTable.writeAll entries updates) := by
  rw [polynomial_output]
  have packet := loaded_canonical (MatchingTable.encode entries) (TableBatch.encodeUpdates updates)
  exact TableBatch.run_canonical updates _ (loaded (encode entries updates)) entries
    packet.1 packet.2 (Or.inl (Nat.lt_succ_self _))

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 11 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (entries : MatchingTable.Entries) (updates : List (Nat × Nat)) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 11 sourceFuel).eval (encode entries updates).length)
      (encode entries updates) = MatchingTable.encode (MatchingTable.writeAll entries updates) :=
  (output_projection (encode entries updates)).symm.trans (polynomial_canonical entries updates)

theorem empty_updates_preserve (entries : MatchingTable.Entries) :
    polynomial.output (encode entries []) = MatchingTable.encode entries :=
  polynomial_canonical entries []

theorem repeated_index_last_wins (entries : MatchingTable.Entries) (index first last : Nat) :
    polynomial.output (encode entries [(index,first),(index,last)]) =
      MatchingTable.encode (MatchingTable.write entries index last) := by
  rw [polynomial_canonical]
  simp only [MatchingTable.writeAll, MatchingTable.write_last_wins]

end PNP.Concrete.NormalizerBlocks.BatchPacket
