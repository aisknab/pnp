/-
Copyright (c) 2026 PNP Labs.

Load a length-delimited table and its pending updates from one raw input.
The finite header/split/pack code derives both fields internally, including
truncated inputs. Packing preserves the table's existing finish token.
-/

import PNP.Concrete.NormalizerBatchPacketSplit

namespace PNP.Concrete.NormalizerBlocks.BatchPacket

open BitRegister Occurrence

def taken (input : BitString) : Result :=
  takeResult (TableInit.readCount input).state.target (TableInit.readCount input).state

def coreLoader : Block 9 := .seq TableInit.header (.seq takeLoop TableWrite.pack)
def coreResult (input : BitString) : Registers := TableWrite.packed (taken input).state
def coreFuel (input : BitString) : Nat :=
  TableInit.headerFuel input + ((taken input).fuel + TableWrite.packFuel (taken input).state)

theorem core_exec (input : BitString) :
    Exec coreLoader (initialRegisters input).store (coreFuel input) (coreResult input).store :=
  Exec.seq (TableInit.header_exec input)
    (Exec.seq (take_exec (TableInit.readCount input).state.target (TableInit.readCount input).state)
      (TableWrite.pack_exec (taken input).state))

theorem taken_size (input : BitString) :
    (taken input).state.excess.length + (taken input).state.input.length ≤ input.length := by
  have size := take_size (TableInit.readCount input).state.target (TableInit.readCount input).state
  have empty : (TableInit.readCount input).state.excess = [] :=
    Occurrence.header_excess input (TableInit.seeded input)
  have remainder : (TableInit.readCount input).state.input.length ≤ input.length :=
    Occurrence.header_input_bound input (TableInit.seeded input)
  rw [empty] at size
  simp only [List.length_nil, Nat.zero_add] at size
  exact Nat.le_trans size remainder

theorem core_size (input : BitString) :
    (coreResult input).output.length + (coreResult input).input.length ≤ input.length := by
  simpa only [coreResult, TableWrite.packed, List.length_reverse] using taken_size input

theorem coreFuel_bound (input : BitString) : coreFuel input ≤ 33 * input.length + 42 := by
  have header := TableInit.headerFuel_bound input
  have count := TableInit.count_length_bound input
  have split : (taken input).fuel ≤ 5 * (TableInit.readCount input).state.target.length + 4 :=
    take_fuel_bound (TableInit.readCount input).state.target (TableInit.readCount input).state
  have buffer := taken_size input
  simp only [coreFuel, TableWrite.packFuel]
  omega

def seedState (input : BitString) : TableBatch.State := ⟨initialRegisters input, [], []⟩
def commit : Block 11 := .seq (.action (.copy 9 0)) (.action (.copy 10 8))
def committed (r : TableBatch.State) : TableBatch.State := ⟨r.core, r.core.input, r.core.output⟩

theorem commit_exec (r : TableBatch.State) : Exec commit r.store 2 (committed r).store :=
  Exec.seq (.action _ _) (.action _ _)

def loader : Block 11 := .seq (Frame.block 2 coreLoader) commit
def loaded (input : BitString) : TableBatch.State :=
  ⟨coreResult input, (coreResult input).input, (coreResult input).output⟩
def loaderFuel (input : BitString) : Nat := coreFuel input + 2

theorem loader_exec (input : BitString) :
    Exec loader (seedState input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (Frame.execution (core_exec input) (seedState input).frame)
    (commit_exec ⟨coreResult input, [], []⟩)

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 33 * input.length + 44 := by
  have bound := coreFuel_bound input
  simp only [loaderFuel]
  omega

theorem loaded_size (input : BitString) :
    (loaded input).pending.length ≤ input.length ∧ (loaded input).table.length ≤ input.length := by
  have bound := core_size input
  change (coreResult input).input.length ≤ input.length ∧ (coreResult input).output.length ≤ input.length
  constructor <;> omega

end PNP.Concrete.NormalizerBlocks.BatchPacket
