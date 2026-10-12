/-
Copyright (c) 2026 PNP Labs.

Closed candidate-packet loading. The variable count and both table boundaries
are read from the raw input by fixed finite blocks. The loader never receives
decoded dimensions or an execution certificate as runtime premises.
-/

import PNP.Concrete.NormalizerCandidatePacketOperations

namespace PNP.Concrete.NormalizerBlocks.CandidatePacket

open BitRegister Occurrence

def initial (input : BitString) : Candidate.State := ⟨initialRegisters input, [], [], [], []⟩
def countState (input : BitString) : Candidate.State := ⟨(TableInit.readCount input).state, [], [], [], []⟩
def head : Block 13 := .seq (Frame.block 4 TableInit.header) saveCount
def headResult (input : BitString) : Candidate.State := counted (countState input)
def headFuel (input : BitString) : Nat := TableInit.headerFuel input + 1

theorem head_exec (input : BitString) :
    Exec head (initial input).store (headFuel input) (headResult input).store :=
  Exec.seq (Frame.execution (TableInit.header_exec input) (initial input).frame)
    (saveCount_exec (countState input))

def first : Block 13 := .seq loadTable saveMatching
def firstResult (r : Candidate.State) : Candidate.State := matched (tableResult r)
def firstFuel (r : Candidate.State) : Nat := tableFuel r + 1

theorem first_exec (r : Candidate.State) : Exec first r.store (firstFuel r) (firstResult r).store :=
  Exec.seq (loadTable_exec r) (saveMatching_exec (tableResult r))

def second : Block 13 := .seq loadTable saveSeen
def secondResult (r : Candidate.State) : Candidate.State := traced (tableResult r)
def secondFuel (r : Candidate.State) : Nat := tableFuel r + 1

theorem second_exec (r : Candidate.State) : Exec second r.store (secondFuel r) (secondResult r).store :=
  Exec.seq (loadTable_exec r) (saveSeen_exec (tableResult r))

def loader : Block 13 := .seq head (.seq first (.seq second startCandidates))
def loaded (input : BitString) : Candidate.State := started (secondResult (firstResult (headResult input)))
def loaderFuel (input : BitString) : Nat :=
  headFuel input + (firstFuel (headResult input) + (secondFuel (firstResult (headResult input)) + 10))

theorem loader_exec (input : BitString) :
    Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (head_exec input) (Exec.seq (first_exec (headResult input))
    (Exec.seq (second_exec (firstResult (headResult input)))
      (startCandidates_exec (secondResult (firstResult (headResult input))))))

theorem head_input_bound (input : BitString) : (headResult input).core.input.length ≤ input.length :=
  Occurrence.header_input_bound input (TableInit.seeded input)

theorem head_counter_bound (input : BitString) :
    (headResult input).remaining.length ≤ 5 * input.length + 6 :=
  TableInit.count_length_bound input

theorem first_size (r : Candidate.State) :
    (firstResult r).core.input.length ≤ r.core.input.length ∧
      (firstResult r).matching.length ≤ r.core.input.length :=
  tableResult_size r

theorem second_size (r : Candidate.State) :
    (secondResult r).core.input.length ≤ r.core.input.length ∧
      (secondResult r).seen.length ≤ r.core.input.length :=
  tableResult_size r

theorem loaded_size (input : BitString) :
    (loaded input).matching.length ≤ input.length ∧
      (loaded input).seen.length ≤ input.length ∧
        (loaded input).remaining.length ≤ 5 * input.length + 6 := by
  have start := head_input_bound input
  have first := first_size (headResult input)
  have second := second_size (firstResult (headResult input))
  refine ⟨?_, ?_, head_counter_bound input⟩
  · exact Nat.le_trans first.2 start
  · exact Nat.le_trans second.2 (Nat.le_trans first.1 start)

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 70 * input.length + 119 := by
  have header := TableInit.headerFuel_bound input
  have start := head_input_bound input
  have size := (first_size (headResult input)).1
  have first := tableFuel_bound (headResult input)
  have second := tableFuel_bound (firstResult (headResult input))
  simp only [loaderFuel, headFuel, firstFuel, secondFuel]
  omega

def packet (table suffix : BitString) : BitString :=
  TableInit.encodeCount table.length (table ++ suffix)
def encode (count : Nat) (matching seen : MatchingTable.Entries) : BitString :=
  TableInit.encodeCount count (packet (MatchingTable.encode matching) (packet (MatchingTable.encode seen) []))

theorem loaded_canonical (count : Nat) (matching seen : MatchingTable.Entries) :
    loaded (encode count matching seen) =
      Candidate.initial count (MatchingTable.encode matching) (MatchingTable.encode seen) := by
  simp only [loaded, encode, packet, headResult, counted, countState, firstResult, secondResult,
    tableResult, matched, traced, started, BatchPacket.header_canonical, TableInit.canonicalHeader,
    BatchPacket.core_canonical, Candidate.initial]

end PNP.Concrete.NormalizerBlocks.CandidatePacket
