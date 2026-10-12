/-
Copyright (c) 2026 PNP Labs.

One raw packet supplies a target, clause index, length-delimited formula
and matching table. This finite loader reads and retains those data itself;
neither incidence nor matching answers appear in the input contract.
-/

import PNP.Concrete.NormalizerForwardOperations

namespace PNP.Concrete.NormalizerBlocks.ForwardEdge

open BitRegister Occurrence

def initial (input : BitString) : State := ⟨initialRegisters input, [], [], [], [], []⟩
def firstHeader : Block 14 := .seq readHeader saveTarget
def firstResult (r : State) : State := targeted (headerResult r)
def firstFuel (r : State) : Nat := headerFuel r + 1
theorem firstHeader_exec (r : State) :
    Exec firstHeader r.store (firstFuel r) (firstResult r).store :=
  Exec.seq (readHeader_exec r) (saveTarget_exec (headerResult r))

def secondHeader : Block 14 := .seq readHeader saveIndex
def secondResult (r : State) : State := indexed (headerResult r)
def secondFuel (r : State) : Nat := headerFuel r + 1
theorem secondHeader_exec (r : State) :
    Exec secondHeader r.store (secondFuel r) (secondResult r).store :=
  Exec.seq (readHeader_exec r) (saveIndex_exec (headerResult r))

def loader : Block 14 := .seq firstHeader (.seq secondHeader (.seq loadData saveData))
def loaded (input : BitString) : State := saved (dataResult (secondResult (firstResult (initial input))))
def loaderFuel (input : BitString) : Nat :=
  firstFuel (initial input) +
    (secondFuel (firstResult (initial input)) + (dataFuel (secondResult (firstResult (initial input))) + 2))

theorem loader_exec (input : BitString) :
    Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (firstHeader_exec (initial input)) (Exec.seq (secondHeader_exec (firstResult (initial input)))
    (Exec.seq (loadData_exec (secondResult (firstResult (initial input))))
      (saveData_exec (dataResult (secondResult (firstResult (initial input)))))))

theorem header_input_bound (r : State) : (headerResult r).core.input.length ≤ r.core.input.length :=
  Occurrence.header_input_bound r.core.input (TableInit.seeded r.core.input)

theorem header_target_bound (r : State) :
    (headerResult r).core.target.length ≤ 5 * r.core.input.length + 6 :=
  TableInit.count_length_bound r.core.input

theorem loaded_size (input : BitString) :
    (loaded input).target.length ≤ 5 * input.length + 6 ∧
      (loaded input).index.length ≤ 5 * input.length + 6 ∧
        (loaded input).formula.length ≤ input.length ∧ (loaded input).matching.length ≤ input.length := by
  have firstInput : (firstResult (initial input)).core.input.length ≤ input.length :=
    header_input_bound (initial input)
  have secondInput : (secondResult (firstResult (initial input))).core.input.length ≤
      (firstResult (initial input)).core.input.length := header_input_bound (firstResult (initial input))
  have firstTarget := header_target_bound (initial input)
  have secondTarget := header_target_bound (firstResult (initial input))
  have packet := BatchPacket.core_size (secondResult (firstResult (initial input))).core.input
  refine ⟨firstTarget, ?_, ?_, ?_⟩
  · change (headerResult (firstResult (initial input))).core.target.length ≤ _
    omega
  · change (BatchPacket.coreResult (secondResult (firstResult (initial input))).core.input).output.length ≤ _
    omega
  · change (BatchPacket.coreResult (secondResult (firstResult (initial input))).core.input).input.length ≤ _
    omega

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 41 * input.length + 82 := by
  have firstInput : (firstResult (initial input)).core.input.length ≤ input.length :=
    header_input_bound (initial input)
  have secondInput : (secondResult (firstResult (initial input))).core.input.length ≤
      (firstResult (initial input)).core.input.length := header_input_bound (firstResult (initial input))
  have first := TableInit.headerFuel_bound input
  have second := TableInit.headerFuel_bound (firstResult (initial input)).core.input
  have packet := BatchPacket.coreFuel_bound (secondResult (firstResult (initial input))).core.input
  change (8 + TableInit.headerFuel input + 1) +
    ((8 + TableInit.headerFuel (firstResult (initial input)).core.input + 1) +
      ((8 + BatchPacket.coreFuel (secondResult (firstResult (initial input))).core.input) + 2)) ≤ _
  omega

def encode (target index : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : BitString :=
  TableInit.encodeCount target (TableInit.encodeCount index
    (TableInit.encodeCount (GraphQuery.clauseData clauses).length
      (GraphQuery.clauseData clauses ++ MatchingTable.encode entries)))

theorem loaded_canonical (target index : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    (loaded (encode target index clauses entries)).target = List.replicate target true ∧
      (loaded (encode target index clauses entries)).index = List.replicate index true ∧
        (loaded (encode target index clauses entries)).formula = GraphQuery.clauseData clauses ∧
          (loaded (encode target index clauses entries)).matching = MatchingTable.encode entries := by
  simp only [loaded, encode, saved, dataResult, secondResult, indexed, firstResult, targeted, headerResult,
    initial, initialRegisters, BatchPacket.header_canonical, TableInit.canonicalHeader, BatchPacket.core_canonical]
  exact ⟨trivial, trivial, trivial, trivial⟩

end PNP.Concrete.NormalizerBlocks.ForwardEdge
