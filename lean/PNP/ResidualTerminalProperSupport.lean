/-
Copyright (c) 2026 PNP Labs.

Constructive exhaustive search for governed proper positive terminal supports.
Every Boolean-selected subset of the finite terminal primitive-record universe
has a canonical seed.  The search saturates and extracts every such seed, then
tests whether the extracted support is nonempty, strictly smaller than the
whole gate carrier, and has positive exact local gain.

This reconstructs the proper-positive support search edge between Sections
2.2, 3, and 10 of the pinned manuscript.  The terminal dependency system
remains explicit data.  This module makes no claim that the full manuscript
frontier has been derived, that saturation preserves positivity step by step,
that a legitimate projection square has been constructed, or that this
exhaustive reference search runs in polynomial time.
-/

import PNP.ResidualTerminalSupportExtraction
import PNP.NANDSlack

namespace PNP
namespace DirectWire

/-! ## Canonical finite seed universe -/

/-- Enumerate every order-preserving subset of a finite list. -/
private def terminalListSubsets {alpha : Type} : List alpha -> List (List alpha)
  | [] => [[]]
  | head :: tail =>
      let remaining := terminalListSubsets tail
      remaining ++ remaining.map (fun subset => head :: subset)

private theorem filter_mem_terminalListSubsets {alpha : Type}
    (items : List alpha) (select : alpha -> Bool) :
    items.filter select ∈ terminalListSubsets items := by
  induction items with
  | nil =>
      exact List.Mem.head []
  | cons head tail ih =>
      unfold terminalListSubsets
      cases checked : select head with
      | false =>
          simp only [List.filter, checked]
          exact List.mem_append_left _ ih
      | true =>
          simp only [List.filter, checked]
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨tail.filter select, ih, rfl⟩

/-- Every canonical terminal-record seed, in primitive-universe order. -/
def allTerminalSupportSeeds
    (inputs gates outputs profileWidth : Nat) :
    List (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  terminalListSubsets
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth)

/-- Canonical list representative of a Boolean-selected primitive-record set. -/
def canonicalTerminalSupportSeed
    (inputs gates outputs profileWidth : Nat)
    (select : TerminalPrimitiveRecord inputs gates outputs profileWidth -> Bool) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter select

/-- Every Boolean-selected primitive-record set occurs in the exhaustive seed
    universe. -/
theorem canonicalTerminalSupportSeed_mem
    (inputs gates outputs profileWidth : Nat)
    (select : TerminalPrimitiveRecord inputs gates outputs profileWidth -> Bool) :
    canonicalTerminalSupportSeed inputs gates outputs profileWidth select ∈
      allTerminalSupportSeeds inputs gates outputs profileWidth :=
  filter_mem_terminalListSubsets
    (allTerminalPrimitiveRecords inputs gates outputs profileWidth) select

/-- The canonical seed contains exactly the records accepted by its selector. -/
theorem mem_canonicalTerminalSupportSeed_iff
    {inputs gates outputs profileWidth : Nat}
    (select : TerminalPrimitiveRecord inputs gates outputs profileWidth -> Bool)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ canonicalTerminalSupportSeed inputs gates outputs profileWidth select ↔
      select record = true := by
  unfold canonicalTerminalSupportSeed
  constructor
  · intro member
    exact (List.mem_filter.mp member).2
  · intro checked
    exact List.mem_filter.mpr
      ⟨mem_allTerminalPrimitiveRecords record, checked⟩

/-! ## Exact local gain and qualification -/

/-- Exact local gain of the saturated extracted open support.  This is the
    extracted gate count minus the exhaustive minimum for the same boundary,
    interface, and open Boolean semantics. -/
def terminalSupportLocalGain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Nat :=
  let extracted := extractSaturatedTerminalSupport candidate system seed
  residualSlack extracted.extractedCandidate.toImplementation

/-- A terminal seed is proper when its saturated extraction selects at least
    one gate but not every gate of the ambient candidate. -/
def TerminalSupportProper
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  let extracted := extractSaturatedTerminalSupport candidate system seed
  0 < extracted.gateCount ∧ extracted.gateCount < gates

/-- A terminal seed is positive when its exact local gain is positive. -/
def TerminalSupportPositive
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  0 < terminalSupportLocalGain candidate system seed

private def terminalProperPositiveDecidable
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Decidable (TerminalSupportProper candidate system seed ∧
      TerminalSupportPositive candidate system seed) := by
  unfold TerminalSupportProper TerminalSupportPositive terminalSupportLocalGain
  infer_instance

/-- Executable proper-positive qualification test. -/
def terminalProperPositiveSupportBool
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  @decide
    (TerminalSupportProper candidate system seed ∧
      TerminalSupportPositive candidate system seed)
    (terminalProperPositiveDecidable candidate system seed)

/-- The executable test has exactly the intended proper-positive meaning. -/
theorem terminalProperPositiveSupportBool_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalProperPositiveSupportBool candidate system seed = true ↔
      TerminalSupportProper candidate system seed ∧
        TerminalSupportPositive candidate system seed := by
  unfold terminalProperPositiveSupportBool
  constructor
  · exact fun checked =>
      @of_decide_eq_true _
        (terminalProperPositiveDecidable candidate system seed) checked
  · exact fun qualified =>
      @decide_eq_true _
        (terminalProperPositiveDecidable candidate system seed) qualified

/-! ## Deterministic exhaustive search -/

private structure TerminalProperPositiveSeedResult
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seeds : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) where
  seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  member : seed ∈ seeds
  proper : TerminalSupportProper candidate system seed
  positive : TerminalSupportPositive candidate system seed

private def firstTerminalProperPositiveSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    (seeds : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) ->
      Option (TerminalProperPositiveSeedResult candidate system seeds)
  | [] => none
  | seed :: seeds =>
      if checked :
          terminalProperPositiveSupportBool candidate system seed = true then
        let qualified :=
          (terminalProperPositiveSupportBool_eq_true_iff
            candidate system seed).1 checked
        some
          { seed := seed
            member := List.Mem.head seeds
            proper := qualified.1
            positive := qualified.2 }
      else
        match firstTerminalProperPositiveSupport candidate system seeds with
        | none => none
        | some found =>
            some
              { seed := found.seed
                member := List.Mem.tail seed found.member
                proper := found.proper
                positive := found.positive }

private theorem firstTerminalProperPositiveSupport_exists_of_mem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {seeds : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))}
    (member : seed ∈ seeds)
    (proper : TerminalSupportProper candidate system seed)
    (positive : TerminalSupportPositive candidate system seed) :
    ∃ found, firstTerminalProperPositiveSupport candidate system seeds =
      some found := by
  induction seeds generalizing seed with
  | nil => cases member
  | cons head tail ih =>
      cases List.mem_cons.mp member with
      | inl equal =>
          subst seed
          let checked := (terminalProperPositiveSupportBool_eq_true_iff
            candidate system head).2 ⟨proper, positive⟩
          let qualified := (terminalProperPositiveSupportBool_eq_true_iff
            candidate system head).1 checked
          refine ⟨
            { seed := head
              member := List.Mem.head tail
              proper := qualified.1
              positive := qualified.2 }, ?_⟩
          unfold firstTerminalProperPositiveSupport
          rw [dif_pos checked]
      | inr tailMember =>
          if headQualified :
              terminalProperPositiveSupportBool candidate system head = true then
            let qualified := (terminalProperPositiveSupportBool_eq_true_iff
              candidate system head).1 headQualified
            refine ⟨
              { seed := head
                member := List.Mem.head tail
                proper := qualified.1
                positive := qualified.2 }, ?_⟩
            unfold firstTerminalProperPositiveSupport
            rw [dif_pos headQualified]
          else
            obtain ⟨found, foundAt⟩ := ih tailMember proper positive
            refine ⟨
              { seed := found.seed
                member := List.Mem.tail head found.member
                proper := found.proper
                positive := found.positive }, ?_⟩
            unfold firstTerminalProperPositiveSupport
            rw [dif_neg headQualified, foundAt]

/-- Proof-bearing result of the governed proper-positive support search. -/
structure TerminalProperPositiveSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) where
  seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  governed : seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth
  proper : TerminalSupportProper candidate system seed
  positive : TerminalSupportPositive candidate system seed

/-- Exhaustively search all canonical terminal seeds and return the first
    governed proper-positive result. -/
def findTerminalProperPositiveSupport
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    Option (TerminalProperPositiveSupport candidate system) :=
  match firstTerminalProperPositiveSupport candidate system
      (allTerminalSupportSeeds inputs gates outputs profileWidth) with
  | none => none
  | some found =>
      some
        { seed := found.seed
          governed := found.member
          proper := found.proper
          positive := found.positive }

/-- Every returned search result carries exact governance, properness, and
    positivity evidence. -/
theorem findTerminalProperPositiveSupport_sound
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (found : TerminalProperPositiveSupport candidate system)
    (_foundAt : findTerminalProperPositiveSupport candidate system = some found) :
    found.seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      TerminalSupportProper candidate system found.seed ∧
        TerminalSupportPositive candidate system found.seed :=
  ⟨found.governed, found.proper, found.positive⟩

/-- Any governed proper-positive seed forces the exhaustive search to return
    a proof-bearing result. -/
theorem findTerminalProperPositiveSupport_exists_of_seed
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (governed : seed ∈
      allTerminalSupportSeeds inputs gates outputs profileWidth)
    (proper : TerminalSupportProper candidate system seed)
    (positive : TerminalSupportPositive candidate system seed) :
    ∃ found, findTerminalProperPositiveSupport candidate system = some found := by
  obtain ⟨foundSeed, foundAt⟩ :=
    firstTerminalProperPositiveSupport_exists_of_mem candidate system
      governed proper positive
  unfold findTerminalProperPositiveSupport
  simp only [foundAt]
  exact ⟨_, rfl⟩

/-- Search failure is equivalent to absence of every governed proper-positive
    support.  Thus `none` cannot hide an omitted canonical seed. -/
theorem findTerminalProperPositiveSupport_eq_none_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) :
    findTerminalProperPositiveSupport candidate system = none ↔
      ∀ seed,
        seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ->
        ¬(TerminalSupportProper candidate system seed ∧
          TerminalSupportPositive candidate system seed) := by
  constructor
  · intro notFound seed governed qualified
    obtain ⟨found, foundAt⟩ :=
      findTerminalProperPositiveSupport_exists_of_seed candidate system
        governed qualified.1 qualified.2
    rw [notFound] at foundAt
    cases foundAt
  · intro absent
    cases foundAt : findTerminalProperPositiveSupport candidate system with
    | none => rfl
    | some found =>
        have sound := findTerminalProperPositiveSupport_sound
          candidate system found foundAt
        exact False.elim (absent found.seed sound.1 ⟨sound.2.1, sound.2.2⟩)

/-- The canonical search has at most one proof-bearing first result. -/
theorem findTerminalProperPositiveSupport_unique
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    {left right : TerminalProperPositiveSupport candidate system}
    (leftAt : findTerminalProperPositiveSupport candidate system = some left)
    (rightAt : findTerminalProperPositiveSupport candidate system = some right) :
    left = right :=
  Option.some.inj (leftAt.symm.trans rightAt)

/-! ## Properties of every returned support -/

/-- The exact executable saturated record list carried by a result. -/
def TerminalProperPositiveSupport.saturatedRecords
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :=
  terminalSaturateRecords system support.seed

/-- The exact open circuit extracted from a result's saturated records. -/
def TerminalProperPositiveSupport.extractedSupport
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :=
  extractSaturatedTerminalSupport candidate system support.seed

/-- A returned support's executable record set is closed under every governed
    dependency edge. -/
theorem TerminalProperPositiveSupport.saturatedRecords_closed
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :
    TerminalRawSupport.Closed
      (fun record => record ∈ support.saturatedRecords) system :=
  terminalSaturateRecords_closed system support.seed

/-- Saturation followed by physical completion is compatible for every search
    result. -/
theorem TerminalProperPositiveSupport.physically_compatible
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :
    (completeSaturatedTerminalPhysicalSupport candidate system support.seed).Compatible :=
  completeSaturatedTerminalPhysicalSupport_compatible candidate system support.seed

/-- The extracted gate count is nonzero and strictly below the ambient gate
    count. -/
theorem TerminalProperPositiveSupport.gateCount_bounds
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :
    0 < support.extractedSupport.gateCount ∧
      support.extractedSupport.gateCount < gates :=
  support.proper

/-- Every extracted result denotes the independently defined open support
    function on every boundary valuation and interface coordinate. -/
theorem TerminalProperPositiveSupport.extracted_semantics
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system)
    (boundaryValuation : Valuation
      (terminalBoundaryPorts candidate.program support.saturatedRecords).length)
    (output : Fin
      (terminalInterfacePorts candidate support.saturatedRecords).length) :
    support.extractedSupport.extractedCandidate.semantics
        boundaryValuation output =
      terminalOpenSupportSemantics candidate support.saturatedRecords
        boundaryValuation output :=
  extractSaturatedTerminalSupport_semantics candidate system support.seed
    boundaryValuation output

/-- Under a boundary induced by a whole-circuit input, every extracted output
    recovers the corresponding original gate value. -/
theorem TerminalProperPositiveSupport.extracted_induced
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system)
    (input : Valuation inputs)
    (output : Fin
      (terminalInterfacePorts candidate support.saturatedRecords).length) :
    support.extractedSupport.extractedCandidate.semantics
        (terminalInducedBoundaryValuation candidate support.saturatedRecords input)
        output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate support.saturatedRecords).get output) :=
  extractSaturatedTerminalSupport_induced candidate system support.seed input output

/-- Exact reference-minimum replacement for the extracted open circuit. -/
def TerminalProperPositiveSupport.minimumReplacement
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :=
  support.extractedSupport.extractedCandidate.referenceMinimumReplacement

/-- The exact minimum replacement has the same open Boolean semantics. -/
theorem TerminalProperPositiveSupport.minimumReplacement_equivalent
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :
    Equivalent support.minimumReplacement.program
        support.minimumReplacement.directWireWord
      support.extractedSupport.extractedCandidate.program
        support.extractedSupport.extractedCandidate.directWireWord :=
  Candidate.referenceMinimumReplacement_equivalent
    support.extractedSupport.extractedCandidate

/-- Positive local gain means the exact open minimum is strictly smaller than
    the extracted support. -/
theorem TerminalProperPositiveSupport.referenceMinimum_lt_gateCount
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :
    referenceMinimum support.extractedSupport.extractedCandidate.toImplementation <
      support.extractedSupport.gateCount := by
  have positive := support.positive
  unfold TerminalSupportPositive terminalSupportLocalGain at positive
  unfold residualSlack at positive
  exact Nat.sub_pos_iff_lt.mp positive

/-- The reference-minimum replacement contains strictly fewer NAND gates than
    the extracted support. -/
theorem TerminalProperPositiveSupport.minimumReplacement_size_lt
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (support : TerminalProperPositiveSupport candidate system) :
    support.minimumReplacement.program.size <
      support.extractedSupport.extractedCandidate.program.size := by
  change
    (support.extractedSupport.extractedCandidate.referenceMinimumReplacement).program.size <
      support.extractedSupport.extractedCandidate.program.size
  rw [Candidate.referenceMinimumReplacement_size]
  rw [Candidate.program_size_eq_gateCount]
  exact support.referenceMinimum_lt_gateCount

end DirectWire
end PNP
