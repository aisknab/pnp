/-
Copyright (c) 2026 PNP Labs.

Semantic output conditions forcing a direct-wire implementation to expose at
least one distinct NAND gate per output.  The finite pigeonhole argument is
constructive and the resulting bound is independent of any locked-circuit
construction.
-/

import PNP.NANDMinimum

namespace PNP
namespace DirectWire

/-- One output is not a constant Boolean function. -/
def OutputNonconstant {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (output : Fin outputs) : Prop :=
  ∃ leftInput rightInput,
    candidate.semantics leftInput output ≠
      candidate.semantics rightInput output

/-- One output is not any positive primary-input projection. -/
def OutputNotPositiveProjection {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (output : Fin outputs) : Prop :=
  ∀ input : Fin inputs, ∃ valuation,
    candidate.semantics valuation output ≠ valuation input

/-- Two output coordinates denote distinct Boolean functions. -/
def OutputPairwiseDistinct {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) : Prop :=
  ∀ {leftOutput rightOutput : Fin outputs},
    leftOutput ≠ rightOutput →
      ∃ valuation,
        candidate.semantics valuation leftOutput ≠
          candidate.semantics valuation rightOutput

/-- The semantic baseline conditions used by the direct-wire lower bound. -/
structure BaselineOutputConditions {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) : Prop where
  nonconstant : ∀ output, OutputNonconstant candidate output
  notPositiveProjection : ∀ output,
    OutputNotPositiveProjection candidate output
  pairwiseDistinct : OutputPairwiseDistinct candidate

/-- A constant output source contradicts semantic nonconstancy. -/
theorem outputSource_not_constant {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate)
    (output : Fin outputs) (value : Bool) :
    candidate.directWireWord.source output ≠ .constant value := by
  intro sourceEqual
  obtain ⟨leftInput, rightInput, different⟩ :=
    conditions.nonconstant output
  apply different
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [sourceEqual]
  rfl

/-- A primary-input source contradicts the no-positive-projection condition. -/
theorem outputSource_not_input {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate)
    (output : Fin outputs) (input : Fin inputs) :
    candidate.directWireWord.source output ≠ .input input := by
  intro sourceEqual
  obtain ⟨valuation, different⟩ :=
    conditions.notPositiveProjection output input
  apply different
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [sourceEqual]
  rfl

/-- Every output satisfying the baseline conditions is wired from a gate. -/
theorem outputSource_isGate {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate)
    (output : Fin outputs) :
    ∃ gate : Fin gates,
      candidate.directWireWord.source output = .gate gate := by
  cases sourceEqual : candidate.directWireWord.source output with
  | input input =>
      exact False.elim
        (outputSource_not_input candidate conditions output input sourceEqual)
  | constant value =>
      exact False.elim
        (outputSource_not_constant candidate conditions output value sourceEqual)
  | gate gate => exact ⟨gate, rfl⟩

/-- Extract a gate index from a source after excluding both non-gate forms. -/
def Source.gateIndexOfNontrivial {inputs gates : Nat}
    (source : Source inputs gates)
    (notInput : ∀ input, source ≠ .input input)
    (notConstant : ∀ value, source ≠ .constant value) : Fin gates :=
  match source with
  | .input index => False.elim (notInput index rfl)
  | .constant boolValue => False.elim (notConstant boolValue rfl)
  | .gate gateIndex => gateIndex

/-- The extracted index reconstructs the original nontrivial source. -/
theorem Source.gateIndexOfNontrivial_source {inputs gates : Nat}
    (source : Source inputs gates)
    (notInput : ∀ input, source ≠ .input input)
    (notConstant : ∀ value, source ≠ .constant value) :
    source = .gate (source.gateIndexOfNontrivial notInput notConstant) := by
  cases source with
  | input index => exact False.elim (notInput index rfl)
  | constant value => exact False.elim (notConstant value rfl)
  | gate gate => rfl

/-- Extract the gate selected by an output.  Non-gate branches are impossible
    by the semantic baseline conditions. -/
def outputGateIndex {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate)
    (output : Fin outputs) : Fin gates :=
  (candidate.directWireWord.source output).gateIndexOfNontrivial
    (outputSource_not_input candidate conditions output)
    (outputSource_not_constant candidate conditions output)

/-- Extraction remembers the exact gate source selected by the output. -/
theorem outputGateIndex_source {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate)
    (output : Fin outputs) :
    candidate.directWireWord.source output =
      .gate (outputGateIndex candidate conditions output) := by
  unfold outputGateIndex
  exact Source.gateIndexOfNontrivial_source
    (candidate.directWireWord.source output)
    (outputSource_not_input candidate conditions output)
    (outputSource_not_constant candidate conditions output)

/-- Pairwise-distinct output functions select pairwise-distinct gate indices. -/
theorem outputGateIndex_injective {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate) :
    Function.Injective (outputGateIndex candidate conditions) := by
  intro leftOutput rightOutput gateEqual
  if outputEqual : leftOutput = rightOutput then
    exact outputEqual
  else
    obtain ⟨valuation, different⟩ :=
      conditions.pairwiseDistinct outputEqual
    apply False.elim
    apply different
    unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
    rw [outputGateIndex_source candidate conditions leftOutput]
    rw [outputGateIndex_source candidate conditions rightOutput]
    rw [gateEqual]

/-- Constructively remove one witnessed list member while retaining every
    different item. -/
theorem listRemoveWitness {alpha : Type} {chosen : alpha} {items : List alpha}
    (member : chosen ∈ items) :
    ∃ remainder : List alpha,
      items.length = remainder.length + 1 ∧
      ∀ item, item ∈ items → item ≠ chosen → item ∈ remainder := by
  induction member with
  | head =>
      refine ⟨_, rfl, ?_⟩
      intro item itemMember itemDifferent
      cases itemMember with
      | head => exact False.elim (itemDifferent rfl)
      | tail _ tailMember => exact tailMember
  | tail head _ ih =>
      obtain ⟨remainder, lengthEqual, retained⟩ := ih
      refine ⟨head :: remainder, ?_, ?_⟩
      · exact congrArg Nat.succ lengthEqual
      · intro item itemMember itemDifferent
        cases itemMember with
        | head => exact List.Mem.head _
        | tail _ tailMember =>
            exact List.Mem.tail head
              (retained item tailMember itemDifferent)

/-- Constructive duplicate-freedom, stated without library pairwise helpers. -/
inductive ListNoDuplicates {alpha : Type} : List alpha → Prop where
  | nil : ListNoDuplicates []
  | cons {head : alpha} {tail : List alpha} :
      (head ∈ tail → False) → ListNoDuplicates tail →
        ListNoDuplicates (head :: tail)

/-- A duplicate-free list embedded into another list cannot be longer. -/
theorem noDuplicatesSubset_length_le {alpha : Type}
    (items available : List alpha)
    (noDuplicates : ListNoDuplicates items)
    (subset : ∀ item, item ∈ items → item ∈ available) :
    items.length ≤ available.length := by
  induction items generalizing available with
  | nil => exact Nat.zero_le available.length
  | cons head tail ih =>
      cases noDuplicates with
      | cons headAbsent tailNoDuplicates =>
          obtain ⟨remainder, lengthEqual, retained⟩ :=
            listRemoveWitness (subset head (List.Mem.head _))
          have tailSubset : ∀ item, item ∈ tail → item ∈ remainder := by
            intro item itemMember
            apply retained item
            · exact subset item (List.Mem.tail head itemMember)
            · intro itemEqual
              apply headAbsent
              rw [← itemEqual]
              exact itemMember
          have tailBound : tail.length ≤ remainder.length :=
            ih remainder tailNoDuplicates tailSubset
          change Nat.succ tail.length ≤ available.length
          rw [lengthEqual]
          exact Nat.succ_le_succ tailBound

/-- Recover a preimage from membership in a mapped list. -/
theorem mem_map_preimage {alpha beta : Type}
    (function : alpha → beta) (items : List alpha) {mapped : beta}
    (member : mapped ∈ items.map function) :
    ∃ item, item ∈ items ∧ function item = mapped := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      cases member with
      | head => exact ⟨head, List.Mem.head _, rfl⟩
      | tail _ tailMember =>
          obtain ⟨item, itemMember, mappedEqual⟩ := ih tailMember
          exact ⟨item, List.Mem.tail head itemMember, mappedEqual⟩

/-- Mapping a list preserves its length. -/
theorem listMap_length {alpha beta : Type}
    (function : alpha → beta) (items : List alpha) :
    (items.map function).length = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

/-- Mapping an injective function preserves duplicate-freedom. -/
theorem noDuplicates_map_of_injective {alpha beta : Type}
    (function : alpha → beta) (injective : Function.Injective function)
    (items : List alpha) (noDuplicates : ListNoDuplicates items) :
    ListNoDuplicates (items.map function) := by
  induction noDuplicates with
  | nil => exact ListNoDuplicates.nil
  | @cons head tail headAbsent tailNoDuplicates ih =>
      apply ListNoDuplicates.cons
      · intro headMember
        obtain ⟨item, itemMember, mappedEqual⟩ :=
          mem_map_preimage function tail headMember
        apply headAbsent
        have itemEqual : item = head := injective mappedEqual
        rw [← itemEqual]
        exact itemMember
      · exact ih

/-- The canonical finite-index list has exactly the indexed length. -/
theorem allFin_length (width : Nat) :
    (allFin width).length = width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      unfold allFin
      change Nat.succ ((allFin width).map Fin.succ).length = Nat.succ width
      exact congrArg Nat.succ
        ((listMap_length Fin.succ (allFin width)).trans ih)

/-- The canonical finite-index list contains no duplicate indices. -/
theorem allFin_noDuplicates (width : Nat) :
    ListNoDuplicates (allFin width) := by
  induction width with
  | zero => exact ListNoDuplicates.nil
  | succ width ih =>
      unfold allFin
      apply ListNoDuplicates.cons
      · intro zeroMember
        obtain ⟨index, _indexMember, impossible⟩ :=
          mem_map_preimage Fin.succ (allFin width) zeroMember
        have valueImpossible := congrArg Fin.val impossible
        exact Nat.noConfusion valueImpossible
      · apply noDuplicates_map_of_injective Fin.succ
          (fun left right equal => by
            apply Fin.ext
            exact Nat.succ.inj (congrArg Fin.val equal))
          (allFin width) ih

/-- Constructive finite pigeonhole: an injection between finite indices gives
    the corresponding cardinal inequality. -/
theorem finCard_le_of_injective {domain codomain : Nat}
    (mapping : Fin domain → Fin codomain)
    (injective : Function.Injective mapping) : domain ≤ codomain := by
  let image := (allFin domain).map mapping
  have imageNoDuplicates : ListNoDuplicates image :=
    noDuplicates_map_of_injective mapping injective (allFin domain)
      (allFin_noDuplicates domain)
  have imageSubset : ∀ item, item ∈ image → item ∈ allFin codomain := by
    intro item _itemMember
    exact mem_allFin item
  have lengthBound := noDuplicatesSubset_length_le image (allFin codomain)
    imageNoDuplicates imageSubset
  unfold image at lengthBound
  rw [listMap_length, allFin_length, allFin_length] at lengthBound
  exact lengthBound

/-- The baseline conditions extract an injective output-to-gate map. -/
theorem outputGateEmbedding {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate) :
    ∃ mapping : Fin outputs → Fin gates,
      (∀ output,
        candidate.directWireWord.source output = .gate (mapping output)) ∧
      Function.Injective mapping := by
  refine ⟨outputGateIndex candidate conditions, ?_, ?_⟩
  · exact outputGateIndex_source candidate conditions
  · exact outputGateIndex_injective candidate conditions

/-- Every direct-wire candidate satisfying the semantic baseline conditions
    uses at least as many gates as it exposes outputs. -/
theorem outputCount_le_gateCount {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate) : outputs ≤ gates :=
  finCard_le_of_injective (outputGateIndex candidate conditions)
    (outputGateIndex_injective candidate conditions)

/-- The baseline output conditions transport from a semantically equivalent
    target to the candidate on the left. -/
theorem BaselineOutputConditions.of_equivalent
    {inputs leftGates rightGates outputs : Nat}
    {left : Candidate inputs leftGates outputs}
    {right : Candidate inputs rightGates outputs}
    (rightConditions : BaselineOutputConditions right)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord) :
    BaselineOutputConditions left := by
  constructor
  · intro output
    obtain ⟨leftInput, rightInput, different⟩ :=
      rightConditions.nonconstant output
    refine ⟨leftInput, rightInput, ?_⟩
    intro leftEqual
    apply different
    exact (equivalent leftInput output).symm.trans
      (leftEqual.trans (equivalent rightInput output))
  · intro output input
    obtain ⟨valuation, different⟩ :=
      rightConditions.notPositiveProjection output input
    refine ⟨valuation, ?_⟩
    intro leftEqual
    apply different
    exact (equivalent valuation output).symm.trans leftEqual
  · intro leftOutput rightOutput outputDifferent
    obtain ⟨valuation, different⟩ :=
      rightConditions.pairwiseDistinct outputDifferent
    refine ⟨valuation, ?_⟩
    intro leftEqual
    apply different
    exact (equivalent valuation leftOutput).symm.trans
      (leftEqual.trans (equivalent valuation rightOutput))

/-- A square candidate with the baseline output conditions has exact exhaustive
    reference minimum equal to its number of outputs and gates. -/
theorem referenceMinimum_eq_gateCount_of_squareBaseline
    {inputs baseline : Nat}
    (candidate : Candidate inputs baseline baseline)
    (conditions : BaselineOutputConditions candidate) :
    referenceMinimum (Implementation.mk baseline candidate) = baseline := by
  let target : Implementation inputs baseline := ⟨baseline, candidate⟩
  have witnessEquivalent : Equivalent
      (referenceMinimumWitness target).program
      (referenceMinimumWitness target).directWireWord
      candidate.program candidate.directWireWord :=
    equivalentBool_sound (referenceMinimumWitness_equivalent target)
  have witnessConditions :
      BaselineOutputConditions (referenceMinimumWitness target) :=
    conditions.of_equivalent witnessEquivalent
  have baselineLowerBound : baseline ≤ referenceMinimum target :=
    outputCount_le_gateCount (referenceMinimumWitness target) witnessConditions
  have minimumUpperBound : referenceMinimum target ≤ baseline :=
    referenceMinimum_le_target target
  exact Nat.le_antisymm minimumUpperBound baselineLowerBound

end DirectWire
end PNP
