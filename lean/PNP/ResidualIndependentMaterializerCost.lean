/-
Copyright (c) 2026 PNP Labs.

Independent computational NAND materializers beside an arbitrary direct-wire
circuit. Fresh primary inputs are real Boolean inputs, not proof/profile data.
This module does not replace the terminal profile system or assert global
saturation transparency, polynomial PCCMin, SAT in P, or P = NP.
-/

import PNP.DirectWireBaseline
import PNP.NANDSlack

namespace PNP
namespace DirectWire

private def independentNandPrefix (total : Nat) :
    (count : Nat) → count ≤ total → Program (total + total) count
  | 0, _within => .empty
  | count + 1, within =>
      let index : Fin total := ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) within⟩
      .snoc (independentNandPrefix total count (Nat.le_of_succ_le within))
        ⟨.input (Fin.castAdd total index), .input (Fin.natAdd total index)⟩

private theorem independentNandPrefix_eval
    (total count : Nat) (within : count ≤ total)
    (valuation : Valuation (total + total)) (index : Fin count) :
    (independentNandPrefix total count within).eval valuation index =
      boolNand
        (valuation (Fin.castAdd total
          ⟨index.val, Nat.lt_of_lt_of_le index.isLt within⟩))
        (valuation (Fin.natAdd total
          ⟨index.val, Nat.lt_of_lt_of_le index.isLt within⟩)) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      if earlier : index.val < count then
        let previous : Fin count := ⟨index.val, earlier⟩
        have indexEqual : index = previous.castSucc := Fin.ext rfl
        rw [indexEqual]
        change (Program.snoc
          (independentNandPrefix total count (Nat.le_of_succ_le within)) _).eval
            valuation previous.castSucc = _
        rw [Program.eval_snoc_castSucc]
        exact ih (Nat.le_of_succ_le within) previous
      else
        have indexEqual : index = Fin.last count := by
          apply Fin.ext
          have upper := index.isLt
          simp only [Fin.val_last]
          omega
        subst index
        change (Program.snoc
          (independentNandPrefix total count (Nat.le_of_succ_le within)) _).eval
            valuation (Fin.last count) = _
        rw [Program.eval_snoc_last]
        rfl

/-- Append one independent NAND per fresh input pair, keeping every original
    output in order. No materializer or correctness certificate is supplied. -/
def appendIndependentNandMaterializers
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    Candidate (inputs + (count + count)) (gates + count) (outputs + count) :=
  let initial := candidate.program.renameInputs (Fin.castAdd (count + count))
  let program := initial.appendSubstituted
    (fun input => Source.input (Fin.natAdd inputs input))
    (independentNandPrefix count count (Nat.le_refl count))
  let word : DirectWireWord (inputs + (count + count))
      (gates + count) (outputs + count) :=
    ⟨splitFin
      (fun output => ((candidate.directWireWord.source output).renameInputs
        (Fin.castAdd (count + count))).weakenGates count)
      (fun output => Source.gate (Fin.natAdd gates output))⟩
  Candidate.ofDirectWireWord program word

/-- The construction adds exactly the declared number of physical NAND gates. -/
theorem appendIndependentNandMaterializers_size
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    (appendIndependentNandMaterializers candidate count).program.size =
      gates + count :=
  Program.size_eq_gateCount _

/-- Every original ordered output ignores the newly introduced input pairs. -/
theorem appendIndependentNandMaterializers_original
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat)
    (valuation : Valuation (inputs + (count + count))) (output : Fin outputs) :
    (appendIndependentNandMaterializers candidate count).semantics valuation
        (Fin.castAdd count output) =
      candidate.semantics
        (fun input => valuation (Fin.castAdd (count + count) input)) output := by
  simp only [appendIndependentNandMaterializers, Candidate.ofDirectWireWord_semantics,
    DirectWire.semantics, DirectWireWord.eval, splitFin_left,
    Source.eval_weakenGates, Source.eval_renameInputs,
    Program.eval_appendSubstituted_prefix, Program.eval_renameInputs]
  rfl

/-- Every added output is the NAND of its own pair of fresh primary inputs. -/
theorem appendIndependentNandMaterializers_materializer
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat)
    (valuation : Valuation (inputs + (count + count))) (output : Fin count) :
    (appendIndependentNandMaterializers candidate count).semantics valuation
        (Fin.natAdd outputs output) =
      boolNand
        (valuation (Fin.natAdd inputs (Fin.castAdd count output)))
        (valuation (Fin.natAdd inputs (Fin.natAdd count output))) := by
  simp only [appendIndependentNandMaterializers, Candidate.ofDirectWireWord_semantics,
    DirectWire.semantics, DirectWireWord.eval, splitFin_right, Source.eval,
    Program.eval_appendSubstituted_suffix]
  exact independentNandPrefix_eval count count (Nat.le_refl count)
    (fun input => valuation (Fin.natAdd inputs input)) output

/-! ## Semantic erasure under an input restriction -/

private structure MaterializerGateErasure (originalGates inputs : Nat) where
  gateCount : Nat
  program : Program inputs gateCount
  image : Fin originalGates → Source inputs gateCount

private def materializerErasureEvaluation
    {originalGates inputs : Nat}
    (result : MaterializerGateErasure originalGates inputs)
    (valuation : Valuation inputs) (index : Fin originalGates) : Bool :=
  (result.image index).eval valuation (result.program.eval valuation)

private def materializerInputLift {inputs gates : Nat} :
    Source inputs 0 → Source inputs gates
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => Fin.elim0 index

private def materializerRebindSource
    {originalInputs inputs originalGates gates : Nat}
    (binding : Fin originalInputs → Source inputs 0)
    (image : Fin originalGates → Source inputs gates) :
    Source originalInputs originalGates → Source inputs gates
  | .input index => materializerInputLift (binding index)
  | .constant value => .constant value
  | .gate index => image index

private theorem materializerRebindSource_eval
    {originalInputs inputs originalGates gates : Nat}
    (binding : Fin originalInputs → Source inputs 0)
    (image : Fin originalGates → Source inputs gates)
    (source : Source originalInputs originalGates)
    (valuation : Valuation inputs) (gateValues : Valuation gates)
    (originalValues : Valuation originalGates)
    (imageCorrect : ∀ index,
      (image index).eval valuation gateValues = originalValues index) :
    (materializerRebindSource binding image source).eval valuation gateValues =
      source.eval (fun input => (binding input).eval valuation Fin.elim0)
        originalValues := by
  cases source with
  | input index =>
      change (materializerInputLift (binding index)).eval valuation gateValues =
        (binding index).eval valuation Fin.elim0
      cases binding index with
      | input input => rfl
      | constant value => rfl
      | gate gate => exact Fin.elim0 gate
  | constant value => rfl
  | gate index => exact imageCorrect index

private def materializerEraseProgram
    {originalInputs inputs : Nat}
    (binding : Fin originalInputs → Source inputs 0) :
    {gates : Nat} → Program originalInputs gates →
      (Fin gates → Bool) → (Fin gates → Bool) →
      MaterializerGateErasure gates inputs
  | 0, .empty, _erase, _values =>
      ⟨0, .empty, Fin.elim0⟩
  | gates + 1, .snoc initial gate, erase, values =>
      let previous := materializerEraseProgram binding initial
        (fun index => erase index.castSucc) (fun index => values index.castSucc)
      if erase (Fin.last gates) = true then
        ⟨previous.gateCount, previous.program,
          splitFin previous.image (fun _ => .constant (values (Fin.last gates)))⟩
      else
        ⟨previous.gateCount + 1,
          .snoc previous.program
            ⟨materializerRebindSource binding previous.image gate.left,
              materializerRebindSource binding previous.image gate.right⟩,
          splitFin (fun index => (previous.image index).weakenGates 1)
            (fun _ => .gate (Fin.last previous.gateCount))⟩

private def materializerRetainedGateCount :
    (gates : Nat) → (Fin gates → Bool) → Nat
  | 0, _erase => 0
  | gates + 1, erase =>
      materializerRetainedGateCount gates (fun index => erase index.castSucc) +
        (if erase (Fin.last gates) = true then 0 else 1)

private theorem materializerEraseProgram_count
    {originalInputs inputs gates : Nat}
    (binding : Fin originalInputs → Source inputs 0)
    (program : Program originalInputs gates)
    (erase values : Fin gates → Bool) :
    (materializerEraseProgram binding program erase values).gateCount =
      materializerRetainedGateCount gates erase := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      by_cases lastErased : erase (Fin.last gates) = true
      · simpa only [materializerEraseProgram, materializerRetainedGateCount,
          if_pos lastErased, Nat.add_zero] using
          ih (fun index => erase index.castSucc) (fun index => values index.castSucc)
      · simpa only [materializerEraseProgram, materializerRetainedGateCount,
          if_neg lastErased] using
          congrArg (fun count => count + 1)
            (ih (fun index => erase index.castSucc) (fun index => values index.castSucc))

private theorem materializerEraseProgram_semantics
    {originalInputs inputs gates : Nat}
    (binding : Fin originalInputs → Source inputs 0)
    (program : Program originalInputs gates)
    (erase values : Fin gates → Bool)
    (valuation : Valuation inputs)
    (erasedConstant : ∀ index, erase index = true →
      program.eval (fun input => (binding input).eval valuation Fin.elim0) index =
        values index)
    (index : Fin gates) :
    ((materializerEraseProgram binding program erase values).image index).eval
        valuation ((materializerEraseProgram binding program erase values).program.eval valuation) =
      program.eval (fun input => (binding input).eval valuation Fin.elim0) index := by
  change materializerErasureEvaluation
    (materializerEraseProgram binding program erase values) valuation index = _
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      let previous := materializerEraseProgram binding initial
        (fun index => erase index.castSucc) (fun index => values index.castSucc)
      have previousConstant : ∀ index : Fin gates, erase index.castSucc = true →
          initial.eval (fun input => (binding input).eval valuation Fin.elim0) index =
            values index.castSucc := by
        intro index selected
        exact (Program.eval_snoc_castSucc initial gate _ index).symm.trans
          (erasedConstant index.castSucc selected)
      have previousSemantics : ∀ index : Fin gates,
          (previous.image index).eval valuation (previous.program.eval valuation) =
            initial.eval (fun input => (binding input).eval valuation Fin.elim0) index :=
        fun index => ih (fun index => erase index.castSucc)
          (fun index => values index.castSucc) previousConstant index
      rw [materializerEraseProgram.eq_2]
      by_cases lastErased : erase (Fin.last gates) = true
      · rw [if_pos lastErased]
        dsimp only [materializerErasureEvaluation]
        if earlier : index.val < gates then
          let old : Fin gates := ⟨index.val, earlier⟩
          have indexEqual : index = Fin.castAdd 1 old := Fin.ext rfl
          rw [indexEqual]
          simp only [splitFin_left]
          change (previous.image old).eval valuation (previous.program.eval valuation) =
            (initial.snoc gate).eval
              (fun input => (binding input).eval valuation Fin.elim0) old.castSucc
          rw [Program.eval_snoc_castSucc]
          exact previousSemantics old
        else
          have indexEqual : index = Fin.natAdd gates (0 : Fin 1) := by
            apply Fin.ext
            have upper := index.isLt
            simp only [Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
            omega
          rw [indexEqual]
          simp only [splitFin_right,
            Source.eval]
          exact (erasedConstant (Fin.last gates) lastErased).symm
      · rw [if_neg lastErased]
        dsimp only [materializerErasureEvaluation]
        if earlier : index.val < gates then
          let old : Fin gates := ⟨index.val, earlier⟩
          have indexEqual : index = Fin.castAdd 1 old := Fin.ext rfl
          rw [indexEqual]
          simp only [splitFin_left]
          let translated : Gate inputs previous.gateCount :=
            ⟨materializerRebindSource binding previous.image gate.left,
              materializerRebindSource binding previous.image gate.right⟩
          change ((previous.image old).weakenGates 1).eval valuation
              ((previous.program.snoc translated).eval valuation) =
            (initial.snoc gate).eval
              (fun input => (binding input).eval valuation Fin.elim0) old.castSucc
          rw [Source.eval_weakenGates, Program.eval_snoc_castSucc]
          have prefixValues : (fun index =>
              (previous.program.snoc translated).eval valuation (Fin.castAdd 1 index)) =
              previous.program.eval valuation := by
            funext index
            change (previous.program.snoc translated).eval valuation index.castSucc = _
            exact Program.eval_snoc_castSucc previous.program translated valuation index
          rw [prefixValues]
          exact previousSemantics old
        else
          have indexEqual : index = Fin.natAdd gates (0 : Fin 1) := by
            apply Fin.ext
            have upper := index.isLt
            simp only [Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
            omega
          rw [indexEqual]
          simp only [splitFin_right]
          let translated : Gate inputs previous.gateCount :=
            ⟨materializerRebindSource binding previous.image gate.left,
              materializerRebindSource binding previous.image gate.right⟩
          change (previous.program.snoc translated).eval valuation (Fin.last previous.gateCount) =
            (initial.snoc gate).eval
              (fun input => (binding input).eval valuation Fin.elim0) (Fin.last gates)
          rw [Program.eval_snoc_last, Program.eval_snoc_last]
          change boolNand
              ((materializerRebindSource binding previous.image gate.left).eval valuation
                (previous.program.eval valuation))
              ((materializerRebindSource binding previous.image gate.right).eval valuation
                (previous.program.eval valuation)) =
            boolNand
              (gate.left.eval (fun input => (binding input).eval valuation Fin.elim0)
                (initial.eval (fun input => (binding input).eval valuation Fin.elim0)))
              (gate.right.eval (fun input => (binding input).eval valuation Fin.elim0)
                (initial.eval (fun input => (binding input).eval valuation Fin.elim0)))
          rw [materializerRebindSource_eval binding previous.image gate.left
            valuation (previous.program.eval valuation) (initial.eval _) previousSemantics]
          rw [materializerRebindSource_eval binding previous.image gate.right
            valuation (previous.program.eval valuation) (initial.eval _) previousSemantics]

private def materializerEraseCandidate
    {originalInputs inputs gates outputs : Nat}
    (candidate : Candidate originalInputs gates outputs)
    (binding : Fin originalInputs → Source inputs 0)
    (erase values : Fin gates → Bool) : Implementation inputs outputs :=
  let result := materializerEraseProgram binding candidate.program erase values
  ⟨result.gateCount, Candidate.ofDirectWireWord result.program
    ⟨fun output => materializerRebindSource binding result.image
      (candidate.directWireWord.source output)⟩⟩

private theorem materializerEraseCandidate_semantics
    {originalInputs inputs gates outputs : Nat}
    (candidate : Candidate originalInputs gates outputs)
    (binding : Fin originalInputs → Source inputs 0)
    (erase values : Fin gates → Bool)
    (valuation : Valuation inputs)
    (erasedConstant : ∀ index, erase index = true →
      candidate.program.eval (fun input => (binding input).eval valuation Fin.elim0) index =
        values index)
    (output : Fin outputs) :
    (materializerEraseCandidate candidate binding erase values).candidate.semantics
        valuation output =
      candidate.semantics (fun input => (binding input).eval valuation Fin.elim0) output := by
  let result := materializerEraseProgram binding candidate.program erase values
  change (Candidate.ofDirectWireWord result.program
    ⟨fun index => materializerRebindSource binding result.image
      (candidate.directWireWord.source index)⟩).semantics valuation output = _
  rw [Candidate.ofDirectWireWord_semantics]
  change (materializerRebindSource binding result.image
      (candidate.directWireWord.source output)).eval valuation (result.program.eval valuation) =
    (candidate.directWireWord.source output).eval
      (fun input => (binding input).eval valuation Fin.elim0)
      (candidate.program.eval (fun input => (binding input).eval valuation Fin.elim0))
  exact materializerRebindSource_eval binding result.image
    (candidate.directWireWord.source output) valuation (result.program.eval valuation)
    (candidate.program.eval (fun input => (binding input).eval valuation Fin.elim0))
    (materializerEraseProgram_semantics binding candidate.program erase values valuation
      erasedConstant)

private theorem materializerAllFin_snoc (width : Nat) :
    allFin (width + 1) = (allFin width).map Fin.castSucc ++ [Fin.last width] := by
  induction width with
  | zero => rfl
  | succ width ih =>
      change (0 : Fin (width + 1 + 1)) :: (allFin (width + 1)).map Fin.succ =
        ((0 : Fin (width + 1)) :: (allFin width).map Fin.succ).map Fin.castSucc ++
          [Fin.last (width + 1)]
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
        List.cons_append]
      rfl

private theorem materializerRetainedGateCount_balance
    (gates : Nat) (erase : Fin gates → Bool) :
    materializerRetainedGateCount gates erase +
      ((allFin gates).filter erase).length = gates := by
  induction gates with
  | zero => rfl
  | succ gates ih =>
      have previous := ih (fun index => erase index.castSucc)
      rw [materializerRetainedGateCount, materializerAllFin_snoc]
      simp only [List.filter_append, List.length_append, List.filter_map, List.length_map,
        List.filter_cons, List.filter_nil, Function.comp_def]
      by_cases erased : erase (Fin.last gates) = true
      · simp only [erased, if_true, Nat.add_zero, List.length_cons, List.length_nil]
        omega
      · simp only [if_neg erased, List.length_nil, Nat.add_zero]
        omega

private def materializerOutputView
    {inputs gates outputs count : Nat}
    (candidate : Candidate inputs gates (outputs + count)) :
    Candidate inputs gates count :=
  Candidate.ofDirectWireWord candidate.program
    ⟨fun output => candidate.directWireWord.source (Fin.natAdd outputs output)⟩

private theorem materializerOutputView_semantics
    {inputs gates outputs count : Nat}
    (candidate : Candidate inputs gates (outputs + count))
    (valuation : Valuation inputs) (output : Fin count) :
    (materializerOutputView candidate).semantics valuation output =
      candidate.semantics valuation (Fin.natAdd outputs output) := by
  unfold materializerOutputView
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

private theorem materializerOutputView_conditions
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    BaselineOutputConditions
      (materializerOutputView (appendIndependentNandMaterializers candidate count)) := by
  constructor
  · intro output
    refine ⟨(fun _ => false), (fun _ => true), ?_⟩
    rw [materializerOutputView_semantics, materializerOutputView_semantics,
      appendIndependentNandMaterializers_materializer,
      appendIndependentNandMaterializers_materializer]
    decide
  · intro output input
    refine ⟨(fun _ => false), ?_⟩
    rw [materializerOutputView_semantics, appendIndependentNandMaterializers_materializer]
    change true ≠ false
    decide
  · intro left right different
    let valuation : Valuation (inputs + (count + count)) :=
      splitFin (fun _ => false)
        (splitFin (fun index : Fin count => decide (index = left))
          (fun index : Fin count => decide (index = left)))
    refine ⟨valuation, ?_⟩
    rw [materializerOutputView_semantics, materializerOutputView_semantics,
      appendIndependentNandMaterializers_materializer,
      appendIndependentNandMaterializers_materializer]
    simp only [valuation, splitFin_right, splitFin_left]
    have rightDifferent : right ≠ left := fun equal => different equal.symm
    simp [rightDifferent, boolNand]

private def materializerRestrictInputs (inputs count : Nat) :
    Fin (inputs + (count + count)) → Source inputs 0 :=
  splitFin Source.input (fun _ => .constant false)

private theorem materializerNoDuplicates_filter {alpha : Type}
    (predicate : alpha → Bool) (items : List alpha)
    (noDuplicates : ListNoDuplicates items) :
    ListNoDuplicates (items.filter predicate) := by
  induction noDuplicates with
  | nil => exact ListNoDuplicates.nil
  | @cons head tail headAbsent tailNoDuplicates ih =>
      by_cases retained : predicate head = true
      · rw [List.filter_cons, if_pos retained]
        exact ListNoDuplicates.cons
          (fun member => headAbsent (List.mem_filter.mp member).1) ih
      · rw [List.filter_cons, if_neg retained]
        exact ih

/-- Every competing realization pays the original minimum plus one gate for
    each independently materialized fresh NAND output. The competitor may have
    any topology, sharing pattern, gate order or number of gates. -/
theorem appendIndependentNandMaterializers_lower_bound
    {inputs gates outputs competingGates : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat)
    (competing : Candidate (inputs + (count + count)) competingGates (outputs + count))
    (equivalent : Equivalent competing.program competing.directWireWord
      (appendIndependentNandMaterializers candidate count).program
      (appendIndependentNandMaterializers candidate count).directWireWord) :
    referenceMinimum candidate.toImplementation + count ≤ competingGates := by
  let combined := appendIndependentNandMaterializers candidate count
  let view := materializerOutputView competing
  have viewEquivalent : Equivalent view.program view.directWireWord
      (materializerOutputView combined).program
      (materializerOutputView combined).directWireWord := by
    intro valuation output
    exact (materializerOutputView_semantics competing valuation output).trans
      ((equivalent valuation (Fin.natAdd outputs output)).trans
        (materializerOutputView_semantics combined valuation output).symm)
  let conditions : BaselineOutputConditions view :=
    (materializerOutputView_conditions candidate count).of_equivalent viewEquivalent
  let selected : List (Fin competingGates) :=
    (allFin count).map (outputGateIndex view conditions)
  let erase : Fin competingGates → Bool := fun gate => decide (gate ∈ selected)
  let binding := materializerRestrictInputs inputs count
  let removed := materializerEraseCandidate competing binding erase (fun _ => true)
  have selectedLength : selected.length = count :=
    (listMap_length (outputGateIndex view conditions) (allFin count)).trans (allFin_length count)
  have selectedNoDuplicates : ListNoDuplicates selected :=
    noDuplicates_map_of_injective (outputGateIndex view conditions)
      (outputGateIndex_injective view conditions) (allFin count) (allFin_noDuplicates count)
  have selectedSubset : ∀ gate, gate ∈ selected →
      gate ∈ (allFin competingGates).filter erase := by
    intro gate member
    apply List.mem_filter.mpr
    refine ⟨mem_allFin gate, ?_⟩
    change decide (gate ∈ selected) = true
    exact decide_eq_true member
  have removedCountLower : count ≤ ((allFin competingGates).filter erase).length := by
    rw [← selectedLength]
    exact noDuplicatesSubset_length_le selected ((allFin competingGates).filter erase)
      selectedNoDuplicates selectedSubset
  have erasedCount : ((allFin competingGates).filter erase).length = count := by
    apply Nat.le_antisymm
    · rw [← selectedLength]
      exact noDuplicatesSubset_length_le ((allFin competingGates).filter erase) selected
        (materializerNoDuplicates_filter erase (allFin competingGates)
          (allFin_noDuplicates competingGates))
        (fun _ member => of_decide_eq_true (List.mem_filter.mp member).2)
    · exact removedCountLower
  have erasedConstant : ∀ valuation : Valuation inputs, ∀ index,
      erase index = true →
        competing.program.eval
            (fun input => (binding input).eval valuation Fin.elim0) index = true := by
    intro valuation index selectedAt
    have member : index ∈ selected := of_decide_eq_true selectedAt
    obtain ⟨output, _outputMember, outputAt⟩ :=
      mem_map_preimage (outputGateIndex view conditions) (allFin count) member
    let restricted : Valuation (inputs + (count + count)) :=
      fun input => (binding input).eval valuation Fin.elim0
    have observed : view.semantics restricted output = true := by
      rw [materializerOutputView_semantics]
      change competing.semantics restricted (Fin.natAdd outputs output) = true
      have matched : competing.semantics restricted (Fin.natAdd outputs output) =
          (appendIndependentNandMaterializers candidate count).semantics restricted
            (Fin.natAdd outputs output) :=
        equivalent restricted (Fin.natAdd outputs output)
      rw [matched]
      rw [appendIndependentNandMaterializers_materializer]
      simp only [restricted, binding, materializerRestrictInputs, splitFin_right,
        Source.eval, boolNand, Bool.false_and, Bool.not_false]
    change (view.directWireWord.source output).eval restricted
      (view.program.eval restricted) = true at observed
    rw [outputGateIndex_source view conditions output] at observed
    change competing.program.eval restricted (outputGateIndex view conditions output) = true
      at observed
    rw [outputAt] at observed
    exact observed
  let original : Candidate inputs removed.gateCount outputs :=
    Candidate.ofDirectWireWord removed.candidate.program
      ⟨fun output => removed.candidate.directWireWord.source (Fin.castAdd count output)⟩
  have originalEquivalent : Equivalent original.program original.directWireWord
      candidate.program candidate.directWireWord := by
    intro valuation output
    change original.semantics valuation output = candidate.semantics valuation output
    calc
      original.semantics valuation output =
          removed.candidate.semantics valuation (Fin.castAdd count output) := by
        change (Candidate.ofDirectWireWord removed.candidate.program
          ⟨fun index => removed.candidate.directWireWord.source
            (Fin.castAdd count index)⟩).semantics valuation output = _
        rw [Candidate.ofDirectWireWord_semantics]
        rfl
      _ = competing.semantics
          (fun input => (binding input).eval valuation Fin.elim0)
          (Fin.castAdd count output) :=
        materializerEraseCandidate_semantics competing binding erase (fun _ => true)
          valuation (erasedConstant valuation) (Fin.castAdd count output)
      _ = combined.semantics
          (fun input => (binding input).eval valuation Fin.elim0)
          (Fin.castAdd count output) :=
        equivalent _ (Fin.castAdd count output)
      _ = candidate.semantics valuation output := by
        rw [appendIndependentNandMaterializers_original]
        have inputEqual : (fun input =>
            (binding (Fin.castAdd (count + count) input)).eval valuation Fin.elim0) =
            valuation := by
          funext input
          simp only [binding, materializerRestrictInputs, splitFin_left, Source.eval]
        rw [inputEqual]
  have minimumBound : referenceMinimum candidate.toImplementation ≤ removed.gateCount :=
    referenceMinimum_le_of_equivalent candidate.toImplementation original originalEquivalent
  have removedSize : removed.gateCount = materializerRetainedGateCount competingGates erase :=
    materializerEraseProgram_count binding competing.program erase (fun _ => true)
  have countBalance := materializerRetainedGateCount_balance competingGates erase
  rw [erasedCount] at countBalance
  rw [removedSize] at minimumBound
  omega

/-- Appending the same independent bank preserves complete ordered Boolean
    equivalence, including every original output and every fresh NAND output. -/
theorem appendIndependentNandMaterializers_equivalent
    {inputs leftGates rightGates outputs : Nat}
    (left : Candidate inputs leftGates outputs)
    (right : Candidate inputs rightGates outputs) (count : Nat)
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord) :
    Equivalent (appendIndependentNandMaterializers left count).program
      (appendIndependentNandMaterializers left count).directWireWord
      (appendIndependentNandMaterializers right count).program
      (appendIndependentNandMaterializers right count).directWireWord := by
  intro valuation output
  change (appendIndependentNandMaterializers left count).semantics valuation output =
    (appendIndependentNandMaterializers right count).semantics valuation output
  rcases finSum_decompose output with ⟨original, rfl⟩ | ⟨fresh, rfl⟩
  · rw [appendIndependentNandMaterializers_original,
      appendIndependentNandMaterializers_original]
    exact equivalent _ original
  · rw [appendIndependentNandMaterializers_materializer,
      appendIndependentNandMaterializers_materializer]

/-- Independent fresh NAND materializers increase the exhaustive semantic
    minimum by exactly their number, for an arbitrary original circuit.
    No original-minimality or competitor-layout assumption is required. -/
theorem appendIndependentNandMaterializers_referenceMinimum
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    referenceMinimum (appendIndependentNandMaterializers candidate count).toImplementation =
      referenceMinimum candidate.toImplementation + count := by
  apply Nat.le_antisymm
  · exact referenceMinimum_le_of_equivalent
      (appendIndependentNandMaterializers candidate count).toImplementation
      (appendIndependentNandMaterializers
        (referenceMinimumWitness candidate.toImplementation) count)
      (appendIndependentNandMaterializers_equivalent
        (referenceMinimumWitness candidate.toImplementation) candidate count
        (equivalentBool_sound (referenceMinimumWitness_equivalent candidate.toImplementation)))
  · exact appendIndependentNandMaterializers_lower_bound candidate count
      (referenceMinimumWitness
        (appendIndependentNandMaterializers candidate count).toImplementation)
      (equivalentBool_sound (referenceMinimumWitness_equivalent
        (appendIndependentNandMaterializers candidate count).toImplementation))

/-- The physical gate increase is paid exactly in the semantic minimum,
    so the original circuit's residual slack is preserved. This is not a
    statement about arbitrary profile materializers or global saturation. -/
theorem appendIndependentNandMaterializers_residualSlack
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (count : Nat) :
    residualSlack (appendIndependentNandMaterializers candidate count).toImplementation =
      residualSlack candidate.toImplementation := by
  unfold residualSlack
  rw [appendIndependentNandMaterializers_referenceMinimum]
  change gates + count - (referenceMinimum candidate.toImplementation + count) =
    gates - referenceMinimum candidate.toImplementation
  omega

end DirectWire
end PNP
