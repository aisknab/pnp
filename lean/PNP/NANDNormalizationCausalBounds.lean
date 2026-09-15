/-
Copyright (c) 2026 PNP Labs.

Syntactic dependency preservation for the actual constant-propagation, structural
sharing and output-cone pruning passes, and their computed physical closure.
Bounds are proved for arbitrary finite programs and all input label assignments.
No Boolean-equivalence premise supplies a syntactic dependence certificate.

This is the existing three-pass physical normalizer, not all manuscript
normalization rules, complete Package E, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDCausalBounds
import PNP.PCCMinPhysicalNormalizationClosure

namespace PNP.DirectWire.CausalBound

private def append {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin (width + 1)) : alpha :=
  if within : index.val < width then earlier ⟨index.val, within⟩ else last

private theorem append_castSucc {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin width) :
    append earlier last index.castSucc = earlier index := by
  unfold append
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

private theorem append_last {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) :
    append earlier last (Fin.last width) = last := by
  unfold append
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl width impossible)
  · rfl

theorem source_weaken_snoc {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (wire : Source inputs gates) (labels : Fin inputs → Nat) :
    source (wire.weakenGates 1) labels (levels (program.snoc gate) labels) =
      source wire labels (levels program labels) := by
  cases wire with
  | input index => rfl
  | constant value => rfl
  | gate index => exact levels_snoc_castSucc program gate labels index

theorem propagationRename_source_bound {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates)
    (wire : Source inputs fromGates) (labels : Fin inputs → Nat)
    (original : Fin fromGates → Nat) (retained : Fin toGates → Nat)
    (bounded : ∀ index, source (alias index) labels retained ≤ original index) :
    source (wire.propagationRename alias) labels retained ≤ source wire labels original := by
  cases wire with
  | input index => exact Nat.le_refl _
  | constant value => exact Nat.le_refl _
  | gate index => exact bounded index

/-- The actual computed pass never introduces an input above an original gate's bound.
This is derived by induction on its constructors, not from its Boolean equivalence. -/
theorem propagation_alias_bound {inputs gates : Nat}
    (program : Program inputs gates) (labels : Fin inputs → Nat) :
    ∀ index,
      source ((compileNANDConstantPropagation program).alias index) labels
          (levels (compileNANDConstantPropagation program).program labels) ≤
        levels program labels index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      simp only [compileNANDConstantPropagation]
      split
      · intro index
        rcases index_cases index with ⟨earlier, rfl⟩ | rfl
        · change source
            (append (fun index =>
              ((compileNANDConstantPropagation initial).alias index).weakenGates 1)
              (.gate (Fin.last (compileNANDConstantPropagation initial).gateCount))
              earlier.castSucc)
            labels
            (levels ((compileNANDConstantPropagation initial).program.snoc
              ⟨gate.left.propagationRename (compileNANDConstantPropagation initial).alias,
                gate.right.propagationRename (compileNANDConstantPropagation initial).alias⟩)
              labels) ≤ levels (initial.snoc gate) labels earlier.castSucc
          rw [append_castSucc, source_weaken_snoc, levels_snoc_castSucc]
          exact ih earlier
        · change source
            (append (fun index =>
              ((compileNANDConstantPropagation initial).alias index).weakenGates 1)
              (.gate (Fin.last (compileNANDConstantPropagation initial).gateCount))
              (Fin.last gates))
            labels
            (levels ((compileNANDConstantPropagation initial).program.snoc
              ⟨gate.left.propagationRename (compileNANDConstantPropagation initial).alias,
                gate.right.propagationRename (compileNANDConstantPropagation initial).alias⟩)
              labels) ≤ levels (initial.snoc gate) labels (Fin.last gates)
          rw [append_last]
          change levels ((compileNANDConstantPropagation initial).program.snoc
              ⟨gate.left.propagationRename (compileNANDConstantPropagation initial).alias,
                gate.right.propagationRename (compileNANDConstantPropagation initial).alias⟩)
              labels (Fin.last (compileNANDConstantPropagation initial).gateCount) ≤
            levels (initial.snoc gate) labels (Fin.last gates)
          rw [levels_snoc_last, levels_snoc_last]
          have leftBound := propagationRename_source_bound
            (compileNANDConstantPropagation initial).alias gate.left labels
            (levels initial labels)
            (levels (compileNANDConstantPropagation initial).program labels) ih
          have rightBound := propagationRename_source_bound
            (compileNANDConstantPropagation initial).alias gate.right labels
            (levels initial labels)
            (levels (compileNANDConstantPropagation initial).program labels) ih
          dsimp only
          omega
      · rename_i value checked
        intro index
        rcases index_cases index with ⟨earlier, rfl⟩ | rfl
        · change source
            (append (compileNANDConstantPropagation initial).alias (.constant value)
              earlier.castSucc)
            labels (levels (compileNANDConstantPropagation initial).program labels) ≤
              levels (initial.snoc gate) labels earlier.castSucc
          rw [append_castSucc, levels_snoc_castSucc]
          exact ih earlier
        · change source
            (append (compileNANDConstantPropagation initial).alias (.constant value)
              (Fin.last gates))
            labels (levels (compileNANDConstantPropagation initial).program labels) ≤
              levels (initial.snoc gate) labels (Fin.last gates)
          rw [append_last]
          exact Nat.zero_le _

theorem constant_propagation_output_bound {inputs outputs : Nat}
    (current : Implementation inputs outputs) (labels : Fin inputs → Nat)
    (output : Fin outputs) :
    source ((constantPropagationImplementation current).candidate.directWireWord.source output)
        labels (levels (constantPropagationImplementation current).candidate.program labels) ≤
      source (current.candidate.directWireWord.source output) labels
        (levels current.candidate.program labels) := by
  simp only [constantPropagationImplementation, Candidate.ofDirectWireWord_program,
    Candidate.ofDirectWireWord_pointwise]
  exact propagationRename_source_bound
    (compileNANDConstantPropagation current.candidate.program).alias
    (current.candidate.directWireWord.source output) labels
    (levels current.candidate.program labels)
    (levels (compileNANDConstantPropagation current.candidate.program).program labels)
    (propagation_alias_bound current.candidate.program labels)


theorem terminal_sources_level {inputs gates : Nat}
    (program : Program inputs gates) (labels : Fin inputs → Nat) (index : Fin gates) :
    max (source (program.terminalGateSources index).1 labels (levels program labels))
        (source (program.terminalGateSources index).2 labels (levels program labels)) =
      levels program labels index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      rcases index_cases index with ⟨earlier, rfl⟩ | rfl
      · have sources :
            (initial.snoc gate).terminalGateSources earlier.castSucc =
              ((initial.terminalGateSources earlier).1.weakenGates 1,
                (initial.terminalGateSources earlier).2.weakenGates 1) := by
          change (if within : earlier.castSucc.val < gates then
            let pair := initial.terminalGateSources ⟨earlier.castSucc.val, within⟩
            (pair.1.weakenGates 1, pair.2.weakenGates 1)
            else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
          split
          · rfl
          · rename_i outside
            exact False.elim (outside earlier.isLt)
        rw [sources, source_weaken_snoc, source_weaken_snoc, ih,
          levels_snoc_castSucc]
      · have sources :
            (initial.snoc gate).terminalGateSources (Fin.last gates) =
              (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
          change (if within : (Fin.last gates).val < gates then
            let pair := initial.terminalGateSources ⟨(Fin.last gates).val, within⟩
            (pair.1.weakenGates 1, pair.2.weakenGates 1)
            else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
          split
          · rename_i impossible
            exact False.elim (Nat.lt_irrefl gates impossible)
          · rfl
        rw [sources, source_weaken_snoc, source_weaken_snoc, levels_snoc_last]

/-- Recover the actual source-pair match from the implementation's finite search.
No semantic equivalence premise is substituted for this wiring property. -/
theorem sharing_find_sources {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (found : Fin gates) (checked : sharingFindGate program gate = some found) :
    let pair := program.terminalGateSources found
    (pair.1 = gate.left ∧ pair.2 = gate.right) ∨
      (pair.1 = gate.right ∧ pair.2 = gate.left) := by
  unfold sharingFindGate at checked
  generalize indicesEq : allFin gates = indices at checked
  clear indicesEq
  induction indices with
  | nil => cases checked
  | cons index remaining ih =>
      change (if decide
        (((program.terminalGateSources index).1 = gate.left ∧
            (program.terminalGateSources index).2 = gate.right) ∨
          ((program.terminalGateSources index).1 = gate.right ∧
            (program.terminalGateSources index).2 = gate.left))
        then some index else _) = some found at checked
      split at checked
      · rename_i matched
        cases checked
        exact of_decide_eq_true matched
      · exact ih checked

theorem sharing_find_level {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (found : Fin gates) (checked : sharingFindGate program gate = some found)
    (labels : Fin inputs → Nat) :
    levels program labels found =
      max (source gate.left labels (levels program labels))
        (source gate.right labels (levels program labels)) := by
  rw [← terminal_sources_level program labels found]
  rcases sharing_find_sources program gate found checked with
    ⟨left, right⟩ | ⟨left, right⟩
  · rw [left, right]
  · rw [left, right]
    omega

theorem sharingRename_source_bound {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Fin toGates)
    (wire : Source inputs fromGates) (labels : Fin inputs → Nat)
    (original : Fin fromGates → Nat) (retained : Fin toGates → Nat)
    (bounded : ∀ index, retained (alias index) ≤ original index) :
    source (wire.sharingRename alias) labels retained ≤ source wire labels original := by
  cases wire with
  | input index => exact Nat.le_refl _
  | constant value => exact Nat.le_refl _
  | gate index => exact bounded index

theorem sharing_alias_bound {inputs gates : Nat}
    (program : Program inputs gates) (labels : Fin inputs → Nat) :
    ∀ index,
      levels (compileNANDSharing program).program labels
          ((compileNANDSharing program).alias index) ≤
        levels program labels index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      simp only [compileNANDSharing]
      split
      · intro index
        rcases index_cases index with ⟨earlier, rfl⟩ | rfl
        · change levels ((compileNANDSharing initial).program.snoc
              ⟨gate.left.sharingRename (compileNANDSharing initial).alias,
                gate.right.sharingRename (compileNANDSharing initial).alias⟩)
            labels
            (append (fun index => ((compileNANDSharing initial).alias index).castSucc)
              (Fin.last (compileNANDSharing initial).gateCount) earlier.castSucc) ≤
            levels (initial.snoc gate) labels earlier.castSucc
          rw [append_castSucc, levels_snoc_castSucc, levels_snoc_castSucc]
          exact ih earlier
        · change levels ((compileNANDSharing initial).program.snoc
              ⟨gate.left.sharingRename (compileNANDSharing initial).alias,
                gate.right.sharingRename (compileNANDSharing initial).alias⟩)
            labels
            (append (fun index => ((compileNANDSharing initial).alias index).castSucc)
              (Fin.last (compileNANDSharing initial).gateCount) (Fin.last gates)) ≤
            levels (initial.snoc gate) labels (Fin.last gates)
          rw [append_last, levels_snoc_last, levels_snoc_last]
          have leftBound := sharingRename_source_bound (compileNANDSharing initial).alias
            gate.left labels (levels initial labels)
            (levels (compileNANDSharing initial).program labels) ih
          have rightBound := sharingRename_source_bound (compileNANDSharing initial).alias
            gate.right labels (levels initial labels)
            (levels (compileNANDSharing initial).program labels) ih
          dsimp only
          omega
      · rename_i found checked
        intro index
        rcases index_cases index with ⟨earlier, rfl⟩ | rfl
        · change levels (compileNANDSharing initial).program labels
            (append (compileNANDSharing initial).alias found earlier.castSucc) ≤
            levels (initial.snoc gate) labels earlier.castSucc
          rw [append_castSucc, levels_snoc_castSucc]
          exact ih earlier
        · change levels (compileNANDSharing initial).program labels
            (append (compileNANDSharing initial).alias found (Fin.last gates)) ≤
            levels (initial.snoc gate) labels (Fin.last gates)
          rw [append_last, levels_snoc_last]
          rw [sharing_find_level (compileNANDSharing initial).program
            ⟨gate.left.sharingRename (compileNANDSharing initial).alias,
              gate.right.sharingRename (compileNANDSharing initial).alias⟩ found checked labels]
          have leftBound := sharingRename_source_bound (compileNANDSharing initial).alias
            gate.left labels (levels initial labels)
            (levels (compileNANDSharing initial).program labels) ih
          have rightBound := sharingRename_source_bound (compileNANDSharing initial).alias
            gate.right labels (levels initial labels)
            (levels (compileNANDSharing initial).program labels) ih
          dsimp only
          omega

theorem sharing_output_bound {inputs outputs : Nat}
    (current : Implementation inputs outputs) (labels : Fin inputs → Nat)
    (output : Fin outputs) :
    source ((sharingImplementation current).candidate.directWireWord.source output)
        labels (levels (sharingImplementation current).candidate.program labels) ≤
      source (current.candidate.directWireWord.source output) labels
        (levels current.candidate.program labels) := by
  simp only [sharingImplementation, Candidate.ofDirectWireWord_program,
    Candidate.ofDirectWireWord_pointwise]
  exact sharingRename_source_bound (compileNANDSharing current.candidate.program).alias
    (current.candidate.directWireWord.source output) labels
    (levels current.candidate.program labels)
    (levels (compileNANDSharing current.candidate.program).program labels)
    (sharing_alias_bound current.candidate.program labels)


/-- Every pass in the actual physical normalizer preserves the dependency bound. -/
theorem physical_pass_output_bound {inputs outputs : Nat}
    (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    outputLevel (physicalNormalizationPassResult pass current).candidate labels output ≤
      outputLevel current.candidate labels output := by
  cases pass with
  | constants => exact constant_propagation_output_bound current labels output
  | sharing => exact sharing_output_bound current labels output
  | pruning => exact outputConeImplementation_causal_bound current labels output

/-- Compose bounds along the complete trace of actual physical passes. -/
theorem physical_trace_output_bound {inputs outputs : Nat}
    {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    outputLevel final.candidate labels output ≤
      outputLevel current.candidate labels output := by
  induction trace with
  | done current quiet => exact Nat.le_refl _
  | step gain tail ih =>
      exact Nat.le_trans ih (physical_pass_output_bound gain.pass _ labels output)

/-- The computed three-pass closure preserves every output dependency bound.
The execution trace is constructed by the normalizer, not supplied by a caller. -/
theorem physical_normalization_output_bound {inputs outputs : Nat}
    (current : Implementation inputs outputs) (labels : Fin inputs → Nat)
    (output : Fin outputs) :
    outputLevel (runPhysicalNormalization current).result.candidate labels output ≤
      outputLevel current.candidate labels output :=
  physical_trace_output_bound (runPhysicalNormalization current).trace labels output

end PNP.DirectWire.CausalBound
