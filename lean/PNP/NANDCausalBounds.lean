/-
Copyright (c) 2026 PNP Labs.

Syntactic input-dependency bounds for arbitrary finite direct-wire NAND programs.
Constants have level zero; a gate takes the maximum of its two physical sources.
These bounds are not inferred from Boolean equivalence or semantic minimization.
Structural caps will be derived from actual programs and used to audit extraction,
normalization and literal splicing. This module alone proves none of those passes,
the full manuscript package, a global gate or polynomial PCCMin.
-/

import PNP.NANDComposition

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

theorem index_cases {width : Nat} (index : Fin (width + 1)) :
    (∃ earlier : Fin width, index = earlier.castSucc) ∨ index = Fin.last width := by
  if within : index.val < width then
    exact Or.inl ⟨⟨index.val, within⟩, Fin.ext rfl⟩
  else
    apply Or.inr
    apply Fin.ext
    have upper := index.isLt
    change index.val = width
    omega

def source {inputs gates : Nat} (wire : Source inputs gates)
    (labels : Fin inputs → Nat) (earlier : Fin gates → Nat) : Nat :=
  match wire with
  | .input index => labels index
  | .constant _ => 0
  | .gate index => earlier index

def levels {inputs gates : Nat} (program : Program inputs gates)
    (labels : Fin inputs → Nat) : Fin gates → Nat :=
  match program with
  | .empty => Fin.elim0
  | .snoc initial gate =>
      let earlier := levels initial labels
      append earlier (max (source gate.left labels earlier)
        (source gate.right labels earlier))

theorem levels_snoc_castSucc {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (labels : Fin inputs → Nat) (index : Fin gates) :
    levels (initial.snoc gate) labels index.castSucc = levels initial labels index :=
  append_castSucc _ _ _

theorem levels_snoc_last {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (labels : Fin inputs → Nat) :
    levels (initial.snoc gate) labels (Fin.last gates) =
      max (source gate.left labels (levels initial labels))
        (source gate.right labels (levels initial labels)) :=
  append_last _ _

theorem source_mono {inputs gates : Nat} (wire : Source inputs gates)
    (leftLabels rightLabels : Fin inputs → Nat)
    (leftGates rightGates : Fin gates → Nat)
    (inputLe : ∀ index, leftLabels index ≤ rightLabels index)
    (gateLe : ∀ index, leftGates index ≤ rightGates index) :
    source wire leftLabels leftGates ≤ source wire rightLabels rightGates := by
  cases wire with
  | input index => exact inputLe index
  | constant _ => exact Nat.le_refl 0
  | gate index => exact gateLe index

theorem levels_mono {inputs gates : Nat} (program : Program inputs gates)
    (leftLabels rightLabels : Fin inputs → Nat)
    (inputLe : ∀ index, leftLabels index ≤ rightLabels index) :
    ∀ index, levels program leftLabels index ≤ levels program rightLabels index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      intro index
      rcases index_cases index with ⟨earlier, rfl⟩ | rfl
      · simpa only [levels_snoc_castSucc] using ih earlier
      · simp only [levels_snoc_last]
        have leftBound := source_mono gate.left _ _ _ _ inputLe ih
        have rightBound := source_mono gate.right _ _ _ _ inputLe ih
        omega

theorem source_noninterference {inputs gates : Nat} (wire : Source inputs gates)
    (labels : Fin inputs → Nat) (gateLevels : Fin gates → Nat) (cutoff : Nat)
    (leftInput rightInput : Valuation inputs)
    (leftGates rightGates : Valuation gates)
    (inputSame : ∀ index, labels index ≤ cutoff → leftInput index = rightInput index)
    (gateSame : ∀ index, gateLevels index ≤ cutoff → leftGates index = rightGates index)
    (bounded : source wire labels gateLevels ≤ cutoff) :
    wire.eval leftInput leftGates = wire.eval rightInput rightGates := by
  cases wire with
  | input index => exact inputSame index bounded
  | constant _ => rfl
  | gate index => exact gateSame index bounded

theorem program_noninterference {inputs gates : Nat} (program : Program inputs gates)
    (labels : Fin inputs → Nat) (cutoff : Nat)
    (leftInput rightInput : Valuation inputs)
    (inputSame : ∀ index, labels index ≤ cutoff → leftInput index = rightInput index) :
    ∀ index, levels program labels index ≤ cutoff →
      program.eval leftInput index = program.eval rightInput index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      intro index bounded
      rcases index_cases index with ⟨earlier, rfl⟩ | rfl
      · have earlierBound : levels initial labels earlier ≤ cutoff := by
          simpa only [levels_snoc_castSucc] using bounded
        simpa only [Program.eval_snoc_castSucc] using ih earlier earlierBound
      · have bounds :
            max (source gate.left labels (levels initial labels))
              (source gate.right labels (levels initial labels)) ≤ cutoff := by
          simpa only [levels_snoc_last] using bounded
        have leftBound := Nat.le_trans (Nat.le_max_left _ _) bounds
        have rightBound := Nat.le_trans (Nat.le_max_right _ _) bounds
        have leftValue := source_noninterference gate.left labels (levels initial labels)
          cutoff leftInput rightInput (initial.eval leftInput) (initial.eval rightInput)
          inputSame ih leftBound
        have rightValue := source_noninterference gate.right labels (levels initial labels)
          cutoff leftInput rightInput (initial.eval leftInput) (initial.eval rightInput)
          inputSame ih rightBound
        simp only [Program.eval_snoc_last, Gate.eval, leftValue, rightValue]

theorem source_sound {inputs gates : Nat} (program : Program inputs gates)
    (wire : Source inputs gates) (labels : Fin inputs → Nat) (cutoff : Nat)
    (leftInput rightInput : Valuation inputs)
    (inputSame : ∀ index, labels index ≤ cutoff → leftInput index = rightInput index)
    (bounded : source wire labels (levels program labels) ≤ cutoff) :
    wire.eval leftInput (program.eval leftInput) =
      wire.eval rightInput (program.eval rightInput) :=
  source_noninterference wire labels (levels program labels) cutoff
    leftInput rightInput _ _ inputSame
    (program_noninterference program labels cutoff leftInput rightInput inputSame) bounded

theorem source_congr {inputs gates : Nat} (wire : Source inputs gates)
    {leftLabels rightLabels : Fin inputs → Nat} {leftGates rightGates : Fin gates → Nat}
    (inputEq : ∀ index, leftLabels index = rightLabels index)
    (gateEq : ∀ index, leftGates index = rightGates index) :
    source wire leftLabels leftGates = source wire rightLabels rightGates := by
  cases wire with
  | input index => exact inputEq index
  | constant value => rfl
  | gate index => exact gateEq index

theorem source_rename_inputs {fromInputs toInputs gates : Nat}
    (wire : Source fromInputs gates) (rename : Fin fromInputs → Fin toInputs)
    (labels : Fin toInputs → Nat) (gateLevels : Fin gates → Nat) :
    source (wire.renameInputs rename) labels gateLevels =
      source wire (fun index => labels (rename index)) gateLevels := by
  cases wire <;> rfl

theorem levels_rename_inputs {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates) (rename : Fin fromInputs → Fin toInputs)
    (labels : Fin toInputs → Nat) (index : Fin gates) :
    levels (program.renameInputs rename) labels index =
      levels program (fun input => labels (rename input)) index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      rcases index_cases index with ⟨earlier, rfl⟩ | rfl
      · simpa only [Program.renameInputs, levels_snoc_castSucc] using ih earlier
      · simp only [Program.renameInputs, levels_snoc_last, Gate.renameInputs,
          source_rename_inputs]
        rw [funext ih]

theorem source_weaken {inputs gates : Nat}
    (wire : Source inputs gates) (extra : Nat)
    (labels : Fin inputs → Nat) (gateLevels : Fin (gates + extra) → Nat) :
    source (wire.weakenGates extra) labels gateLevels =
      source wire labels (fun index => gateLevels (Fin.castAdd extra index)) := by
  cases wire <;> rfl

theorem source_shift {inputs gates : Nat}
    (wire : Source inputs gates) (offset : Nat)
    (labels : Fin inputs → Nat) (gateLevels : Fin (offset + gates) → Nat) :
    source (wire.shiftGates offset) labels gateLevels =
      source wire labels (fun index => gateLevels (Fin.natAdd offset index)) := by
  cases wire <;> rfl

theorem source_substitute {innerInputs outerInputs prefixGates suffixGates : Nat}
    (wire : Source innerInputs suffixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (labels : Fin outerInputs → Nat) (gateLevels : Fin (prefixGates + suffixGates) → Nat) :
    source (wire.substituteInputs binding) labels gateLevels =
      source wire
        (fun input => source (binding input) labels
          (fun gate => gateLevels (Fin.castAdd suffixGates gate)))
        (fun gate => gateLevels (Fin.natAdd prefixGates gate)) := by
  cases wire with
  | input index => exact source_weaken (binding index) suffixGates labels gateLevels
  | constant value => rfl
  | gate index => rfl

theorem levels_append_prefix {outerInputs innerInputs prefixGates suffixGates : Nat}
    (prefixProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates)
    (labels : Fin outerInputs → Nat) (index : Fin prefixGates) :
    levels (prefixProgram.appendSubstituted binding suffix) labels
        (Fin.castAdd suffixGates index) = levels prefixProgram labels index := by
  induction suffix with
  | empty => rfl
  | @snoc gates initial gate ih =>
      change levels ((prefixProgram.appendSubstituted binding initial).snoc
        (gate.substituteInputs binding)) labels
        (Fin.castSucc (Fin.castAdd gates index)) = levels prefixProgram labels index
      rw [levels_snoc_castSucc]
      exact ih

theorem levels_append_suffix {outerInputs innerInputs prefixGates suffixGates : Nat}
    (prefixProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates)
    (labels : Fin outerInputs → Nat) (index : Fin suffixGates) :
    levels (prefixProgram.appendSubstituted binding suffix) labels
        (Fin.natAdd prefixGates index) =
      levels suffix (fun input => source (binding input) labels (levels prefixProgram labels)) index := by
  induction suffix with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      rcases index_cases index with ⟨earlier, rfl⟩ | rfl
      · change levels ((prefixProgram.appendSubstituted binding initial).snoc
          (gate.substituteInputs binding)) labels
          (Fin.castSucc (Fin.natAdd prefixGates earlier)) =
          levels (initial.snoc gate)
            (fun input => source (binding input) labels (levels prefixProgram labels)) earlier.castSucc
        rw [levels_snoc_castSucc, levels_snoc_castSucc]
        exact ih earlier
      · change levels ((prefixProgram.appendSubstituted binding initial).snoc
          (gate.substituteInputs binding)) labels (Fin.last (prefixGates + gates)) =
          levels (initial.snoc gate)
            (fun input => source (binding input) labels (levels prefixProgram labels)) (Fin.last gates)
        rw [levels_snoc_last, levels_snoc_last]
        simp only [Gate.substituteInputs]
        rw [source_substitute, source_substitute]
        have inputEq : ∀ input,
            source (binding input) labels
              (fun gate => levels (prefixProgram.appendSubstituted binding initial) labels
                (Fin.castAdd gates gate)) =
            source (binding input) labels (levels prefixProgram labels) :=
          fun input => source_congr (binding input) (fun _ => rfl)
            (fun gate => levels_append_prefix prefixProgram binding initial labels gate)
        have gateEq : ∀ gateIndex,
            levels (prefixProgram.appendSubstituted binding initial) labels
              (Fin.natAdd prefixGates gateIndex) =
            levels initial (fun input => source (binding input) labels
              (levels prefixProgram labels)) gateIndex := ih
        rw [source_congr gate.left inputEq gateEq, source_congr gate.right inputEq gateEq]

theorem substituted_source_level {outerInputs innerInputs prefixGates suffixGates : Nat}
    (prefixProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates)
    (wire : Source innerInputs suffixGates) (labels : Fin outerInputs → Nat) :
    source (wire.substituteInputs binding) labels
        (levels (prefixProgram.appendSubstituted binding suffix) labels) =
      source wire (fun input => source (binding input) labels (levels prefixProgram labels))
        (levels suffix (fun input => source (binding input) labels (levels prefixProgram labels))) := by
  rw [source_substitute]
  exact source_congr wire
    (fun input => source_congr (binding input) (fun _ => rfl)
      (fun gate => levels_append_prefix prefixProgram binding suffix labels gate))
    (fun gate => levels_append_suffix prefixProgram binding suffix labels gate)

/-! Structural upper bounds are independent of Boolean equivalence. -/

def Bounds {inputs gates : Nat} (program : Program inputs gates)
    (labels : Fin inputs → Nat) (caps : Fin gates → Nat) : Prop :=
  match program with
  | .empty => True
  | @Program.snoc _ earlierGates initial gate =>
      Bounds initial labels (fun index => caps index.castSucc) ∧
        max (source gate.left labels (fun index => caps index.castSucc))
          (source gate.right labels (fun index => caps index.castSucc)) ≤
            caps (Fin.last earlierGates)

theorem bounds_levels {inputs gates : Nat} (program : Program inputs gates)
    (labels : Fin inputs → Nat) : Bounds program labels (levels program labels) := by
  induction program with
  | empty => trivial
  | @snoc gates initial gate ih =>
      change Bounds initial labels
          (fun index => levels (initial.snoc gate) labels index.castSucc) ∧
        max (source gate.left labels
          (fun index => levels (initial.snoc gate) labels index.castSucc))
          (source gate.right labels
            (fun index => levels (initial.snoc gate) labels index.castSucc)) ≤
              levels (initial.snoc gate) labels (Fin.last gates)
      have earlier : (fun index => levels (initial.snoc gate) labels index.castSucc) =
          levels initial labels := funext (levels_snoc_castSucc initial gate labels)
      rw [earlier, levels_snoc_last]
      exact ⟨ih, Nat.le_refl _⟩

theorem bounds_index {inputs gates : Nat} (program : Program inputs gates) :
    Bounds program (fun _ => 0) (fun index => index.val + 1) := by
  induction program with
  | empty => trivial
  | @snoc gates initial gate ih =>
      change Bounds initial (fun _ => 0) (fun index => index.val + 1) ∧
        max (source gate.left (fun _ => 0) (fun index => index.val + 1))
          (source gate.right (fun _ => 0) (fun index => index.val + 1)) ≤ gates + 1
      refine ⟨ih, ?_⟩
      have wireBound (wire : Source inputs gates) :
          source wire (fun _ => 0) (fun index => index.val + 1) ≤ gates + 1 := by
        cases wire with
        | input index => exact Nat.zero_le _
        | constant value => exact Nat.zero_le _
        | gate index =>
            have prior := index.isLt
            change index.val + 1 ≤ gates + 1
            omega
      have left := wireBound gate.left
      have right := wireBound gate.right
      omega

theorem levels_le_of_bounds {inputs gates : Nat} (program : Program inputs gates)
    (labels : Fin inputs → Nat) (caps : Fin gates → Nat)
    (bounded : Bounds program labels caps) :
    ∀ index, levels program labels index ≤ caps index := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      change Bounds initial labels (fun index => caps index.castSucc) ∧
        max (source gate.left labels (fun index => caps index.castSucc))
          (source gate.right labels (fun index => caps index.castSucc)) ≤
            caps (Fin.last gates) at bounded
      have earlier := ih (fun index => caps index.castSucc) bounded.1
      intro index
      rcases index_cases index with ⟨prior, rfl⟩ | rfl
      · rw [levels_snoc_castSucc]
        exact earlier prior
      · rw [levels_snoc_last]
        have left := source_mono gate.left labels labels _ _
          (fun _ => Nat.le_refl _) earlier
        have right := source_mono gate.right labels labels _ _
          (fun _ => Nat.le_refl _) earlier
        have last := bounded.2
        omega

/-- Syntactic dependency level of one actual candidate output. -/
def outputLevel {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (labels : Fin inputs → Nat)
    (output : Fin outputs) : Nat :=
  source (candidate.directWireWord.source output) labels (levels candidate.program labels)

/-- Input renaming transports the labels of the actual wiring exactly. -/
theorem outputLevel_renameInputs {fromInputs toInputs gates outputs : Nat}
    (rename : Fin fromInputs → Fin toInputs)
    (candidate : Candidate fromInputs gates outputs) (labels : Fin toInputs → Nat)
    (output : Fin outputs) :
    outputLevel (candidate.renameInputs rename) labels output =
      outputLevel candidate (fun index => labels (rename index)) output := by
  unfold outputLevel Candidate.renameInputs
  rw [Candidate.ofDirectWireWord_pointwise]
  change source ((candidate.directWireWord.source output).renameInputs rename) labels
      (levels (candidate.program.renameInputs rename) labels) = _
  rw [source_rename_inputs]
  exact source_congr _ (fun _ => rfl)
    (levels_rename_inputs candidate.program rename labels)

end PNP.DirectWire.CausalBound
