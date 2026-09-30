import PNP.NANDNormalizationTerm

set_option autoImplicit false

/-!
The actual physical normalizer preserves exact source-derived NAND expressions
up to recursive operand commutation. The proof uses real compiler source
incidence, not a Boolean equivalence certificate or a supplied ownership map.
-/

namespace PNP.DirectWire.NormalizationTerm

open NormalizationAbstractValue (extend extend_earlier extend_last)

def read {inputs gates : Nat} (source : Source inputs gates)
    (input : Fin inputs → Term) (computed : Fin gates → Term) : Term :=
  match source with
  | .input index => input index
  | .constant value => .constant value
  | .gate index => computed index

def evaluate {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Term) : Fin gates → Term :=
  match program with
  | .empty => Fin.elim0
  | .snoc initial gate =>
      extend (evaluate initial input)
        (nand (read gate.left input (evaluate initial input))
          (read gate.right input (evaluate initial input)))

def output {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (input : Fin inputs → Term) (index : Fin outputs) : Term :=
  read (candidate.directWireWord.source index) input (evaluate candidate.program input)

theorem evaluate_earlier {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (input : Fin inputs → Term) (index : Fin gates) :
    evaluate (program.snoc gate) input index.castSucc = evaluate program input index :=
  extend_earlier _ _ _

theorem evaluate_last {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (input : Fin inputs → Term) :
    evaluate (program.snoc gate) input (Fin.last gates) =
      nand (read gate.left input (evaluate program input))
        (read gate.right input (evaluate program input)) :=
  extend_last _ _

theorem read_weaken {inputs gates : Nat} (source : Source inputs gates)
    (input : Fin inputs → Term) (computed : Fin (gates + 1) → Term) :
    read (source.weakenGates 1) input computed =
      read source input (fun index => computed index.castSucc) := by
  cases source <;> rfl

private theorem sources_earlier {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (index : Fin gates) :
    (program.snoc gate).terminalGateSources index.castSucc =
      ((program.terminalGateSources index).1.weakenGates 1,
        (program.terminalGateSources index).2.weakenGates 1) := by
  change (if within : index.val < gates then
    let pair := program.terminalGateSources ⟨index.val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  rw [dif_pos index.isLt]

private theorem sources_last {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) :
    (program.snoc gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
  change (if within : gates < gates then
    let pair := program.terminalGateSources ⟨gates, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  rw [dif_neg (Nat.lt_irrefl gates)]

theorem evaluate_equation {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Term) (index : Fin gates) :
    nand (read (program.terminalGateSources index).1 input (evaluate program input))
      (read (program.terminalGateSources index).2 input (evaluate program input)) =
        evaluate program input index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc width initial gate ih =>
      have initialTerms : (fun index => evaluate (initial.snoc gate) input index.castSucc) =
          evaluate initial input := funext (evaluate_earlier initial gate input)
      rcases CausalBound.index_cases index with ⟨earlier, rfl⟩ | rfl
      · rw [sources_earlier, read_weaken, read_weaken, initialTerms, evaluate_earlier]
        exact ih earlier
      · rw [sources_last, read_weaken, read_weaken, initialTerms, evaluate_last]


theorem Related.of_eq {left right : Term} (same : left = right) : Related left right := by
  cases same
  exact Related.refl _

theorem read_related {inputs gates : Nat} (wire : Source inputs gates)
    (leftInput rightInput : Fin inputs → Term) (leftGates rightGates : Fin gates → Term)
    (inputsRelated : ∀ index, Related (leftInput index) (rightInput index))
    (gatesRelated : ∀ index, Related (leftGates index) (rightGates index)) :
    Related (read wire leftInput leftGates) (read wire rightInput rightGates) := by
  cases wire with
  | input index => exact inputsRelated index
  | constant bit => exact Related.refl _
  | gate index => exact gatesRelated index

/-- Uniqueness modulo structural commutation for an arbitrary topological program. -/
theorem evaluate_related_assignment {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Term) (assigned : Fin gates → Term)
    (equations : ∀ index,
      Related
        (nand (read (program.terminalGateSources index).1 input assigned)
          (read (program.terminalGateSources index).2 input assigned))
        (assigned index)) :
    ∀ index, Related (evaluate program input index) (assigned index) := by
  induction program with
  | empty => intro index; exact Fin.elim0 index
  | @snoc width initial gate ih =>
      have earlier := ih (fun index => assigned index.castSucc) (fun index => by
        have equation := equations index.castSucc
        rw [sources_earlier, read_weaken, read_weaken] at equation
        exact equation)
      intro index
      rcases CausalBound.index_cases index with ⟨previous, rfl⟩ | rfl
      · rw [evaluate_earlier]
        exact earlier previous
      · rw [evaluate_last]
        have equation := equations (Fin.last width)
        rw [sources_last, read_weaken, read_weaken] at equation
        exact (nand_congr
          (read_related gate.left _ _ _ _ (fun index => Related.refl _) earlier)
          (read_related gate.right _ _ _ _ (fun index => Related.refl _) earlier)).trans equation

theorem read_propagation {inputs oldGates newGates : Nat}
    (alias : Fin oldGates → Source inputs newGates) (wire : Source inputs oldGates)
    (input : Fin inputs → Term) (computed : Fin newGates → Term) :
    read (wire.propagationRename alias) input computed =
      read wire input (fun index => read (alias index) input computed) := by
  cases wire <;> rfl

theorem read_sharing {inputs oldGates newGates : Nat}
    (alias : Fin oldGates → Fin newGates) (wire : Source inputs oldGates)
    (input : Fin inputs → Term) (computed : Fin newGates → Term) :
    read (wire.sharingRename alias) input computed =
      read wire input (fun index => computed (alias index)) := by
  cases wire <;> rfl

private theorem constant_rule {inputs gates : Nat}
    (gate : Gate inputs gates) (bit : Bool)
    (checked : constantGateValue gate = some bit)
    (input : Fin inputs → Term) (computed : Fin gates → Term) :
    nand (read gate.left input computed) (read gate.right input computed) = .constant bit := by
  unfold constantGateValue at checked
  split at checked
  next oneFalse =>
    cases checked
    rcases oneFalse with left | right
    · rw [left]
      exact nand_false_left _
    · rw [right]
      exact nand_false_right _
  next neitherFalse =>
    split at checked
    next bothTrue =>
      cases checked
      rw [bothTrue.1, bothTrue.2]
      exact nand_true_true
    next neither => cases checked

theorem constants_alias {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Term) (index : Fin gates) :
    Related
      (read ((compileNANDConstantPropagation program).alias index) input
        (evaluate (compileNANDConstantPropagation program).program input))
      (evaluate program input index) := by
  let compiled := compileNANDConstantPropagation program
  have unique := evaluate_related_assignment program input
    (fun index => read (compiled.alias index) input (evaluate compiled.program input))
    (fun index => by
      rw [← read_propagation compiled.alias (program.terminalGateSources index).1 input
        (evaluate compiled.program input),
        ← read_propagation compiled.alias (program.terminalGateSources index).2 input
          (evaluate compiled.program input)]
      cases found : compiled.alias index with
      | input inputIndex =>
          exact False.elim (ConstantSourceIncidence.alias_not_input program index inputIndex found)
      | constant bit =>
          exact Related.of_eq (constant_rule _ bit
            (ConstantSourceIncidence.folded_sources program index bit found) input _)
      | gate position =>
          have pair := ConstantSourceIncidence.retained_sources program index position found
          have equation := evaluate_equation compiled.program input position
          rw [← pair] at equation
          exact Related.of_eq equation)
  exact (unique index).symm

theorem constants_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Term) (index : Fin outputs) :
    Related (output (constantPropagationImplementation current).candidate input index)
      (output current.candidate input index) := by
  simp only [output, constantPropagationImplementation, Candidate.ofDirectWireWord_program,
    Candidate.ofDirectWireWord_pointwise, read_propagation]
  exact read_related _ _ _ _ _ (fun index => Related.refl _)
    (constants_alias current.candidate.program input)

theorem sharing_alias {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Term) (index : Fin gates) :
    Related
      (evaluate (compileNANDSharing program).program input
        ((compileNANDSharing program).alias index))
      (evaluate program input index) := by
  let compiled := compileNANDSharing program
  have unique := evaluate_related_assignment program input
    (fun index => evaluate compiled.program input (compiled.alias index))
    (fun index => by
      rw [← read_sharing compiled.alias (program.terminalGateSources index).1 input
        (evaluate compiled.program input),
        ← read_sharing compiled.alias (program.terminalGateSources index).2 input
          (evaluate compiled.program input)]
      have pair := SharingSourceIncidence.actual_sources program index
      have equation := evaluate_equation compiled.program input (compiled.alias index)
      rcases pair with same | swapped
      · rw [← same] at equation
        exact Related.of_eq equation
      · have left := congrArg Prod.fst swapped
        have right := congrArg Prod.snd swapped
        dsimp only [SharingSourceIncidence.pairMap] at left right
        rw [left, right]
        exact (nand_comm _ _).trans (Related.of_eq equation))
  exact (unique index).symm

theorem sharing_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Term) (index : Fin outputs) :
    Related (output (sharingImplementation current).candidate input index)
      (output current.candidate input index) := by
  simp only [output, sharingImplementation, Candidate.ofDirectWireWord_program,
    Candidate.ofDirectWireWord_pointwise, read_sharing]
  exact read_related _ _ _ _ _ (fun index => Related.refl _)
    (sharing_alias current.candidate.program input)

theorem pruning_source {inputs outputs : Nat} (current : Implementation inputs outputs)
    (wire : Source inputs (outputConeImplementation current).gateCount)
    (input : Fin inputs → Term) :
    read (outputConeOriginalSource current.candidate wire) input
        (evaluate current.candidate.program input) =
      read wire input (fun index => evaluate current.candidate.program input
        (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) index)) := by
  cases wire <;> rfl

theorem pruning_gates {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Term) (index : Fin (outputConeImplementation current).gateCount) :
    Related (evaluate (outputConeImplementation current).candidate.program input index)
      (evaluate current.candidate.program input
        (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) index)) := by
  apply evaluate_related_assignment (outputConeImplementation current).candidate.program input
    (fun index => evaluate current.candidate.program input
      (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) index)) ?_ index
  intro position
  rw [← pruning_source, ← pruning_source]
  have pair := outputConeImplementation_original_sources current position
  have equation := evaluate_equation current.candidate.program input
    (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) position)
  rw [← pair] at equation
  exact Related.of_eq equation

theorem pruning_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Term) (index : Fin outputs) :
    Related (output (outputConeImplementation current).candidate input index)
      (output current.candidate input index) := by
  have first := read_related
    ((outputConeImplementation current).candidate.directWireWord.source index) input input
    (evaluate (outputConeImplementation current).candidate.program input)
    (fun position => evaluate current.candidate.program input
      (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) position))
    (fun coordinate => Related.refl _) (pruning_gates current input)
  rw [← pruning_source current _ input, outputConeImplementation_original_output_source] at first
  exact first

theorem pass_output {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) (input : Fin inputs → Term) (index : Fin outputs) :
    Related (output (physicalNormalizationPassResult pass current).candidate input index)
      (output current.candidate input index) := by
  cases pass with
  | constants => exact constants_output current input index
  | sharing => exact sharing_output current input index
  | pruning => exact pruning_output current input index

theorem trace_output {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) (input : Fin inputs → Term)
    (index : Fin outputs) :
    Related (output final.candidate input index) (output current.candidate input index) := by
  induction trace with
  | done current quiet => exact Related.refl _
  | step gain tail ih => exact ih.trans (pass_output gain.pass _ input index)

theorem normalized_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Term) (index : Fin outputs) :
    Related (output (runPhysicalNormalization current).result.candidate input index)
      (output current.candidate input index) :=
  trace_output (runPhysicalNormalization current).trace input index

theorem read_value {inputs gates : Nat} (wire : Source inputs gates)
    (input : Fin inputs → Term) (computed : Fin gates → Term) (valuation : Nat → Bool) :
    value valuation (read wire input computed) =
      wire.eval (fun index => value valuation (input index))
        (fun index => value valuation (computed index)) := by
  cases wire <;> rfl

theorem evaluate_value {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Term) (valuation : Nat → Bool) (index : Fin gates) :
    value valuation (evaluate program input index) =
      program.eval (fun coordinate => value valuation (input coordinate)) index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc width initial gate ih =>
      rcases CausalBound.index_cases index with ⟨earlier, rfl⟩ | rfl
      · rw [evaluate_earlier, Program.eval_snoc_castSucc]
        exact ih earlier
      · rw [evaluate_last, Program.eval_snoc_last, nand_value, read_value, read_value]
        rw [funext ih]
        rfl

theorem output_value {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (input : Fin inputs → Term) (valuation : Nat → Bool) (index : Fin outputs) :
    value valuation (output candidate input index) =
      candidate.semantics (fun coordinate => value valuation (input coordinate)) index := by
  change value valuation (read (candidate.directWireWord.source index) input
    (evaluate candidate.program input)) =
    (candidate.directWireWord.source index).eval
      (fun coordinate => value valuation (input coordinate))
      (candidate.program.eval (fun coordinate => value valuation (input coordinate)))
  rw [read_value, funext (evaluate_value candidate.program input valuation)]

end PNP.DirectWire.NormalizationTerm
