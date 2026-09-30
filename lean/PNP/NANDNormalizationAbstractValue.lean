import PNP.NANDConstantSourceIncidence
import PNP.NANDSharingSourceIncidence
import PNP.NANDNormalizationCausalBounds

set_option autoImplicit false

/-!
Exact structural values for the real physical normalizer. Unknown wires retain
a dependency label; only the literal constant-propagation NAND rules collapse
them. This is not Boolean semantic minimization or a full manuscript profile.
-/

namespace PNP.DirectWire.NormalizationAbstractValue

inductive Value where
  | constant (bit : Bool)
  | wire (level : Nat)
  deriving DecidableEq, Repr

def Value.level : Value → Nat
  | .constant _ => 0
  | .wire level => level

def nand : Value → Value → Value
  | .constant false, _ => .constant true
  | _, .constant false => .constant true
  | .constant true, .constant true => .constant false
  | left, right => .wire (max left.level right.level)

theorem nand_comm (left right : Value) : nand left right = nand right left := by
  cases left with
  | constant left =>
      cases left <;> cases right with
      | constant right => cases right <;> rfl
      | wire level => simp only [nand, Value.level, Nat.zero_max, Nat.max_zero]
  | wire left =>
      cases right with
      | constant right =>
          cases right <;> simp only [nand, Value.level, Nat.zero_max, Nat.max_zero]
      | wire right =>
          change Value.wire (max left right) = Value.wire (max right left)
          rw [Nat.max_comm]

def extend {width : Nat} {alpha : Type} (earlier : Fin width → alpha)
    (last : alpha) (index : Fin (width + 1)) : alpha :=
  if within : index.val < width then earlier ⟨index.val, within⟩ else last

theorem extend_earlier {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin width) :
    extend earlier last index.castSucc = earlier index := by
  unfold extend
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

theorem extend_last {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) :
    extend earlier last (Fin.last width) = last := by
  unfold extend
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl width impossible)
  · rfl

def read {inputs gates : Nat} (source : Source inputs gates)
    (input : Fin inputs → Value) (computed : Fin gates → Value) : Value :=
  match source with
  | .input index => input index
  | .constant value => .constant value
  | .gate index => computed index

def evaluate {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Value) : Fin gates → Value :=
  match program with
  | .empty => Fin.elim0
  | .snoc initial gate =>
      extend (evaluate initial input)
        (nand (read gate.left input (evaluate initial input))
          (read gate.right input (evaluate initial input)))

def output {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (input : Fin inputs → Value) (index : Fin outputs) : Value :=
  read (candidate.directWireWord.source index) input (evaluate candidate.program input)

theorem evaluate_earlier {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (input : Fin inputs → Value) (index : Fin gates) :
    evaluate (program.snoc gate) input index.castSucc = evaluate program input index :=
  extend_earlier _ _ _

theorem evaluate_last {inputs gates : Nat} (program : Program inputs gates)
    (gate : Gate inputs gates) (input : Fin inputs → Value) :
    evaluate (program.snoc gate) input (Fin.last gates) =
      nand (read gate.left input (evaluate program input))
        (read gate.right input (evaluate program input)) :=
  extend_last _ _

theorem read_weaken {inputs gates : Nat} (source : Source inputs gates)
    (input : Fin inputs → Value) (computed : Fin (gates + 1) → Value) :
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
    (input : Fin inputs → Value) (index : Fin gates) :
    nand (read (program.terminalGateSources index).1 input (evaluate program input))
      (read (program.terminalGateSources index).2 input (evaluate program input)) =
        evaluate program input index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc width initial gate ih =>
      have initialValues : (fun index => evaluate (initial.snoc gate) input index.castSucc) =
          evaluate initial input := funext (evaluate_earlier initial gate input)
      rcases CausalBound.index_cases index with ⟨earlier, rfl⟩ | rfl
      · rw [sources_earlier, read_weaken, read_weaken, initialValues, evaluate_earlier]
        exact ih earlier
      · rw [sources_last, read_weaken, read_weaken, initialValues, evaluate_last]

/-- A topological program has a unique value assignment for these NAND rules. -/
theorem evaluate_unique {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Value) (assigned : Fin gates → Value)
    (equations : ∀ index,
      nand (read (program.terminalGateSources index).1 input assigned)
        (read (program.terminalGateSources index).2 input assigned) = assigned index) :
    evaluate program input = assigned := by
  induction program with
  | empty => funext index; exact Fin.elim0 index
  | @snoc width initial gate ih =>
      have earlier := ih (fun index => assigned index.castSucc) (fun index => by
        have equation := equations index.castSucc
        rw [sources_earlier, read_weaken, read_weaken] at equation
        exact equation)
      funext index
      rcases CausalBound.index_cases index with ⟨previous, rfl⟩ | rfl
      · rw [evaluate_earlier, earlier]
      · rw [evaluate_last, earlier]
        have equation := equations (Fin.last width)
        rw [sources_last, read_weaken, read_weaken] at equation
        exact equation

theorem read_propagation {inputs oldGates newGates : Nat}
    (alias : Fin oldGates → Source inputs newGates) (wire : Source inputs oldGates)
    (input : Fin inputs → Value) (computed : Fin newGates → Value) :
    read (wire.propagationRename alias) input computed =
      read wire input (fun index => read (alias index) input computed) := by
  cases wire <;> rfl

theorem read_sharing {inputs oldGates newGates : Nat}
    (alias : Fin oldGates → Fin newGates) (wire : Source inputs oldGates)
    (input : Fin inputs → Value) (computed : Fin newGates → Value) :
    read (wire.sharingRename alias) input computed =
      read wire input (fun index => computed (alias index)) := by
  cases wire <;> rfl

private theorem constant_rule {inputs gates : Nat}
    (gate : Gate inputs gates) (bit : Bool)
    (checked : constantGateValue gate = some bit)
    (input : Fin inputs → Value) (computed : Fin gates → Value) :
    nand (read gate.left input computed) (read gate.right input computed) = .constant bit := by
  unfold constantGateValue at checked
  split at checked
  next oneFalse =>
    cases checked
    rcases oneFalse with left | right
    · rw [left]
      rfl
    · rw [right, nand_comm]
      rfl
  next neitherFalse =>
    split at checked
    next bothTrue =>
      cases checked
      rw [bothTrue.1, bothTrue.2]
      rfl
    next neither => cases checked

theorem constants_alias {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Value) (index : Fin gates) :
    read ((compileNANDConstantPropagation program).alias index) input
      (evaluate (compileNANDConstantPropagation program).program input) =
        evaluate program input index := by
  let compiled := compileNANDConstantPropagation program
  have unique := evaluate_unique program input
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
          exact constant_rule _ bit
            (ConstantSourceIncidence.folded_sources program index bit found) input _
      | gate position =>
          have pair := ConstantSourceIncidence.retained_sources program index position found
          have equation := evaluate_equation compiled.program input position
          rw [← pair] at equation
          exact equation)
  exact (congrFun unique index).symm

theorem constants_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Value) (index : Fin outputs) :
    output (constantPropagationImplementation current).candidate input index =
      output current.candidate input index := by
  simp only [output, constantPropagationImplementation, Candidate.ofDirectWireWord_program,
    Candidate.ofDirectWireWord_pointwise, read_propagation]
  have same := funext (constants_alias current.candidate.program input)
  rw [same]

theorem sharing_alias {inputs gates : Nat} (program : Program inputs gates)
    (input : Fin inputs → Value) (index : Fin gates) :
    evaluate (compileNANDSharing program).program input
      ((compileNANDSharing program).alias index) = evaluate program input index := by
  let compiled := compileNANDSharing program
  have unique := evaluate_unique program input
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
        exact equation
      · rw [← nand_comm] at equation
        have left := congrArg Prod.fst swapped
        have right := congrArg Prod.snd swapped
        dsimp only [SharingSourceIncidence.pairMap] at left right
        rw [left, right]
        exact equation)
  exact (congrFun unique index).symm

theorem sharing_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Value) (index : Fin outputs) :
    output (sharingImplementation current).candidate input index =
      output current.candidate input index := by
  simp only [output, sharingImplementation, Candidate.ofDirectWireWord_program,
    Candidate.ofDirectWireWord_pointwise, read_sharing]
  have same := funext (sharing_alias current.candidate.program input)
  rw [same]

theorem pruning_source {inputs outputs : Nat} (current : Implementation inputs outputs)
    (wire : Source inputs (outputConeImplementation current).gateCount)
    (input : Fin inputs → Value) :
    read (outputConeOriginalSource current.candidate wire) input
        (evaluate current.candidate.program input) =
      read wire input (fun index => evaluate current.candidate.program input
        (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) index)) := by
  cases wire <;> rfl

theorem pruning_gates {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Value) (index : Fin (outputConeImplementation current).gateCount) :
    evaluate (outputConeImplementation current).candidate.program input index =
      evaluate current.candidate.program input
        (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) index) := by
  apply congrFun (evaluate_unique (outputConeImplementation current).candidate.program input
    (fun index => evaluate current.candidate.program input
      (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) index)) ?_) index
  intro position
  rw [← pruning_source, ← pruning_source]
  have pair := outputConeImplementation_original_sources current position
  have equation := evaluate_equation current.candidate.program input
    (terminalExtractionOrigin current.candidate (outputConeRecords current.candidate) position)
  rw [← pair] at equation
  exact equation

theorem pruning_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Value) (index : Fin outputs) :
    output (outputConeImplementation current).candidate input index =
      output current.candidate input index := by
  unfold output
  rw [funext (pruning_gates current input), ← pruning_source,
    outputConeImplementation_original_output_source]

theorem pass_output {inputs outputs : Nat} (pass : PhysicalNormalizationPass)
    (current : Implementation inputs outputs) (input : Fin inputs → Value) (index : Fin outputs) :
    output (physicalNormalizationPassResult pass current).candidate input index =
      output current.candidate input index := by
  cases pass with
  | constants => exact constants_output current input index
  | sharing => exact sharing_output current input index
  | pruning => exact pruning_output current input index

theorem trace_output {inputs outputs : Nat} {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) (input : Fin inputs → Value)
    (index : Fin outputs) :
    output final.candidate input index = output current.candidate input index := by
  induction trace with
  | done current quiet => rfl
  | step gain tail ih => exact ih.trans (pass_output gain.pass _ input index)

theorem normalized_output {inputs outputs : Nat} (current : Implementation inputs outputs)
    (input : Fin inputs → Value) (index : Fin outputs) :
    output (runPhysicalNormalization current).result.candidate input index =
      output current.candidate input index :=
  trace_output (runPhysicalNormalization current).trace input index

end PNP.DirectWire.NormalizationAbstractValue
