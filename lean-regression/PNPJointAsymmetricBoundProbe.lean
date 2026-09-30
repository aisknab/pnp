import PNP

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.JointAsymmetricBoundProbe
open JointAsymmetricBound
open ReadOnceTerm (variables)
open DemandForest (constants expression)
open EssentialInputBound (Essential)
open DemandDeficit (JointEssential)
open TightDemandSymmetry (inputSwap)

variable {inputs gates outputs : Nat}

theorem general_zero_budget_read_once (program : Program inputs gates)
    (demand : List (Source inputs gates)) (joint : JointEssential program demand)
    (small : demand.length + gates ≤ inputs)
    (source : Source inputs gates) (member : source ∈ demand) :
    constants (expression program source) = 0 ∧
      (variables (expression program source)).Nodup :=
  zero_budget_read_once program demand joint small source member

theorem general_asymmetric_bound (program : Program inputs gates)
    (demand : List (Source inputs gates)) (joint : JointEssential program demand)
    (source : Source inputs gates) (member : source ∈ demand)
    (atFalse : source.eval (fun _ => false) (program.eval (fun _ => false)) = true)
    (asymmetric : ∀ first second : Fin inputs, first ≠ second →
      Essential (fun input => source.eval input (program.eval input)) first →
      Essential (fun input => source.eval input (program.eval input)) second →
      ∃ input, source.eval input (program.eval input) ≠
        source.eval (inputSwap first second input) (program.eval (inputSwap first second input))) :
    inputs + 1 ≤ demand.length + gates :=
  asymmetric_bound program demand joint source member atFalse asymmetric

theorem general_two_positions_permutation {alpha : Type} (items : List alpha)
    (first second : Fin items.length) (different : first ≠ second) :
    ∃ rest : List alpha, items.Perm (items.get first :: items.get second :: rest) :=
  two_positions_permutation items first second different

theorem general_two_output_positions_bound (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs)
    (joint : JointEssential program (List.ofFn word.source))
    (left right : Fin outputs) (different : left ≠ right)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => (word.source left).eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => (word.source right).eval input (program.eval input)) common)
    (onlyCommon : ∀ index,
      Essential (fun input => (word.source left).eval input (program.eval input)) index →
      Essential (fun input => (word.source right).eval input (program.eval input)) index → index = common)
    (atFalse : (word.source left).eval (fun _ => false) (program.eval (fun _ => false)) = true)
    (asymmetric : ∀ first second : Fin inputs, first ≠ second →
      Essential (fun input => (word.source left).eval input (program.eval input)) first →
      Essential (fun input => (word.source left).eval input (program.eval input)) second →
      ∃ input, (word.source left).eval input (program.eval input) ≠
        (word.source left).eval (inputSwap first second input) (program.eval (inputSwap first second input))) :
    inputs + 2 ≤ outputs + gates :=
  two_output_positions_bound program word joint left right different common leftEssential rightEssential onlyCommon atFalse asymmetric

theorem equal_values_keep_two_positions :
    ∃ rest : List Nat, [7,7,9].Perm (7 :: 7 :: rest) := by
  exact two_positions_permutation [7,7,9] 0 1 (by decide)

theorem one_position_is_not_two :
    ¬ ∃ left right : Fin 1, left ≠ right := by
  decide +kernel

theorem direct_input_fails_true_at_false :
    ¬ (Source.input (0 : Fin 1) : Source 1 0).eval
      (fun _ => false) ((Program.empty : Program 1 0).eval (fun _ => false)) = true := by
  decide +kernel

end PNP.DirectWire.JointAsymmetricBoundProbe

#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.general_zero_budget_read_once
#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.general_asymmetric_bound
#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.general_two_positions_permutation
#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.general_two_output_positions_bound
#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.equal_values_keep_two_positions
#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.one_position_is_not_two
#print axioms PNP.DirectWire.JointAsymmetricBoundProbe.direct_input_fails_true_at_false
