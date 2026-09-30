import PNP.NANDNoReuseForest
import PNP.NANDGuardedSpineMinimum

set_option autoImplicit false
set_option Elab.async false

/-! A constant-free read-once NAND term is either a direct input or has a
swappable pair of essential inputs. This contradicts signed-prefix semantics
and completes the semantic tight-budget obstruction for the stated interface. -/

namespace PNP.DirectWire.ReadOnceSymmetry
open NormalizationTerm (Term value)
open ReadOnceTerm (variables)
open DemandForest (constants expression extendInput)
open EssentialInputBound (Essential)
open DemandDeficit (JointEssential)
open TightDemandSymmetry (inputSwap)

variable {inputs gates : Nat}

/-- Choose a literal pair at the bottom of the actual raw tree and propagate
its swap through disjoint sibling inputs. No tree-to-circuit compiler is used. -/
theorem leaf_or_swap (term : Term) (noConstant : constants term = 0)
    (distinct : (variables term).Nodup) :
    (∃ index, term = .input index) ∨
      ∃ first second : Nat, first ≠ second ∧ first ∈ variables term ∧ second ∈ variables term ∧
        ∀ original swapped : Nat → Bool,
          swapped first = original second → swapped second = original first →
          (∀ other, other ≠ first → other ≠ second → swapped other = original other) →
          value original term = value swapped term := by
  induction term with
  | constant bit => cases noConstant
  | input index => exact Or.inl ⟨index,rfl⟩
  | node left right ihLeft ihRight =>
      have noLeft : constants left = 0 := by change constants left + constants right = 0 at noConstant; omega
      have noRight : constants right = 0 := by change constants left + constants right = 0 at noConstant; omega
      obtain ⟨leftDistinct,rightDistinct,separate⟩ := List.nodup_append.mp distinct
      rcases ihLeft noLeft leftDistinct with ⟨index,atLeft⟩ | ⟨first,second,different,inFirst,inSecond,preserved⟩
      · subst left
        rcases ihRight noRight rightDistinct with ⟨other,atRight⟩ | ⟨first,second,different,inFirst,inSecond,preserved⟩
        · subst right
          refine Or.inr ⟨index,other,separate index List.mem_cons_self other List.mem_cons_self,
            List.mem_append_left _ List.mem_cons_self,List.mem_append_right _ List.mem_cons_self,?_⟩
          intro original swapped firstEq secondEq _
          change boolNand (original index) (original other) = boolNand (swapped index) (swapped other)
          rw [firstEq,secondEq]
          cases original index <;> cases original other <;> rfl
        · refine Or.inr ⟨first,second,different,List.mem_append_right _ inFirst,
            List.mem_append_right _ inSecond,?_⟩
          intro original swapped firstEq secondEq outside
          have rightSame := preserved original swapped firstEq secondEq outside
          have leftSame := outside index (separate index List.mem_cons_self first inFirst)
            (separate index List.mem_cons_self second inSecond)
          change boolNand (original index) (value original right) =
            boolNand (swapped index) (value swapped right)
          rw [leftSame,rightSame]
      · refine Or.inr ⟨first,second,different,List.mem_append_left _ inFirst,
          List.mem_append_left _ inSecond,?_⟩
        intro original swapped firstEq secondEq outside
        have leftSame := preserved original swapped firstEq secondEq outside
        have rightSame : value original right = value swapped right := by
          apply ReadOnceTerm.value_congr
          intro index member
          exact (outside index (Ne.symm (separate first inFirst index member))
            (Ne.symm (separate second inSecond index member))).symm
        change boolNand (value original left) (value original right) =
          boolNand (value swapped left) (value swapped right)
        rw [leftSame,rightSame]

private theorem extend_swap_other (first second : Fin inputs) (input : Valuation inputs)
    (index : Nat) (notFirst : index ≠ first.val) (notSecond : index ≠ second.val) :
    extendInput (inputSwap first second input) index = extendInput input index := by
  unfold extendInput
  by_cases bound : index < inputs
  · rw [dif_pos bound,dif_pos bound]
    exact TightDemandSymmetry.inputSwap_other first second input ⟨index,bound⟩
      (fun same => notFirst (congrArg Fin.val same)) (fun same => notSecond (congrArg Fin.val same))
  · rw [dif_neg bound,dif_neg bound]

/-- The symmetry concerns actual finite inputs and actual source semantics.
The pair is essential to the output, not an irrelevant unused-input symmetry. -/
theorem expression_leaf_or_swap (program : Program inputs gates) (source : Source inputs gates)
    (noConstant : constants (expression program source) = 0)
    (distinct : (variables (expression program source)).Nodup) :
    (∃ index : Fin inputs, ∀ input, source.eval input (program.eval input) = input index) ∨
      ∃ first second : Fin inputs, first ≠ second ∧
        Essential (fun input => source.eval input (program.eval input)) first ∧
        Essential (fun input => source.eval input (program.eval input)) second ∧
        ∀ input, source.eval input (program.eval input) =
          source.eval (inputSwap first second input) (program.eval (inputSwap first second input)) := by
  rcases leaf_or_swap (expression program source) noConstant distinct with
    ⟨index,atLeaf⟩ | ⟨first,second,different,inFirst,inSecond,preserved⟩
  · have member : index ∈ variables (expression program source) := by
      rw [atLeaf]
      exact List.mem_cons_self
    have bound := ReadOnceTerm.expression_variables_lt program source index member
    refine Or.inl ⟨⟨index,bound⟩,?_⟩
    intro input
    have sound := DemandForest.expression_sound program source input
    rw [atLeaf] at sound
    change extendInput input index = source.eval input (program.eval input) at sound
    exact sound.symm.trans (DemandForest.extendInput_at input ⟨index,bound⟩)
  · let firstInput : Fin inputs :=
      ⟨first,ReadOnceTerm.expression_variables_lt program source first inFirst⟩
    let secondInput : Fin inputs :=
      ⟨second,ReadOnceTerm.expression_variables_lt program source second inSecond⟩
    have distinctInputs : firstInput ≠ secondInput := fun same => different (congrArg Fin.val same)
    refine Or.inr ⟨firstInput,secondInput,distinctInputs,
      ReadOnceTerm.expression_essential program source noConstant distinct firstInput inFirst,
      ReadOnceTerm.expression_essential program source noConstant distinct secondInput inSecond,?_⟩
    intro input
    have firstEq : extendInput (inputSwap firstInput secondInput input) first = extendInput input second := by
      rw [DemandForest.extendInput_at _ firstInput,DemandForest.extendInput_at _ secondInput]
      exact TightDemandSymmetry.inputSwap_left firstInput secondInput input
    have secondEq : extendInput (inputSwap firstInput secondInput input) second = extendInput input first := by
      rw [DemandForest.extendInput_at _ secondInput,DemandForest.extendInput_at _ firstInput]
      exact TightDemandSymmetry.inputSwap_right firstInput secondInput input distinctInputs
    have same := preserved (extendInput input) (extendInput (inputSwap firstInput secondInput input))
      firstEq secondEq (extend_swap_other firstInput secondInput input)
    rw [DemandForest.expression_sound,DemandForest.expression_sound] at same
    exact same

/-- A true all-false value rules out a direct input. Pairwise asymmetry on
essential inputs rules out every larger constant-free read-once NAND term. -/
theorem asymmetric_not_read_once (program : Program inputs gates) (source : Source inputs gates)
    (atFalse : source.eval (fun _ => false) (program.eval (fun _ => false)) = true)
    (asymmetric : ∀ first second : Fin inputs, first ≠ second →
      Essential (fun input => source.eval input (program.eval input)) first →
      Essential (fun input => source.eval input (program.eval input)) second →
      ∃ input, source.eval input (program.eval input) ≠
        source.eval (inputSwap first second input) (program.eval (inputSwap first second input))) :
    ¬ (constants (expression program source) = 0 ∧ (variables (expression program source)).Nodup) := by
  intro structural
  rcases expression_leaf_or_swap program source structural.1 structural.2 with
    ⟨index,direct⟩ | ⟨first,second,different,firstEssential,secondEssential,preserved⟩
  · have impossible := direct (fun _ => false)
    rw [atFalse] at impossible
    exact Bool.noConfusion impossible
  · obtain ⟨input,changed⟩ := asymmetric first second different firstEssential secondEssential
    exact changed (preserved input)

/-- This closes all physical loss cases of the joint size bound for the
stated semantic interface. Extracting that interface from arbitrary supports
is a separate obligation, not a supplied proof hidden in this statement. -/
theorem single_common_asymmetric_bound (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common)
    (onlyCommon : ∀ index,
      Essential (fun input => left.eval input (program.eval input)) index →
      Essential (fun input => right.eval input (program.eval input)) index → index = common)
    (atFalse : left.eval (fun _ => false) (program.eval (fun _ => false)) = true)
    (asymmetric : ∀ first second : Fin inputs, first ≠ second →
      Essential (fun input => left.eval input (program.eval input)) first →
      Essential (fun input => left.eval input (program.eval input)) second →
      ∃ input, left.eval input (program.eval input) ≠
        left.eval (inputSwap first second input) (program.eval (inputSwap first second input))) :
    inputs + 2 ≤ (before ++ left :: middle ++ right :: after).length + gates := by
  by_cases enough : inputs + 2 ≤ (before ++ left :: middle ++ right :: after).length + gates
  · exact enough
  · exfalso
    have small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1 := by omega
    have structural := NoReuseForest.single_common_read_once program before middle after left right
      joint small common leftEssential rightEssential onlyCommon
    exact asymmetric_not_read_once program left atFalse asymmetric ⟨structural.1,structural.2.1⟩

/-- The complete signed-prefix family cannot be represented by a constant-free
read-once raw expansion, including the one-input boundary. -/
theorem signed_prefix_not_read_once (n : Nat) (program : Program (n + 1) gates)
    (source : Source (n + 1) gates)
    (equivalent : ∀ input, source.eval input (program.eval input) = GuardedSpineFamily.coreValue n input) :
    ¬ (constants (expression program source) = 0 ∧ (variables (expression program source)).Nodup) := by
  apply asymmetric_not_read_once program source
  · rw [equivalent,GuardedSpineMinimum.value_false]
  · intro first second different _ _
    obtain ⟨input,changed⟩ := GuardedSpineMinimum.value_asymmetric n first second different
    refine ⟨input,?_⟩
    rw [equivalent,equivalent]
    exact changed

end PNP.DirectWire.ReadOnceSymmetry
