import PNP.NANDReadOnceSymmetry

set_option autoImplicit false
set_option Elab.async false

/-! Joint asymmetric bounds with every demanded output occurrence retained.
The zero-extra case derives raw read-once structure, not a replacement premise. -/

namespace PNP.DirectWire.JointAsymmetricBound
open NormalizationTerm (Term)
open ReadOnceTerm (variables)
open DemandForest (constants expression weightTotal)
open EssentialInputBound (Essential required)
open DemandDeficit (JointEssential tally inputExcess)
open TightDemandSymmetry (inputSwap)

variable {inputs gates outputs : Nat}

private theorem member_weight (weight : Term → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) (source : Source inputs gates)
    (member : source ∈ demand) :
    weight (expression program source) ≤ weightTotal weight program demand := by
  induction demand with
  | nil => cases member
  | cons head tail ih =>
      change weight (expression program source) ≤
        weight (expression program head) + weightTotal weight program tail
      rcases List.mem_cons.mp member with same | within
      · subst source
        omega
      · have bound := ih within
        omega

private theorem member_occurrences (program : Program inputs gates)
    (demand : List (Source inputs gates)) (source : Source inputs gates)
    (member : source ∈ demand) (index : Nat) :
    (variables (expression program source)).count index ≤
      (NoReuseForest.forestVariables program demand).count index := by
  induction demand with
  | nil => cases member
  | cons head tail ih =>
      simp only [NoReuseForest.forestVariables,List.flatMap_cons,List.count_append]
      rcases List.mem_cons.mp member with same | within
      · subst source
        omega
      · have bound := ih within
        change (variables (expression program source)).count index ≤
          (variables (expression program head)).count index +
            (NoReuseForest.forestVariables program tail).count index
        omega

private theorem distinct_values (items : List (Fin inputs)) (distinct : items.Nodup) :
    (items.map Fin.val).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      obtain ⟨absent,prior⟩ := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      refine ⟨?_,ih prior⟩
      intro member
      obtain ⟨other,within,same⟩ := List.mem_map.mp member
      exact absent ((Fin.ext same : other = head) ▸ within)

/-- A zero-extra total budget forces every actual demanded raw term read-once. -/
theorem zero_budget_read_once (program : Program inputs gates)
    (demand : List (Source inputs gates)) (joint : JointEssential program demand)
    (small : demand.length + gates ≤ inputs)
    (source : Source inputs gates) (member : source ∈ demand) :
    constants (expression program source) = 0 ∧
      (variables (expression program source)).Nodup := by
  have accounting := DemandDeficit.joint_accounting program demand joint
  have zero : (tally program demand).total = 0 := by omega
  have extra : inputExcess program demand = 0 := by omega
  have noReuse : (tally program demand).repeatedGateUses = 0 := by
    unfold DemandDeficit.Ledger.total at zero
    omega
  have noConstants := DemandForest.zero_loss_constants program demand zero
  have constantBound := member_weight constants program demand source member
  have distinct := distinct_values (required program demand)
    (SharedOutputOverlap.joint_zero_excess_distinct program demand joint extra)
  refine ⟨by omega,List.nodup_iff_count.mpr ?_⟩
  intro index
  have occurrences := member_occurrences program demand source member index
  rw [NoReuseForest.no_reuse_occurrences program demand noReuse index] at occurrences
  have bound := List.nodup_iff_count.mp distinct index
  omega

/-- One asymmetric demanded output rules out the zero-extra joint budget. -/
theorem asymmetric_bound (program : Program inputs gates)
    (demand : List (Source inputs gates)) (joint : JointEssential program demand)
    (source : Source inputs gates) (member : source ∈ demand)
    (atFalse : source.eval (fun _ => false) (program.eval (fun _ => false)) = true)
    (asymmetric : ∀ first second : Fin inputs, first ≠ second →
      Essential (fun input => source.eval input (program.eval input)) first →
      Essential (fun input => source.eval input (program.eval input)) second →
      ∃ input, source.eval input (program.eval input) ≠
        source.eval (inputSwap first second input) (program.eval (inputSwap first second input))) :
    inputs + 1 ≤ demand.length + gates := by
  by_cases enough : inputs + 1 ≤ demand.length + gates
  · exact enough
  · exfalso
    exact ReadOnceSymmetry.asymmetric_not_read_once program source atFalse asymmetric
      (zero_budget_read_once program demand joint (by omega) source member)

/-- Select two positions, not two distinct values. Equal source values retain
both occurrences and cannot be erased from a joint demand argument. -/
theorem two_positions_permutation {alpha : Type} (items : List alpha)
    (first second : Fin items.length) (different : first ≠ second) :
    ∃ rest : List alpha, items.Perm (items.get first :: items.get second :: rest) := by
  induction items with
  | nil => exact Fin.elim0 first
  | cons head tail ih =>
      rcases first with ⟨i,ib⟩
      rcases second with ⟨j,jb⟩
      cases i with
      | zero =>
          cases j with
          | zero => exact False.elim (different rfl)
          | succ j =>
              let index : Fin tail.length := ⟨j,by change j + 1 < tail.length + 1 at jb; omega⟩
              obtain ⟨before,after,split⟩ := List.append_of_mem (List.get_mem tail index)
              refine ⟨before ++ after,?_⟩
              change (head :: tail).Perm (head :: tail.get index :: (before ++ after))
              exact ((List.Perm.of_eq split).trans List.perm_middle).cons head
      | succ i =>
          let left : Fin tail.length := ⟨i,by change i + 1 < tail.length + 1 at ib; omega⟩
          cases j with
          | zero =>
              obtain ⟨before,after,split⟩ := List.append_of_mem (List.get_mem tail left)
              refine ⟨before ++ after,?_⟩
              change (head :: tail).Perm (tail.get left :: head :: (before ++ after))
              exact (((List.Perm.of_eq split).trans List.perm_middle).cons head).trans (List.Perm.swap _ _ _)
          | succ j =>
              let right : Fin tail.length := ⟨j,by change j + 1 < tail.length + 1 at jb; omega⟩
              have distinct : left ≠ right := by
                intro same
                apply different
                apply Fin.ext
                have values := congrArg (fun index : Fin tail.length => index.val) same
                change i + 1 = j + 1
                change i = j at values
                omega
              obtain ⟨rest,permutation⟩ := ih left right distinct
              refine ⟨head :: rest,?_⟩
              change (head :: tail).Perm (tail.get left :: tail.get right :: head :: rest)
              exact (permutation.cons head).trans
                ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

/-- Two distinct output positions with exactly one common essential input
inherit the two-extra bound without an injective output-word assumption. -/
theorem two_output_positions_bound (program : Program inputs gates)
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
    inputs + 2 ≤ outputs + gates := by
  let first : Fin (List.ofFn word.source).length := ⟨left.val,by simpa only [List.length_ofFn] using left.isLt⟩
  let second : Fin (List.ofFn word.source).length := ⟨right.val,by simpa only [List.length_ofFn] using right.isLt⟩
  have distinct : first ≠ second := by
    intro same
    apply different
    apply Fin.ext
    exact congrArg (fun index : Fin (List.ofFn word.source).length => index.val) same
  obtain ⟨rest,permutation⟩ := two_positions_permutation (List.ofFn word.source) first second distinct
  have firstGet : (List.ofFn word.source).get first = word.source left := by
    simp only [List.get_eq_getElem,List.getElem_ofFn]
    apply congrArg word.source
    exact Fin.ext rfl
  have secondGet : (List.ofFn word.source).get second = word.source right := by
    simp only [List.get_eq_getElem,List.getElem_ofFn]
    apply congrArg word.source
    exact Fin.ext rfl
  rw [firstGet,secondGet] at permutation
  have reordered : JointEssential program (word.source left :: word.source right :: rest) := by
    intro index
    obtain ⟨source,member,essential⟩ := joint index
    exact ⟨source,permutation.mem_iff.mp member,essential⟩
  have bound := ReadOnceSymmetry.single_common_asymmetric_bound program [] [] rest
    (word.source left) (word.source right) reordered common leftEssential rightEssential
    onlyCommon atFalse asymmetric
  have size := permutation.length_eq
  simp only [List.length_ofFn] at size
  change inputs + 2 ≤ (word.source left :: word.source right :: rest).length + gates at bound
  rw [← size] at bound
  exact bound

end PNP.DirectWire.JointAsymmetricBound
