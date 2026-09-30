import PNP.NANDSingleReuseForest

set_option autoImplicit false
set_option Elab.async false

/-! Cross-output consequences of a single physical reuse. Distinct output
positions are retained as a list decomposition, even when their source values
coincide. The tight-budget corollary derives distinct backward demands. -/

namespace PNP.DirectWire.SharedOutputOverlap
open NormalizationTerm (Term value)
open ReadOnceTerm (variables)
open DemandForest (constants expression expand)
open SingleReuseForest (replaceInput cutExpression cutVariables cutWeightTotal)
open EssentialInputBound (Essential required)
open DemandDeficit (tally JointEssential inputExcess)

variable {inputs gates : Nat}

theorem replacement_count (marker : Nat) (replacement term : Term) (index : Nat) :
    (variables (replaceInput marker replacement term)).count index =
      (if index = marker then 0 else (variables term).count index) +
        (variables term).count marker * (variables replacement).count index := by
  induction term with
  | constant bit =>
      by_cases selected : index = marker
      · simp only [replaceInput,variables,List.count_nil,if_pos selected,Nat.zero_mul,Nat.zero_add]
      · simp only [replaceInput,variables,List.count_nil,if_neg selected,Nat.zero_mul,Nat.zero_add]
  | input actual =>
      by_cases selected : actual = marker
      · subst actual
        rw [replaceInput,if_pos rfl]
        by_cases sought : index = marker
        · subst index
          simp only [variables,List.count_cons_self,List.count_nil,if_true,
            Nat.zero_add,Nat.one_mul]
        · simp only [variables,List.count_cons_self,List.count_nil,if_neg sought,
            List.count_cons_of_ne (Ne.symm sought),Nat.zero_add,Nat.one_mul]
      · rw [replaceInput,if_neg selected]
        by_cases sought : index = marker
        · subst index
          simp only [variables,List.count_cons_of_ne selected,List.count_nil,if_true,
            Nat.zero_mul,Nat.zero_add]
        · simp only [variables,List.count_cons_of_ne selected,List.count_nil,if_neg sought,
            Nat.zero_mul,Nat.add_zero]
  | node left right ihLeft ihRight =>
      simp only [replaceInput,variables,List.count_append,ihLeft,ihRight,Nat.add_mul]
      by_cases selected : index = marker
      · rw [if_pos selected,if_pos selected,if_pos selected]
        omega
      · rw [if_neg selected,if_neg selected,if_neg selected]
        omega

theorem replacement_constants (marker : Nat) (replacement term : Term) :
    constants (replaceInput marker replacement term) =
      constants term + (variables term).count marker * constants replacement := by
  induction term with
  | constant bit =>
      simp only [replaceInput,constants,variables,List.count_nil,Nat.zero_mul,Nat.add_zero]
  | input actual =>
      by_cases selected : actual = marker
      · subst actual
        simp only [replaceInput,if_true,constants,variables,List.count_cons_self,
          List.count_nil,Nat.zero_add,Nat.one_mul]
      · simp only [replaceInput,if_neg selected,constants,variables,
          List.count_cons_of_ne selected,List.count_nil,Nat.zero_mul,Nat.zero_add]
  | node left right ihLeft ihRight =>
      simp only [replaceInput,constants,variables,List.count_append,ihLeft,ihRight,Nat.add_mul]
      omega

theorem replacement_contains (marker : Nat) (replacement term : Term)
    (used : marker ∈ variables term) (index : Nat) (member : index ∈ variables replacement) :
    index ∈ variables (replaceInput marker replacement term) := by
  induction term with
  | constant bit => cases used
  | input actual =>
      have same : marker = actual := List.mem_singleton.mp used
      subst actual
      rw [replaceInput,if_pos rfl]
      exact member
  | node left right ihLeft ihRight =>
      rcases List.mem_append.mp used with inLeft | inRight
      · exact List.mem_append_left _ (ihLeft inLeft)
      · exact List.mem_append_right _ (ihRight inRight)

/-- Exactly one marker occurrence and separation of real primaries suffice;
no read-once correctness certificate is accepted for the substituted term. -/
theorem replacement_read_once (marker : Nat) (replacement term : Term)
    (replacementConstant : constants replacement = 0) (termConstant : constants term = 0)
    (replacementMarker : (variables replacement).count marker = 0)
    (termMarker : (variables term).count marker = 1)
    (separate : ∀ index, index ≠ marker →
      (variables term).count index + (variables replacement).count index ≤ 1) :
    constants (replaceInput marker replacement term) = 0 ∧
      (variables (replaceInput marker replacement term)).Nodup := by
  constructor
  · rw [replacement_constants,replacementConstant,termConstant,Nat.mul_zero,Nat.zero_add]
  · apply List.nodup_iff_count.mpr
    intro index
    rw [replacement_count,termMarker,Nat.one_mul]
    by_cases selected : index = marker
    · rw [selected,if_pos rfl,replacementMarker,Nat.zero_add]
      exact Nat.zero_le _
    · rw [if_neg selected]
      exact separate index selected

private theorem source_essential_mem (program : Program inputs gates) (source : Source inputs gates)
    (index : Fin inputs) (essential : Essential (fun input => source.eval input (program.eval input)) index) :
    index.val ∈ variables (expression program source) := by
  apply ReadOnceTerm.essential_mem (expression program source) index.val
  obtain ⟨left,right,agree,changed⟩ := essential
  refine ⟨DemandForest.extendInput left,DemandForest.extendInput right,?_,?_⟩
  · intro other different
    unfold DemandForest.extendInput
    by_cases bound : other < inputs
    · rw [dif_pos bound,dif_pos bound]
      apply agree ⟨other,bound⟩
      intro same
      exact different (congrArg Fin.val same)
    · rw [dif_neg bound,dif_neg bound]
  · rw [DemandForest.expression_sound,DemandForest.expression_sound]
    exact changed

private theorem two_counts (cut : Nat) (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates) (index : Nat) :
    (variables (cutExpression cut program left)).count index +
      (variables (cutExpression cut program right)).count index ≤
        (cutVariables cut program (before ++ left :: middle ++ right :: after)).count index := by
  simp only [cutVariables,List.flatMap_append,List.flatMap_cons,List.count_append]
  omega

private theorem two_constants (cut : Nat) (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates) :
    constants (cutExpression cut program left) + constants (cutExpression cut program right) ≤
      cutWeightTotal constants cut program (before ++ left :: middle ++ right :: after) := by
  simp only [cutWeightTotal,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
  omega

private theorem perm_from_coverage {alpha : Type} {left right : List alpha}
    (distinct : left.Nodup) (included : ∀ item, item ∈ left → item ∈ right)
    (size : left.length = right.length) : left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.nil
      | cons head tail =>
          simp only [List.length_nil,List.length_cons] at size
          exfalso
          omega
  | cons head tail ih =>
      obtain ⟨before,after,rfl⟩ := List.append_of_mem (included head List.mem_cons_self)
      obtain ⟨absent,prior⟩ := List.nodup_cons.mp distinct
      have tailIncluded : ∀ item, item ∈ tail → item ∈ before ++ after := by
        intro item member
        rcases List.mem_append.mp (included item (List.mem_cons_of_mem head member)) with first | rest
        · exact List.mem_append_left _ first
        · rcases List.mem_cons.mp rest with same | later
          · subst item
            exact False.elim (absent member)
          · exact List.mem_append_right _ later
      have tailSize : tail.length = (before ++ after).length := by
        simp only [List.length_cons,List.length_append] at size ⊢
        omega
      exact ((ih prior tailIncluded tailSize).cons head).trans List.perm_middle.symm

private theorem all_inputs_distinct (width : Nat) :
    (List.ofFn (id : Fin width → Fin width)).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right lb rb less same
  have l : left < width := by simpa only [List.length_ofFn] using lb
  have r : right < width := by simpa only [List.length_ofFn] using rb
  have equal : (⟨left,l⟩ : Fin width) = ⟨right,r⟩ := by
    simpa only [List.getElem_ofFn,id_eq] using same
  have indices : left = right := congrArg Fin.val equal
  omega

/-- Joint essentiality supplies coverage; zero excess turns coverage into an
exact permutation of the input universe, not merely a cardinality bound. -/
theorem joint_zero_excess_distinct (program : Program inputs gates)
    (demand : List (Source inputs gates)) (joint : JointEssential program demand)
    (zero : inputExcess program demand = 0) : (required program demand).Nodup := by
  have lower := DemandDeficit.joint_required_length program demand joint
  have size : (List.ofFn (id : Fin inputs → Fin inputs)).length =
      (required program demand).length := by
    simp only [List.length_ofFn]
    unfold inputExcess at zero
    omega
  have included : ∀ index, index ∈ List.ofFn (id : Fin inputs → Fin inputs) →
      index ∈ required program demand := by
    intro index _
    obtain ⟨source,member,essential⟩ := joint index
    exact DemandDeficit.essential_demand_mem program demand source member index essential
  exact (perm_from_coverage (all_inputs_distinct inputs) included size).nodup (all_inputs_distinct inputs)

/-- Two distinct demanded positions sharing one essential input share at least
two, in the actual no-repeated-primary, one-physical-reuse case. -/
theorem two_output_overlap (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (noUnused : (tally program (before ++ left :: middle ++ right :: after)).unusedGates = 0)
    (oneReuse : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 1)
    (noConstants : (tally program (before ++ left :: middle ++ right :: after)).constantDemands = 0)
    (distinct : (required program (before ++ left :: middle ++ right :: after)).Nodup)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common) :
    ∃ first second : Fin inputs, first ≠ second ∧
      Essential (fun input => left.eval input (program.eval input)) first ∧
      Essential (fun input => right.eval input (program.eval input)) first ∧
      Essential (fun input => left.eval input (program.eval input)) second ∧
      Essential (fun input => right.eval input (program.eval input)) second := by
  obtain ⟨cut,_,_,cutConstant,sharedConstant,_,markerTotal,separated,twoEssential⟩ :=
    SingleReuseForest.one_reuse_semantic program (before ++ left :: middle ++ right :: after)
      noUnused oneReuse noConstants distinct
  let shared := expand program cut
  let lterm := cutExpression cut.val program left
  let rterm := cutExpression cut.val program right
  have pairBound : ∀ index, (variables lterm).count index + (variables rterm).count index ≤
      (cutVariables cut.val program (before ++ left :: middle ++ right :: after)).count index :=
    two_counts cut.val program before middle after left right
  have realBound : ∀ index, index ≠ inputs →
      (variables lterm).count index + (variables rterm).count index +
        (variables shared).count index ≤ 1 := by
    intro index different
    have pair := pairBound index
    have total := separated index different
    dsimp only [shared]
    omega
  have markerBound : (variables lterm).count inputs + (variables rterm).count inputs ≤ 2 := by
    have bound := pairBound inputs
    rw [markerTotal] at bound
    exact bound
  have leftOccurs := List.count_pos_iff.mpr (source_essential_mem program left common leftEssential)
  have rightOccurs := List.count_pos_iff.mpr (source_essential_mem program right common rightEssential)
  have commonNotMarker : common.val ≠ inputs := Nat.ne_of_lt common.isLt
  have leftCount : (variables (expression program left)).count common.val =
      (variables lterm).count common.val +
        (variables lterm).count inputs * (variables shared).count common.val := by
    have count := replacement_count inputs shared lterm common.val
    rw [SingleReuseForest.cutExpression_factorization,if_neg commonNotMarker] at count
    exact count
  have rightCount : (variables (expression program right)).count common.val =
      (variables rterm).count common.val +
        (variables rterm).count inputs * (variables shared).count common.val := by
    have count := replacement_count inputs shared rterm common.val
    rw [SingleReuseForest.cutExpression_factorization,if_neg commonNotMarker] at count
    exact count
  have commonBudget := realBound common.val commonNotMarker
  have sharedPositive : 0 < (variables shared).count common.val := by
    by_cases zero : (variables shared).count common.val = 0
    · rw [zero,Nat.mul_zero,Nat.add_zero] at leftCount rightCount
      exfalso
      omega
    · exact Nat.pos_of_ne_zero zero
  have leftMarkerPositive : 0 < (variables lterm).count inputs := by
    by_cases zero : (variables lterm).count inputs = 0
    · rw [zero,Nat.zero_mul,Nat.add_zero] at leftCount
      exfalso
      omega
    · exact Nat.pos_of_ne_zero zero
  have rightMarkerPositive : 0 < (variables rterm).count inputs := by
    by_cases zero : (variables rterm).count inputs = 0
    · rw [zero,Nat.zero_mul,Nat.add_zero] at rightCount
      exfalso
      omega
    · exact Nat.pos_of_ne_zero zero
  have leftMarker : (variables lterm).count inputs = 1 := by omega
  have rightMarker : (variables rterm).count inputs = 1 := by omega
  have constBound : constants lterm + constants rterm ≤
      cutWeightTotal constants cut.val program (before ++ left :: middle ++ right :: after) :=
    two_constants cut.val program before middle after left right
  have leftConstant : constants lterm = 0 := by omega
  have rightConstant : constants rterm = 0 := by omega
  have sharedMarker : (variables shared).count inputs = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro member
    exact Nat.lt_irrefl inputs (ReadOnceTerm.expression_variables_lt program (.gate cut) inputs member)
  have leftSeparated : ∀ index, index ≠ inputs →
      (variables lterm).count index + (variables shared).count index ≤ 1 := by
    intro index different
    have bound := realBound index different
    omega
  have rightSeparated : ∀ index, index ≠ inputs →
      (variables rterm).count index + (variables shared).count index ≤ 1 := by
    intro index different
    have bound := realBound index different
    omega
  have leftRead := replacement_read_once inputs shared lterm sharedConstant leftConstant sharedMarker
    leftMarker leftSeparated
  have rightRead := replacement_read_once inputs shared rterm sharedConstant rightConstant sharedMarker
    rightMarker rightSeparated
  rw [SingleReuseForest.cutExpression_factorization] at leftRead rightRead
  have transfer (source : Source inputs gates) (term : Term)
      (atTerm : term = cutExpression cut.val program source)
      (markerUsed : inputs ∈ variables term)
      (noConstant : constants (expression program source) = 0)
      (readOnce : (variables (expression program source)).Nodup)
      (index : Fin inputs) (essential : Essential (fun input => program.eval input cut) index) :
      Essential (fun input => source.eval input (program.eval input)) index := by
    have sharedMember := source_essential_mem program (.gate cut) index essential
    have member := replacement_contains inputs shared term markerUsed index.val sharedMember
    rw [atTerm,SingleReuseForest.cutExpression_factorization] at member
    exact ReadOnceTerm.expression_essential program source noConstant readOnce index member
  obtain ⟨first,second,different,firstEssential,secondEssential⟩ := twoEssential
  exact ⟨first,second,different,
    transfer left lterm rfl (List.count_pos_iff.mp leftMarkerPositive) leftRead.1 leftRead.2 first firstEssential,
    transfer right rterm rfl (List.count_pos_iff.mp rightMarkerPositive) rightRead.1 rightRead.2 first firstEssential,
    transfer left lterm rfl (List.count_pos_iff.mp leftMarkerPositive) leftRead.1 leftRead.2 second secondEssential,
    transfer right rterm rfl (List.count_pos_iff.mp rightMarkerPositive) rightRead.1 rightRead.2 second secondEssential⟩

/-- The tight gate/output budget derives zero other losses and distinct primary
demands, closing the single-internal-sharing case without supplied structure. -/
theorem one_reuse_budget_overlap (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1)
    (oneReuse : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 1)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common) :
    ∃ first second : Fin inputs, first ≠ second ∧
      Essential (fun input => left.eval input (program.eval input)) first ∧
      Essential (fun input => right.eval input (program.eval input)) first ∧
      Essential (fun input => left.eval input (program.eval input)) second ∧
      Essential (fun input => right.eval input (program.eval input)) second := by
  have budget := DemandDeficit.one_defect_budget program
    (before ++ left :: middle ++ right :: after) joint small
  unfold DemandDeficit.Ledger.total at budget
  have unused : (tally program (before ++ left :: middle ++ right :: after)).unusedGates = 0 := by omega
  have constant : (tally program (before ++ left :: middle ++ right :: after)).constantDemands = 0 := by omega
  have extra : inputExcess program (before ++ left :: middle ++ right :: after) = 0 := by omega
  exact two_output_overlap program before middle after left right unused oneReuse constant
    (joint_zero_excess_distinct program _ joint extra) common leftEssential rightEssential


/-- The one-shared-guard semantic pattern excludes every internal reuse under
the tight budget. This is a case of the joint bound, not the entire minimum. -/
theorem single_shared_input_excludes_reuse (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common)
    (onlyCommon : ∀ index,
      Essential (fun input => left.eval input (program.eval input)) index →
      Essential (fun input => right.eval input (program.eval input)) index → index = common) :
    (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 0 := by
  by_cases zero : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 0
  · exact zero
  · have budget := DemandDeficit.one_defect_budget program
      (before ++ left :: middle ++ right :: after) joint small
    unfold DemandDeficit.Ledger.total at budget
    have once : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 1 := by omega
    obtain ⟨first,second,different,lf,rf,ls,rs⟩ :=
      one_reuse_budget_overlap program before middle after left right joint small once common
        leftEssential rightEssential
    exact False.elim (different ((onlyCommon first lf rf).trans (onlyCommon second ls rs).symm))

end PNP.DirectWire.SharedOutputOverlap
