import PNP.NANDSharedOutputOverlap

set_option autoImplicit false
set_option Elab.async false

/-! Exact primary multiplicity without internal gate reuse. No assumption of
zero unused-gate or constant loss is needed for the occurrence identity.
Tight shared-input interfaces derive, rather than assume, read-once outputs. -/

namespace PNP.DirectWire.NoReuseForest
open NormalizationTerm (Term value)
open ReadOnceTerm (variables)
open DemandForest (constants expression variableWeight weightTotal inputWeight)
open EssentialInputBound (Essential required previous? rewind input?)
open DemandDeficit (tally lastUses JointEssential inputExcess)

variable {inputs gates : Nat}

private theorem weightTotal_sum (weight : Term → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) :
    weightTotal weight program demand =
      (demand.map (fun source => weight (expression program source))).sum := by
  induction demand with
  | nil => rfl
  | cons head tail ih =>
      change weight (expression program head) + weightTotal weight program tail = _
      simp only [List.map_cons,List.sum_cons,ih]

private theorem weightTotal_append (weight : Term → Nat) (program : Program inputs gates)
    (left right : List (Source inputs gates)) :
    weightTotal weight program (left ++ right) =
      weightTotal weight program left + weightTotal weight program right := by
  simp only [weightTotal_sum,List.map_append,List.sum_append]

private theorem no_reuse_step (weight : Term → Nat)
    (additive : ∀ left right, weight (.node left right) = weight left + weight right)
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1)))
    (zero : (tally (.snoc initial gate) demand).repeatedGateUses = 0) :
    (tally initial (rewind gate demand)).repeatedGateUses = 0 ∧
      weightTotal weight (.snoc initial gate) demand =
        weightTotal weight initial (rewind gate demand) := by
  have step := DemandForest.weightTotal_step weight initial gate demand
  by_cases used : Source.gate (Fin.last gates) ∈ demand
  · have positive := DemandDeficit.lastUses_positive demand used
    simp only [tally,if_pos used] at zero
    have once : lastUses demand = 1 := by omega
    have prior : (tally initial (rewind gate demand)).repeatedGateUses = 0 := by omega
    refine ⟨prior,?_⟩
    rw [once,Nat.one_mul,additive] at step
    rw [rewind,if_pos used,weightTotal_append]
    change weightTotal weight (.snoc initial gate) demand =
      weightTotal weight initial (demand.filterMap previous?) +
        (weight (expression initial gate.left) + (weight (expression initial gate.right) + 0))
    simpa only [Nat.add_zero] using step
  · simp only [tally,if_neg used] at zero
    refine ⟨zero,?_⟩
    simp only [DemandDeficit.lastUses_zero demand used,Nat.zero_mul,Nat.add_zero] at step
    simpa only [rewind,if_neg used] using step

private theorem empty_inputs (weights : Nat → Nat) (demand : List (Source inputs 0)) :
    weightTotal (variableWeight weights) .empty demand =
      inputWeight weights (demand.filterMap input?) := by
  induction demand with
  | nil => rfl
  | cons source tail ih =>
      cases source with
      | input index =>
          change weights index.val + weightTotal (variableWeight weights) .empty tail = _
          simp only [List.filterMap_cons,input?]
          change weights index.val + weightTotal (variableWeight weights) .empty tail =
            weights index.val + inputWeight weights (tail.filterMap input?)
          rw [ih]
      | constant bit =>
          change 0 + weightTotal (variableWeight weights) .empty tail = _
          rw [Nat.zero_add]
          exact ih
      | gate index => exact Fin.elim0 index

/-- Primary occurrence conservation needs no internal reuse, not zero total
physical loss. Unused physical gates and demanded constants are allowed. -/
theorem no_reuse_inputs (weights : Nat → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates))
    (zero : (tally program demand).repeatedGateUses = 0) :
    weightTotal (variableWeight weights) program demand =
      inputWeight weights (required program demand) := by
  induction program with
  | empty => exact empty_inputs weights demand
  | @snoc size initial gate ih =>
      obtain ⟨prior,step⟩ := no_reuse_step (variableWeight weights) (fun _ _ => rfl)
        initial gate demand zero
      rw [step,ih (rewind gate demand) prior]
      rfl

/-- Retain each demanded position and every raw primary occurrence. -/
def forestVariables (program : Program inputs gates) (demand : List (Source inputs gates)) : List Nat :=
  demand.flatMap (fun source => variables (expression program source))

private theorem forest_weight (weights : Nat → Nat) (program : Program inputs gates)
    (demand : List (Source inputs gates)) :
    weightTotal (variableWeight weights) program demand =
      ((forestVariables program demand).map weights).sum := by
  induction demand with
  | nil => rfl
  | cons source tail ih =>
      change variableWeight weights (expression program source) +
        weightTotal (variableWeight weights) program tail = _
      rw [ReadOnceTerm.variables_weight,ih]
      simp only [forestVariables,List.flatMap_cons,List.map_append,List.sum_append]

private def pointWeight (needle : Nat) : Nat → Nat :=
  fun index => if index = needle then 1 else 0

private theorem point_sum (needle : Nat) (items : List Nat) :
    (items.map (pointWeight needle)).sum = items.count needle := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons,List.sum_cons,ih]
      by_cases same : head = needle
      · have atHead : pointWeight needle head = 1 := if_pos same
        rw [atHead,same,List.count_cons_self]
        omega
      · have atHead : pointWeight needle head = 0 := if_neg same
        rw [atHead,List.count_cons_of_ne same,Nat.zero_add]

private theorem input_point_sum (needle : Nat) (items : List (Fin inputs)) :
    inputWeight (pointWeight needle) items = (items.map Fin.val).count needle := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change pointWeight needle head.val + inputWeight (pointWeight needle) tail = _
      rw [ih,List.map_cons]
      by_cases same : head.val = needle
      · have atHead : pointWeight needle head.val = 1 := if_pos same
        rw [atHead,same,List.count_cons_self]
        omega
      · have atHead : pointWeight needle head.val = 0 := if_neg same
        rw [atHead,List.count_cons_of_ne same,Nat.zero_add]

private theorem nodup_input_values (items : List (Fin inputs)) (distinct : items.Nodup) :
    (items.map Fin.val).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      obtain ⟨absent,prior⟩ := List.nodup_cons.mp distinct
      change (head.val :: tail.map Fin.val).Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_,ih prior⟩
      intro member
      obtain ⟨other,within,same⟩ := List.mem_map.mp member
      have equal : other = head := Fin.ext same
      exact absent (equal ▸ within)


/-- Equality of every multiplicity, not only total input cardinality. -/
theorem no_reuse_occurrences (program : Program inputs gates)
    (demand : List (Source inputs gates))
    (zero : (tally program demand).repeatedGateUses = 0) (index : Nat) :
    (forestVariables program demand).count index =
      ((required program demand).map Fin.val).count index := by
  have counted := no_reuse_inputs (pointWeight index) program demand zero
  rw [forest_weight,point_sum,input_point_sum] at counted
  exact counted

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


private theorem two_counts (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates) (index : Nat) :
    (variables (expression program left)).count index +
      (variables (expression program right)).count index ≤
        (forestVariables program (before ++ left :: middle ++ right :: after)).count index := by
  simp only [forestVariables,List.flatMap_append,List.flatMap_cons,List.count_append]
  omega

/-- A common essential input in two positions forces primary excess when no
physical gate is reused. This remains true before allocating other losses. -/
theorem shared_input_positive_excess (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (noReuse : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 0)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common) :
    0 < inputExcess program (before ++ left :: middle ++ right :: after) := by
  have l := List.count_pos_iff.mpr (source_essential_mem program left common leftEssential)
  have r := List.count_pos_iff.mpr (source_essential_mem program right common rightEssential)
  have pair := two_counts program before middle after left right common.val
  rw [no_reuse_occurrences program _ noReuse] at pair
  by_cases zero : inputExcess program (before ++ left :: middle ++ right :: after) = 0
  · have distinct := SharedOutputOverlap.joint_zero_excess_distinct program _ joint zero
    have bound := List.nodup_iff_count.mp (nodup_input_values _ distinct) common.val
    exfalso
    omega
  · exact Nat.pos_of_ne_zero zero

/-- The shared primary consumes the entire one-unit budget; unused gates and
constant demands therefore vanish without either being a theorem premise. -/
theorem shared_input_loss_allocation (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1)
    (noReuse : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 0)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common) :
    (tally program (before ++ left :: middle ++ right :: after)).total = 0 ∧
      inputExcess program (before ++ left :: middle ++ right :: after) = 1 := by
  have positive := shared_input_positive_excess program before middle after left right joint noReuse
    common leftEssential rightEssential
  have budget := DemandDeficit.one_defect_budget program _ joint small
  exact ⟨by omega,by omega⟩

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


private theorem universe_distinct (width : Nat) :
    (List.ofFn (fun index : Fin width => index.val)).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right lb rb less same
  simp only [List.getElem_ofFn] at same
  omega

private theorem one_extra_perm {domainList items : List Nat} (common : Nat)
    (distinct : domainList.Nodup) (covered : ∀ item, item ∈ domainList → item ∈ items)
    (size : items.length = domainList.length + 1) (twice : 2 ≤ items.count common) :
    items.Perm (common :: domainList) := by
  have member : common ∈ items := List.count_pos_iff.mp (by omega)
  obtain ⟨before,after,rfl⟩ := List.append_of_mem member
  have remains : common ∈ before ++ after := by
    apply List.count_pos_iff.mp
    simp only [List.count_append,List.count_cons_self] at twice ⊢
    omega
  have restCovered : ∀ item, item ∈ domainList → item ∈ before ++ after := by
    intro item present
    by_cases same : item = common
    · exact same.symm ▸ remains
    · rcases List.mem_append.mp (covered item present) with first | rest
      · exact List.mem_append_left _ first
      · rcases List.mem_cons.mp rest with equal | later
        · exact False.elim (same equal)
        · exact List.mem_append_right _ later
  have restSize : domainList.length = (before ++ after).length := by
    simp only [List.length_append,List.length_cons] at size ⊢
    omega
  have rest := perm_from_coverage distinct restCovered restSize
  exact List.perm_middle.trans (rest.symm.cons common)

/-- The actual backward demand list contains exactly the input universe plus
one further copy of the common primary. No supplied multiplicity map is used. -/
theorem shared_input_primary_permutation (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1)
    (noReuse : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 0)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common) :
    ((required program (before ++ left :: middle ++ right :: after)).map Fin.val).Perm
      (common.val :: List.ofFn (fun index : Fin inputs => index.val)) := by
  obtain ⟨_,extra⟩ := shared_input_loss_allocation program before middle after left right
    joint small noReuse common leftEssential rightEssential
  have lower := DemandDeficit.joint_required_length program _ joint
  have size : ((required program (before ++ left :: middle ++ right :: after)).map Fin.val).length =
      (List.ofFn (fun index : Fin inputs => index.val)).length + 1 := by
    simp only [List.length_map,List.length_ofFn]
    unfold inputExcess at extra
    omega
  have covered : ∀ index, index ∈ List.ofFn (fun i : Fin inputs => i.val) →
      index ∈ (required program (before ++ left :: middle ++ right :: after)).map Fin.val := by
    intro index member
    obtain ⟨actual,same⟩ := List.mem_ofFn.mp member
    obtain ⟨source,within,essential⟩ := joint actual
    exact List.mem_map.mpr ⟨actual,DemandDeficit.essential_demand_mem program _ source within actual essential,same⟩
  have l := List.count_pos_iff.mpr (source_essential_mem program left common leftEssential)
  have r := List.count_pos_iff.mpr (source_essential_mem program right common rightEssential)
  have pair := two_counts program before middle after left right common.val
  rw [no_reuse_occurrences program _ noReuse] at pair
  exact one_extra_perm common.val (universe_distinct inputs) covered size (by omega)

/-- Both actual output terms are constant-free and read-once. The tight
semantic interface supplies every structural fact needed for this conclusion. -/
theorem shared_input_read_once (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1)
    (noReuse : (tally program (before ++ left :: middle ++ right :: after)).repeatedGateUses = 0)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common) :
    constants (expression program left) = 0 ∧
      (variables (expression program left)).Nodup ∧
      constants (expression program right) = 0 ∧
      (variables (expression program right)).Nodup := by
  obtain ⟨zero,_⟩ := shared_input_loss_allocation program before middle after left right
    joint small noReuse common leftEssential rightEssential
  have totalConstants := DemandForest.zero_loss_constants program _ zero
  have constantBound : constants (expression program left) + constants (expression program right) ≤
      weightTotal constants program (before ++ left :: middle ++ right :: after) := by
    simp only [weightTotal_sum,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
    omega
  have permutation := shared_input_primary_permutation program before middle after left right
    joint small noReuse common leftEssential rightEssential
  have l := List.count_pos_iff.mpr (source_essential_mem program left common leftEssential)
  have r := List.count_pos_iff.mpr (source_essential_mem program right common rightEssential)
  have counts : ∀ index, (variables (expression program left)).count index ≤ 1 ∧
      (variables (expression program right)).count index ≤ 1 := by
    intro index
    have pair := two_counts program before middle after left right index
    rw [no_reuse_occurrences program _ noReuse,permutation.count_eq] at pair
    have bound := List.nodup_iff_count.mp (universe_distinct inputs) index
    by_cases same : common.val = index
    · subst index
      rw [List.count_cons_self] at pair
      exact ⟨by omega,by omega⟩
    · rw [List.count_cons_of_ne same] at pair
      exact ⟨by omega,by omega⟩
  exact ⟨by omega,List.nodup_iff_count.mpr (fun index => (counts index).1),
    by omega,List.nodup_iff_count.mpr (fun index => (counts index).2)⟩

/-- Combine the internal-reuse exclusion with the no-reuse argument. A single
common essential input and the tight budget force both output terms read-once. -/
theorem single_common_read_once (program : Program inputs gates)
    (before middle after : List (Source inputs gates)) (left right : Source inputs gates)
    (joint : JointEssential program (before ++ left :: middle ++ right :: after))
    (small : (before ++ left :: middle ++ right :: after).length + gates ≤ inputs + 1)
    (common : Fin inputs)
    (leftEssential : Essential (fun input => left.eval input (program.eval input)) common)
    (rightEssential : Essential (fun input => right.eval input (program.eval input)) common)
    (onlyCommon : ∀ index,
      Essential (fun input => left.eval input (program.eval input)) index →
      Essential (fun input => right.eval input (program.eval input)) index → index = common) :
    constants (expression program left) = 0 ∧
      (variables (expression program left)).Nodup ∧
      constants (expression program right) = 0 ∧
      (variables (expression program right)).Nodup := by
  have noReuse := SharedOutputOverlap.single_shared_input_excludes_reuse program before middle after
    left right joint small common leftEssential rightEssential onlyCommon
  exact shared_input_read_once program before middle after left right joint small noReuse
    common leftEssential rightEssential

end PNP.DirectWire.NoReuseForest
