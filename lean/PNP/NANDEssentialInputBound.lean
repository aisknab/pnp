import PNP.NANDComposition

set_option autoImplicit false
set_option Elab.async false

/-! A constructive fan-in lower bound. Backwards demands share each gate
expansion, so the bound counts physical gates, not an exponentially unfolded
formula. No semantic enumeration or supplied minimum certificate is used. -/

namespace PNP.DirectWire.EssentialInputBound

variable {inputs gates : Nat}

/-- Forget the final gate; every other literal retains its identity. -/
def previous? : Source inputs (gates + 1) → Option (Source inputs gates)
  | .input index => some (.input index)
  | .constant value => some (.constant value)
  | .gate index => if h : index.val < gates then some (.gate ⟨index.val,h⟩) else none

private theorem previous_last :
    previous? (.gate (Fin.last gates) : Source inputs (gates + 1)) = none := by
  simp only [previous?,Fin.val_last,Nat.lt_irrefl,dif_neg,not_false_eq_true]

private theorem previous_none (source : Source inputs (gates + 1))
    (missing : previous? source = none) : source = .gate (Fin.last gates) := by
  cases source with
  | input index => cases missing
  | constant value => cases missing
  | gate index =>
      simp only [previous?] at missing
      split at missing
      · cases missing
      · rename_i absent
        congr 1
        apply Fin.ext
        have upper := index.isLt
        change index.val = gates
        omega

private theorem previous_eval (initial : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs (gates + 1)) (prior : Source inputs gates)
    (found : previous? source = some prior) (input : Valuation inputs) :
    source.eval input ((initial.snoc gate).eval input) =
      prior.eval input (initial.eval input) := by
  cases source with
  | input index => cases found; rfl
  | constant value => cases found; rfl
  | gate index =>
      simp only [previous?] at found
      split at found
      · rename_i before
        cases found
        have same : index = (⟨index.val,before⟩ : Fin gates).castSucc := Fin.ext rfl
        exact (congrArg ((initial.snoc gate).eval input) same).trans
          (Program.eval_snoc_castSucc initial gate input _)
      · cases found

/-- Expand the last demanded gate only once, even when it occurs repeatedly. -/
def rewind (gate : Gate inputs gates) (demand : List (Source inputs (gates + 1))) :
    List (Source inputs gates) :=
  if Source.gate (Fin.last gates) ∈ demand then
    demand.filterMap previous? ++ [gate.left,gate.right]
  else demand.filterMap previous?

private theorem filterMap_shorter {alpha beta : Type} (f : alpha → Option beta)
    (xs : List alpha) (x : alpha) (member : x ∈ xs) (missing : f x = none) :
    (xs.filterMap f).length + 1 ≤ xs.length := by
  induction xs with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst head
        simp only [List.filterMap_cons,missing,List.length_cons]
        have bound := List.length_filterMap_le f tail
        omega
      · have bound := ih later
        cases value : f head with
        | none => simp only [List.filterMap_cons,value,List.length_cons]; omega
        | some kept => simp only [List.filterMap_cons,value,List.length_cons]; omega

theorem rewind_length (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) :
    (rewind gate demand).length ≤ demand.length + 1 := by
  unfold rewind
  split
  · rename_i used
    have bound := filterMap_shorter previous? demand (.gate (Fin.last gates)) used previous_last
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · exact Nat.le_trans (List.length_filterMap_le previous? demand) (Nat.le_succ _)

private theorem rewind_previous (gate : Gate inputs gates)
    (demand : List (Source inputs (gates + 1))) (source : Source inputs (gates + 1))
    (member : source ∈ demand) (prior : Source inputs gates)
    (found : previous? source = some prior) : prior ∈ rewind gate demand := by
  have kept : prior ∈ demand.filterMap previous? := List.mem_filterMap.mpr ⟨source,member,found⟩
  unfold rewind
  split
  · exact List.mem_append_left _ kept
  · exact kept

/-- Keep only primary-input literals once no gate remains. -/
def input? : Source inputs 0 → Option (Fin inputs)
  | .input index => some index
  | .constant _ => none
  | .gate index => Fin.elim0 index

/-- Source-derived input demands, with sharing handled at every reverse step. -/
def required : {gates : Nat} → Program inputs gates →
    List (Source inputs gates) → List (Fin inputs)
  | _,.empty,demand => demand.filterMap input?
  | _,.snoc initial gate,demand => required initial (rewind gate demand)

theorem required_length (program : Program inputs gates) (demand : List (Source inputs gates)) :
    (required program demand).length ≤ demand.length + gates := by
  induction program with
  | empty => exact List.length_filterMap_le input? demand
  | @snoc size initial gate ih =>
      have smaller := ih (rewind gate demand)
      have step := rewind_length gate demand
      change (required initial (rewind gate demand)).length ≤ demand.length + (size + 1)
      omega

/-- Agreement on computed primary demands suffices for every demanded wire. -/
theorem required_sound (program : Program inputs gates) (demand : List (Source inputs gates))
    (left right : Valuation inputs)
    (agree : ∀ index, index ∈ required program demand → left index = right index) :
    ∀ source, source ∈ demand →
      source.eval left (program.eval left) = source.eval right (program.eval right) := by
  induction program with
  | empty =>
      intro source member
      cases source with
      | input index => exact agree index (List.mem_filterMap.mpr ⟨.input index,member,rfl⟩)
      | constant _ => rfl
      | gate index => exact Fin.elim0 index
  | @snoc size initial gate ih =>
      have earlier := ih (rewind gate demand) agree
      intro source member
      cases found : previous? source with
      | some prior =>
          exact (previous_eval initial gate source prior found left).trans
            ((earlier prior (rewind_previous gate demand source member prior found)).trans
              (previous_eval initial gate source prior found right).symm)
      | none =>
          have last := previous_none source found
          subst source
          have lhs : gate.left ∈ rewind gate demand := by
            simp only [rewind,if_pos member]
            exact List.mem_append_right _ (List.mem_cons_self)
          have rhs : gate.right ∈ rewind gate demand := by
            simp only [rewind,if_pos member]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
          change (initial.snoc gate).eval left (Fin.last size) =
            (initial.snoc gate).eval right (Fin.last size)
          rw [Program.eval_snoc_last,Program.eval_snoc_last]
          unfold Gate.eval
          rw [earlier _ lhs,earlier _ rhs]

/-- Changing only this input can change the scalar Boolean output. -/
def Essential (f : Valuation inputs → Bool) (index : Fin inputs) : Prop :=
  ∃ left right, (∀ other, other ≠ index → left other = right other) ∧ f left ≠ f right

theorem essential_mem (program : Program inputs gates) (source : Source inputs gates)
    (index : Fin inputs)
    (essential : Essential (fun input => source.eval input (program.eval input)) index) :
    index ∈ required program [source] := by
  by_cases present : index ∈ required program [source]
  · exact present
  · obtain ⟨left,right,agree,changed⟩ := essential
    have same := required_sound program [source] left right (by
      intro other member
      apply agree other
      intro equal
      subst other
      exact present member) source List.mem_cons_self
    exact False.elim (changed same)

private theorem ofFn_distinct {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (injective : Function.Injective value) :
    (List.ofFn value).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right lb rb less same
  have l : left < width := by simpa only [List.length_ofFn] using lb
  have r : right < width := by simpa only [List.length_ofFn] using rb
  have equal : value ⟨left,l⟩ = value ⟨right,r⟩ := by
    simpa only [List.getElem_ofFn] using same
  have indices : left = right := congrArg Fin.val (injective equal)
  omega

private theorem nodup_length_le_subset {alpha : Type} {left right : List alpha}
    (distinct : left.Nodup) (included : ∀ item, item ∈ left → item ∈ right) :
    left.length ≤ right.length := by
  induction left generalizing right with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      obtain ⟨before,after,rfl⟩ := List.append_of_mem (included head List.mem_cons_self)
      obtain ⟨headAbsent,tailDistinct⟩ := List.nodup_cons.mp distinct
      have tailIncluded : ∀ item, item ∈ tail → item ∈ before ++ after := by
        intro item member
        rcases List.mem_append.mp (included item (List.mem_cons_of_mem head member)) with first | rest
        · exact List.mem_append_left _ first
        · rcases List.mem_cons.mp rest with same | last
          · subst item
            exact False.elim (headAbsent member)
          · exact List.mem_append_right _ last
      have smaller := ih tailDistinct tailIncluded
      simp only [List.length_cons,List.length_append] at smaller ⊢
      omega

/-- A single output depending essentially on every input needs at least inputs-1
physical gates, even in the presence of arbitrary sharing and constants. -/
theorem all_essential_bound (program : Program inputs gates) (source : Source inputs gates)
    (essential : ∀ index, Essential (fun input => source.eval input (program.eval input)) index) :
    inputs ≤ gates + 1 := by
  have distinct := ofFn_distinct (id : Fin inputs → Fin inputs) (fun _ _ same => same)
  have included : ∀ index, index ∈ List.ofFn (id : Fin inputs → Fin inputs) →
      index ∈ required program [source] := fun index _ => essential_mem program source index (essential index)
  have lower := nodup_length_le_subset distinct included
  have upper := required_length program [source]
  simp only [List.length_ofFn] at lower
  simp only [List.length_cons,List.length_nil] at upper
  omega

end PNP.DirectWire.EssentialInputBound
