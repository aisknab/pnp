import PNP.NANDTightDemandSymmetry
import PNP.NANDGuardedSpineFamily

set_option autoImplicit false
set_option Elab.async false

/-! The signed initial spine is minimum against every NAND implementation.
Unlike a plain read-once spine, it starts with NOT a and needs one gate per
essential input. The proof uses the sharp fan-in equality-case symmetry,
not semantic enumeration or a supplied minimum certificate. -/

namespace PNP.DirectWire.GuardedSpineMinimum
open EssentialInputBound TightDemandSymmetry
open GuardedSpineFamily (core coreValue core_value)

/-- Appending a fresh input is an ordinary NAND step. -/
theorem value_snoc (n : Nat) (input : Valuation (n + 1)) (last : Bool) :
    coreValue (n + 1) (input.snoc last) = boolNand (coreValue n input) last := by
  change boolNand (coreValue n (fun index => input.snoc last index.castSucc))
    (input.snoc last (Fin.last (n + 1))) = _
  simp only [Valuation.snoc_castSucc,Valuation.snoc_last]

theorem value_false (n : Nat) : coreValue n (fun _ => false) = true := by
  cases n with
  | zero => rfl
  | succ n =>
      change boolNand (coreValue n (fun _ => false)) false = true
      cases coreValue n (fun _ => false) <;> rfl

private theorem index_cases {width : Nat} (index : Fin (width + 1)) :
    (∃ earlier : Fin width, index = earlier.castSucc) ∨ index = Fin.last width := by
  by_cases before : index.val < width
  · exact Or.inl ⟨⟨index.val,before⟩,Fin.ext rfl⟩
  · apply Or.inr
    apply Fin.ext
    have upper := index.isLt
    change index.val = width
    omega

private theorem cast_not_last {width : Nat} (index : Fin width) :
    index.castSucc ≠ Fin.last width := by
  intro same
  have values := congrArg Fin.val same
  have bound := index.isLt
  change index.val = width at values
  omega

private theorem nand_true_injective :
    Function.Injective (fun bit => boolNand bit true) := by
  intro left right same
  cases left <;> cases right <;> cases same <;> rfl

/-- Every primary input has an explicit sensitivity witness. -/
theorem value_essential (n : Nat) (index : Fin (n + 1)) :
    Essential (coreValue n) index := by
  induction n with
  | zero =>
      refine ⟨(fun _ => false),(fun _ => true),?_,?_⟩
      · intro other different
        have same : other = index := by
          apply Fin.ext
          have first := other.isLt
          have second := index.isLt
          omega
        exact False.elim (different same)
      · change true ≠ false
        exact Bool.noConfusion
  | succ n ih =>
      rcases index_cases index with ⟨earlier,rfl⟩ | rfl
      · obtain ⟨left,right,agree,changed⟩ := ih earlier
        refine ⟨left.snoc true,right.snoc true,?_,?_⟩
        · intro other different
          rcases index_cases other with ⟨old,rfl⟩ | rfl
          · simp only [Valuation.snoc_castSucc]
            exact agree old (fun same => different (congrArg Fin.castSucc same))
          · simp only [Valuation.snoc_last]
        · rw [value_snoc,value_snoc]
          intro same
          exact changed (nand_true_injective same)
      · refine ⟨Valuation.snoc (fun (_ : Fin (n + 1)) => false) false,Valuation.snoc (fun (_ : Fin (n + 1)) => false) true,?_,?_⟩
        · intro other different
          rcases index_cases other with ⟨old,rfl⟩ | rfl
          · simp only [Valuation.snoc_castSucc]
          · exact False.elim (different rfl)
        · rw [value_snoc,value_snoc,value_false]
          change true ≠ false
          exact Bool.noConfusion

private theorem swap_snoc {width : Nat} (left right : Fin width)
    (input : Valuation width) (last : Bool) :
    inputSwap left.castSucc right.castSucc (input.snoc last) =
      (inputSwap left right input).snoc last := by
  funext index
  rcases index_cases index with ⟨old,rfl⟩ | rfl
  · have leftEq : old.castSucc = left.castSucc ↔ old = left :=
      ⟨fun same => Fin.ext (congrArg (fun index : Fin (width + 1) => index.val) same),congrArg Fin.castSucc⟩
    have rightEq : old.castSucc = right.castSucc ↔ old = right :=
      ⟨fun same => Fin.ext (congrArg (fun index : Fin (width + 1) => index.val) same),congrArg Fin.castSucc⟩
    simp only [inputSwap,leftEq,rightEq,Valuation.snoc_castSucc]
  · rw [inputSwap_other _ _ _ _ (Ne.symm (cast_not_last left))
        (Ne.symm (cast_not_last right)),Valuation.snoc_last,Valuation.snoc_last]

private theorem last_asymmetric (n : Nat) (earlier : Fin (n + 1)) :
    ∃ input, coreValue (n + 1) input ≠
      coreValue (n + 1) (inputSwap earlier.castSucc (Fin.last (n + 1)) input) := by
  let input : Valuation (n + 2) :=
    Valuation.snoc (fun index : Fin (n + 1) => if index = earlier then true else false) false
  have swapped : inputSwap earlier.castSucc (Fin.last (n + 1)) input =
      Valuation.snoc (fun (_ : Fin (n + 1)) => false) true := by
    funext index
    rcases index_cases index with ⟨old,rfl⟩ | rfl
    · by_cases same : old = earlier
      · subst old
        rw [inputSwap_left]
        dsimp only [input]
        rw [Valuation.snoc_last,Valuation.snoc_castSucc]
      · have other : old.castSucc ≠ earlier.castSucc :=
          fun equal => same (Fin.ext (congrArg (fun index : Fin (n + 2) => index.val) equal))
        rw [inputSwap_other _ _ _ _ other (cast_not_last old)]
        dsimp only [input]
        rw [Valuation.snoc_castSucc,Valuation.snoc_castSucc,if_neg same]
    · rw [inputSwap_right _ _ _ (cast_not_last earlier)]
      dsimp only [input]
      rw [Valuation.snoc_castSucc,Valuation.snoc_last,if_pos rfl]
  have first : coreValue (n + 1) input = true := by
    change coreValue (n + 1)
      (Valuation.snoc (fun index : Fin (n + 1) => if index = earlier then true else false) false) = true
    rw [value_snoc]
    cases coreValue n (fun index => if index = earlier then true else false) <;> rfl
  have second : coreValue (n + 1)
      (inputSwap earlier.castSucc (Fin.last (n + 1)) input) = false := by
    rw [swapped,value_snoc,value_false]
    rfl
  refine ⟨input,?_⟩
  rw [first,second]
  exact Bool.noConfusion

/-- No two distinct inputs of the signed spine can be interchanged universally. -/
theorem value_asymmetric (n : Nat) (left right : Fin (n + 1)) (different : left ≠ right) :
    ∃ input, coreValue n input ≠ coreValue n (inputSwap left right input) := by
  induction n with
  | zero =>
      exfalso
      apply different
      apply Fin.ext
      have l := left.isLt
      have r := right.isLt
      omega
  | succ n ih =>
      rcases index_cases left with ⟨oldLeft,rfl⟩ | rfl
      · rcases index_cases right with ⟨oldRight,rfl⟩ | rfl
        · have oldDifferent : oldLeft ≠ oldRight :=
            fun same => different (congrArg Fin.castSucc same)
          obtain ⟨input,changed⟩ := ih oldLeft oldRight oldDifferent
          refine ⟨input.snoc true,?_⟩
          rw [swap_snoc,value_snoc,value_snoc]
          intro same
          exact changed (nand_true_injective same)
        · exact last_asymmetric n oldLeft
      · rcases index_cases right with ⟨oldRight,rfl⟩ | rfl
        · obtain ⟨input,changed⟩ := last_asymmetric n oldRight
          refine ⟨input,?_⟩
          rw [inputSwap_comm (Fin.last (n + 1)) oldRight.castSucc]
          exact changed
        · exact False.elim (different rfl)

/-- The actual initial spine, before adding the final reused guard. -/
def candidate (n : Nat) : Candidate (n + 1) (n + 1) 1 :=
  Candidate.ofDirectWireWord (core n).1 ⟨fun _ => (core n).2⟩

theorem candidate_value (n : Nat) (input : Valuation (n + 1)) (output : Fin 1) :
    (candidate n).semantics input output = coreValue n input := by
  unfold candidate
  rw [Candidate.ofDirectWireWord_semantics]
  exact core_value n input

/-- Exact physical-gate lower bound against arbitrary competing programs. -/
theorem minimum_bound (n gates : Nat) (program : Program (n + 1) gates)
    (source : Source (n + 1) gates)
    (equivalent : ∀ input, source.eval input (program.eval input) = coreValue n input) :
    n + 1 ≤ gates := by
  have essential : ∀ index, Essential (fun input => source.eval input (program.eval input)) index := by
    intro index
    obtain ⟨left,right,agree,changed⟩ := value_essential n index
    refine ⟨left,right,agree,?_⟩
    intro same
    exact changed ((equivalent left).symm.trans (same.trans (equivalent right)))
  have lower := all_essential_bound program source essential
  by_cases sufficient : n + 1 ≤ gates
  · exact sufficient
  · exfalso
    have size : gates = n := by omega
    subst gates
    cases n with
    | zero =>
        cases program
        cases source with
        | input index =>
            have impossible := equivalent (fun _ => false)
            change false = true at impossible
            exact Bool.noConfusion impossible
        | constant bit =>
            cases bit with
            | false =>
                have impossible := equivalent (fun _ => false)
                change false = true at impossible
                exact Bool.noConfusion impossible
            | true =>
                have impossible := equivalent (fun _ => true)
                change true = false at impossible
                exact Bool.noConfusion impossible
        | gate index => exact Fin.elim0 index
    | succ n =>
        obtain ⟨left,right,different,preserved⟩ :=
          essential_tight_symmetry program source (Nat.zero_lt_succ n) essential rfl
        obtain ⟨input,changed⟩ := value_asymmetric (n + 1) left right different
        exact changed ((equivalent input).symm.trans
          ((preserved input).trans (equivalent (inputSwap left right input))))

theorem minimum (n : Nat) : IsSemanticallyMinimum (candidate n).toImplementation := by
  intro gates other equivalent
  exact minimum_bound n gates other.program (other.directWireWord.source 0)
    (fun input => (equivalent input 0).trans (candidate_value n input 0))

/-- Reference-minimum agreement is proved without evaluating that reference. -/
theorem exact_reference_minimum (n : Nat) :
    referenceMinimum (candidate n).toImplementation = n + 1 := by
  apply Nat.le_antisymm (referenceMinimum_le_target (candidate n).toImplementation)
  exact minimum n (referenceMinimumWitness (candidate n).toImplementation)
    (equivalentBool_sound (referenceMinimumWitness_equivalent (candidate n).toImplementation))

theorem zero_slack (n : Nat) : residualSlack (candidate n).toImplementation = 0 :=
  (residualSlack_eq_zero_iff_minimum (candidate n).toImplementation).2 (minimum n)

theorem no_smaller_equivalent (n gates : Nat) (other : Candidate (n + 1) gates 1)
    (equivalent : Equivalent other.program other.directWireWord
      (candidate n).program (candidate n).directWireWord) : ¬gates < n + 1 :=
  Nat.not_lt_of_le (minimum n other equivalent)

end PNP.DirectWire.GuardedSpineMinimum
