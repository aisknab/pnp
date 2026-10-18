import PNP.Concrete.ResidualReduction.SourceAffineOutputInstructions

/-! The complete prepared affine-search program now returns the canonical
optional witness bytes. Valid indices are derived from the search itself;
no candidate, successful activity or output bytes are supplied as premises.
The raw-input preparation and solver handoff remain distinct pending phases. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineOutput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear

theorem unitSearch_mode {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (count i : Nat) :
    (SourceAffineSearch.unitSearch F forms count i).unitParameter = true := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    cases found : (SourceAffineSearch.unitResult F forms i).2 <;>
      simp only [SourceAffineSearch.unitSearch, found, Bool.false_eq_true, if_false, if_true]
    · exact ih (i + 1)

theorem zero_parameter_index {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (zero : (SourceAffineSearch.outcome F forms).unitParameter = false) :
    (SourceAffineSearch.outcome F forms).parameterIndex = 0 := by
  cases found : (SourceAffineSearch.zeroResult F forms).2 with
  | false =>
    have mode := unitSearch_mode F forms k 0
    simp only [SourceAffineSearch.outcome, found, Bool.false_eq_true, if_false] at zero
    rw [zero] at mode
    cases mode
  | true => simp only [SourceAffineSearch.outcome, found, if_true]

theorem successful_selection {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (found : (SourceAffineSearch.outcome F forms).found = true) :
    ∃ q : Option (Fin k), ∃ j : Fin n, SourceAffineSearch.outcome F forms =
      ⟨q.isSome, SourceCandidateMapInstructions.cursor q, j.val, true⟩ := by
  let r := SourceAffineSearch.outcome F forms
  have accepted : (SourceAffineSearch.decode F forms r).isSome = true :=
    (SourceAffineSearch.outcome_isSome F forms).trans found
  have eta : r = ⟨r.unitParameter, r.parameterIndex, r.directionIndex, r.found⟩ := rfl
  change r.found = true at found
  cases mode : r.unitParameter with
  | false =>
    have index : r.parameterIndex = 0 := zero_parameter_index F forms mode
    have inside : r.directionIndex < n := by
      by_cases h : r.directionIndex < n
      · exact h
      · simp only [SourceAffineSearch.decode, mode, Bool.false_eq_true, if_false,
          SourceAffineSearch.directionWitness, found, if_true, dif_neg h, Option.isSome] at accepted
    refine ⟨none, ⟨r.directionIndex, inside⟩, ?_⟩
    rw [mode, index, found] at eta
    exact eta
  | true =>
    have parameter : r.parameterIndex < k := by
      by_cases h : r.parameterIndex < k
      · exact h
      · simp only [SourceAffineSearch.decode, mode, if_true, dif_neg h, Option.isSome] at accepted
        cases accepted
    have inside : r.directionIndex < n := by
      by_cases h : r.directionIndex < n
      · exact h
      · simp only [SourceAffineSearch.decode, mode, if_true, dif_pos parameter,
          SourceAffineSearch.directionWitness, found, dif_neg h, Option.isSome] at accepted
        cases accepted
    refine ⟨some ⟨r.parameterIndex, parameter⟩, ⟨r.directionIndex, inside⟩, ?_⟩
    rw [mode, found] at eta
    exact eta

theorem decode_selected {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Fin n) :
    SourceAffineSearch.decode F forms ⟨q.isSome, SourceCandidateMapInstructions.cursor q, j.val, true⟩ =
      some (mapEval forms (SourceCandidateMapInstructions.parameter q), unitPoint n j) := by
  cases q with
  | none => simp only [SourceAffineSearch.decode, Option.isSome, SourceCandidateMapInstructions.cursor,
      Bool.false_eq_true, if_false, SourceAffineSearch.directionWitness, if_true, dif_pos j.isLt]
  | some i => simp only [SourceAffineSearch.decode, Option.isSome, SourceCandidateMapInstructions.cursor,
      if_true, dif_pos i.isLt, SourceAffineSearch.directionWitness, dif_pos j.isLt]

def emit : Block 22 := .branch 8 .skip .skip success
def outputBudget (n k rows : Nat) : Nat := (9 * k + 29) * rows + 8 * n + 13

theorem emit_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    ∃ used after, Exec emit (SourceAffineSearch.finished F forms (SourceAffineSearch.outcome F forms)).store used after ∧
      after.get 8 = (witnessCodec F.length n).encode (SourceAffineSearch.decode F forms (SourceAffineSearch.outcome F forms)) ∧
      used ≤ outputBudget n k F.length := by
  cases found : (SourceAffineSearch.outcome F forms).found with
  | false =>
    let before := SourceAffineSearch.finished F forms (SourceAffineSearch.outcome F forms)
    have flag : before.store.get 8 = [false] := by
      change [(SourceAffineSearch.outcome F forms).found] = [false]
      rw [found]
    have checked : Exec emit before.store 2 before.store := Exec.zero (source := (8 : Fin 22)) flag (.skip _)
    have missing : SourceAffineSearch.decode F forms (SourceAffineSearch.outcome F forms) = none := by
      have present := SourceAffineSearch.outcome_isSome F forms
      rw [found] at present
      cases value : SourceAffineSearch.decode F forms (SourceAffineSearch.outcome F forms) with
      | none => rfl
      | some w => rw [value] at present; cases present
    refine ⟨2, before.store, checked, ?_, ?_⟩
    · rw [flag, missing]; rfl
    · unfold outputBudget; omega
  | true =>
    obtain ⟨q, j, selected⟩ := successful_selection F forms found
    have checked : Exec emit (holder F forms q j.val).store (1 + successFuel n k F.length q j.val)
        (result F forms q j).store := Exec.one (source := (8 : Fin 22)) rfl (success_exec F forms q j)
    have input : (SourceAffineSearch.finished F forms (SourceAffineSearch.outcome F forms)).store =
        (holder F forms q j.val).store := by rw [selected]; rfl
    refine ⟨1 + successFuel n k F.length q j.val, (result F forms q j).store, ?_, ?_, ?_⟩
    · rw [input]; exact checked
    · rw [selected, decode_selected]; rfl
    · have bound := successFuel_bound F q j
      unfold outputBudget
      omega

def query : Block 22 := .seq SourceAffineSearch.block emit

theorem query_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    ∃ used after, Exec query (SourceAffineSearch.ready F forms false 0 0 n 0 false).store used after ∧
      after.get 8 = (witnessCodec F.length n).encode (SourceAffineSearch.decode F forms (SourceAffineSearch.outcome F forms)) ∧
      used ≤ SourceAffineSearch.fuel F forms + outputBudget n k F.length := by
  obtain ⟨used, after, emitted, bytes, bound⟩ := emit_exec F forms
  refine ⟨SourceAffineSearch.fuel F forms + used, after, Exec.seq (SourceAffineSearch.block_exec F forms) emitted, bytes, ?_⟩
  exact Nat.add_le_add_left bound _

theorem outputBudget_mono (n k rows N K R : Nat) (hn : n ≤ N) (hk : k ≤ K) (hr : rows ≤ R) :
    outputBudget n k rows ≤ outputBudget N K R := by
  have factor : 9 * k + 29 ≤ 9 * K + 29 := by omega
  have product := Nat.mul_le_mul factor hr
  unfold outputBudget
  omega

def originalInputBudget (L : Nat) : Nat :=
  (SourceAffineSearch.directionBudget L L L + 7) * (L + 1) + outputBudget L L L

/-- Full search and returned bytes, but still starting from the prepared store.
The equality premise identifies the actual solver branch; it supplies neither
activity nor a successful witness. Raw input and map handoff are not free. -/
theorem computed_query_exec {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    ∃ used after, Exec query (SourceAffineSearch.ready F s.forms false 0 0 n 0 false).store used after ∧
      after.get 8 = (witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) ∧
      used ≤ originalInputBudget (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length := by
  obtain ⟨used, after, execution, bytes, bound⟩ := query_exec F s.forms
  rw [SourceAffineSearch.computed_query_exact F s computed] at bytes
  refine ⟨used, after, execution, bytes, ?_⟩
  let L := (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length
  have search := SourceAffineSearch.original_input_fuel_bound F s computed
  have hn := SourceMatrixEncoding.dimension_bound n F
  have hm := SourceMatrixEncoding.rowCount_bound n F
  have hk := solve_some_parameter_bound (SourceClosure.affineMaskRows F) s computed
  have output := outputBudget_mono n s.parameters F.length L L L hn (Nat.le_trans hk hm) hm
  exact Nat.le_trans bound (Nat.add_le_add search output)

theorem witness_bytes_bound (rows n : Nat) (value : Option (Point rows × Point n)) :
    ((witnessCodec rows n).encode value).length ≤ rows + n + 1 := by
  cases value with
  | none => change 1 ≤ rows + n + 1; omega
  | some pair =>
    change (true :: ((SourceEncoding.pointCodec rows).encode pair.1 ++
      (SourceEncoding.pointCodec n).encode pair.2)).length ≤ rows + n + 1
    simp only [List.length_cons, List.length_append, SourceEncoding.point_length]
    exact Nat.le_refl _

end PNP.Concrete.ResidualReduction.SourceAffineOutput
