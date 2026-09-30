import PNP.NANDCompleteBoundedWindowSearch
import PNP.NANDComposition

set_option autoImplicit false
set_option Elab.async false

/-! A source-derived guarded chain with a uniform two-gate saving.
This constructs the strict-gain family for the bounded-window coverage
investigation. It does not prove local silence for arbitrary window sizes. -/

namespace PNP.DirectWire.GuardedSpineFamily

def core : (n : Nat) → Program (n + 1) (n + 1) × Source (n + 1) (n + 1)
  | 0 => ⟨.snoc .empty ⟨.input 0, .input 0⟩, .gate 0⟩
  | n + 1 =>
      let prior := core n
      ⟨.snoc (prior.1.renameInputs Fin.castSucc)
        ⟨prior.2.renameInputs Fin.castSucc, .input (Fin.last (n + 1))⟩,
        .gate (Fin.last (n + 1))⟩

def candidate (n : Nat) : Candidate (n + 1) (n + 2) 1 :=
  Candidate.ofDirectWireWord
    (.snoc (core n).1 ⟨.input 0, (core n).2⟩)
    ⟨fun _ => .gate (Fin.last (n + 1))⟩

def shortCore : (n : Nat) → Program (n + 3) (n + 1) × Source (n + 3) (n + 1)
  | 0 => ⟨.snoc .empty ⟨.input 2, .input 2⟩, .gate 0⟩
  | n + 1 =>
      let prior := shortCore n
      ⟨.snoc (prior.1.renameInputs Fin.castSucc)
        ⟨prior.2.renameInputs Fin.castSucc, .input (Fin.last (n + 3))⟩,
        .gate (Fin.last (n + 1))⟩

def shorter (n : Nat) : Candidate (n + 3) (n + 2) 1 :=
  Candidate.ofDirectWireWord
    (.snoc (shortCore n).1 ⟨.input 0, (shortCore n).2⟩)
    ⟨fun _ => .gate (Fin.last (n + 1))⟩

def coreValue : (n : Nat) → Valuation (n + 1) → Bool
  | 0, input => boolNand (input 0) (input 0)
  | n + 1, input => boolNand
      (coreValue n (fun index => input index.castSucc))
      (input (Fin.last (n + 1)))

def shortValue : (n : Nat) → Valuation (n + 3) → Bool
  | 0, input => boolNand (input 2) (input 2)
  | n + 1, input => boolNand
      (shortValue n (fun index => input index.castSucc))
      (input (Fin.last (n + 3)))

private theorem renamed_value {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates) (source : Source fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs) (input : Valuation toInputs) :
    (source.renameInputs rename).eval input ((program.renameInputs rename).eval input) =
      source.eval (fun index => input (rename index))
        (program.eval (fun index => input (rename index))) := by
  rw [Source.eval_renameInputs]
  exact source.eval_congr (fun _ => rfl)
    (fun index => Program.eval_renameInputs program rename input index)

theorem core_value (n : Nat) (input : Valuation (n + 1)) :
    (core n).2.eval input ((core n).1.eval input) = coreValue n input := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (Program.snoc ((core n).1.renameInputs Fin.castSucc)
        ⟨(core n).2.renameInputs Fin.castSucc, .input (Fin.last (n + 1))⟩).eval
          input (Fin.last (n + 1)) = _
      rw [Program.eval_snoc_last]
      change boolNand (((core n).2.renameInputs Fin.castSucc).eval input
        (((core n).1.renameInputs Fin.castSucc).eval input))
        (input (Fin.last (n + 1))) = _
      rw [renamed_value, ih]
      rfl

theorem short_core_value (n : Nat) (input : Valuation (n + 3)) :
    (shortCore n).2.eval input ((shortCore n).1.eval input) = shortValue n input := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (Program.snoc ((shortCore n).1.renameInputs Fin.castSucc)
        ⟨(shortCore n).2.renameInputs Fin.castSucc, .input (Fin.last (n + 3))⟩).eval
          input (Fin.last (n + 1)) = _
      rw [Program.eval_snoc_last]
      change boolNand (((shortCore n).2.renameInputs Fin.castSucc).eval input
        (((shortCore n).1.renameInputs Fin.castSucc).eval input))
        (input (Fin.last (n + 3))) = _
      rw [renamed_value, ih]
      rfl

theorem candidate_value (n : Nat) (input : Valuation (n + 1)) (output : Fin 1) :
    (candidate n).semantics input output = boolNand (input 0) (coreValue n input) := by
  unfold candidate
  rw [Candidate.ofDirectWireWord_semantics]
  change (Program.snoc (core n).1 ⟨.input 0, (core n).2⟩).eval
    input (Fin.last (n + 1)) = _
  rw [Program.eval_snoc_last]
  change boolNand (input 0) ((core n).2.eval input ((core n).1.eval input)) = _
  rw [core_value]

theorem shorter_value (n : Nat) (input : Valuation (n + 3)) (output : Fin 1) :
    (shorter n).semantics input output = boolNand (input 0) (shortValue n input) := by
  unfold shorter
  rw [Candidate.ofDirectWireWord_semantics]
  change (Program.snoc (shortCore n).1 ⟨.input 0, (shortCore n).2⟩).eval
    input (Fin.last (n + 1)) = _
  rw [Program.eval_snoc_last]
  change boolNand (input 0) ((shortCore n).2.eval input ((shortCore n).1.eval input)) = _
  rw [short_core_value]

/-- The two early gates cancel only in the true-guard cofactor. -/
theorem true_cofactor (n : Nat) (input : Valuation (n + 3)) (guard : input 0 = true) :
    coreValue (n + 2) input = shortValue n input := by
  induction n with
  | zero =>
      change boolNand (boolNand (boolNand (input 0) (input 0)) (input 1))
        (input 2) = boolNand (input 2) (input 2)
      rw [guard]
      cases input 1 <;> cases input 2 <;> rfl
  | succ n ih =>
      change boolNand (coreValue (n + 2) (fun index => input index.castSucc))
        (input (Fin.last (n + 3))) =
          boolNand (shortValue n (fun index => input index.castSucc))
            (input (Fin.last (n + 3)))
      rw [ih (fun index => input index.castSucc) guard]

/-- Ordinary semantics for every valuation and every chain length. -/
theorem equivalent (n : Nat) :
    Equivalent (shorter n).program (shorter n).directWireWord
      (candidate (n + 2)).program (candidate (n + 2)).directWireWord := by
  intro input output
  change (shorter n).semantics input output = (candidate (n + 2)).semantics input output
  rw [shorter_value, candidate_value]
  cases guard : input 0 with
  | false => rfl
  | true => rw [true_cofactor n input guard]

theorem strict_gain (n : Nat) :
    StrictEquivalentGain (candidate (n + 2)).toImplementation (shorter n).toImplementation := by
  constructor
  · change n + 2 < (n + 2) + 2
    omega
  · exact equivalent n

theorem residual_positive (n : Nat) :
    0 < residualSlack (candidate (n + 2)).toImplementation :=
  Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack (shorter n).toImplementation))
    (strict_gain n).strictResidualDescent

end PNP.DirectWire.GuardedSpineFamily
