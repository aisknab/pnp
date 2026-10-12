import PNP.Concrete.NativeNormalization.MeasuredReach
import PNP.Concrete.CNF

namespace PNP.Concrete.NativeNormalization.MeasuredDecoderTokens

open PNP.Concrete MeasuredReach

/-- Exact strict token-pair decoding. Charges cover pair inspection, token and list
construction, and option dispatch; no suffix scan or allocation is free. -/
def pairs : BitString → Measured (Option (List CNFToken))
  | [] => ⟨none,1⟩
  | [b] => ⟨if b then none else some [],2⟩
  | a::b::rest =>
      let tail := pairs rest
      ⟨tail.value.map (fun ts => CNFToken.ofBits a b::ts),tail.cost+4⟩

theorem pairs_value : ∀ bits : BitString, (pairs bits).value = decodeFormulaTokenPairs bits
  | [] => rfl
  | [b] => by cases b <;> rfl
  | a::b::rest => by
      simp only [pairs,pairs_value rest,decodeFormulaTokenPairs]
      cases decodeFormulaTokenPairs rest <;> rfl

theorem pairs_cost : ∀ bits : BitString, (pairs bits).cost ≤ 2*bits.length+2
  | [] => by decide
  | [b] => by simp only [pairs,List.length_cons,List.length_nil]; omega
  | a::b::rest => by
      have ih := pairs_cost rest
      simp only [pairs,List.length_cons]
      omega

theorem pairs_length : (bits : BitString) → (tokens : List CNFToken) →
    (pairs bits).value = some tokens → 2*tokens.length+1 = bits.length
  | [],_,h => by cases h
  | [false],_,h => by cases h; rfl
  | [true],_,h => by cases h
  | a::b::rest,tokens,h => by
      cases ht : (pairs rest).value with
      | none => simp only [pairs,ht,Option.map_none] at h; cases h
      | some ts =>
          have he : CNFToken.ofBits a b::ts = tokens := by
            simpa only [pairs,ht,Option.map_some,Option.some.injEq] using h
          subst tokens
          have ih := pairs_length rest ts ht
          simp only [List.length_cons]
          omega

/- Fixed per-state charges include the small constructors on successful returns.
The same conservative charge is retained when an option returns no value. -/
mutual
  def clauses : List CNFToken → Measured (Option (List (List CNFLiteral)))
    | [] => ⟨none,1⟩
    | .f::_ => ⟨none,2⟩
    | .t::_ => ⟨none,2⟩
    | .sep::rest =>
        let tail := clause rest
        ⟨tail.value.map (fun p => p.1::p.2),tail.cost+4⟩
    | .finish::rest => ⟨if rest.isEmpty then some [] else none,3⟩

  def clause : List CNFToken →
      Measured (Option (List CNFLiteral × List (List CNFLiteral)))
    | [] => ⟨none,1⟩
    | .f::rest =>
        let tail := literal false 0 rest
        ⟨tail.value,tail.cost+2⟩
    | .t::rest =>
        let tail := literal true 0 rest
        ⟨tail.value,tail.cost+2⟩
    | .sep::_ => ⟨none,2⟩
    | .finish::rest =>
        let tail := clauses rest
        ⟨tail.value.map (fun cs => ([],cs)),tail.cost+4⟩

  def literal (positive : Bool) (index : Nat) : List CNFToken →
      Measured (Option (List CNFLiteral × List (List CNFLiteral)))
    | [] => ⟨none,1⟩
    | .f::rest =>
        let tail := clause rest
        ⟨tail.value.map (fun p => (⟨positive,index⟩::p.1,p.2)),tail.cost+6⟩
    | .t::rest =>
        let tail := literal positive (index+1) rest
        ⟨tail.value,tail.cost+3⟩
    | .sep::_ => ⟨none,2⟩
    | .finish::_ => ⟨none,2⟩
end

private theorem suffix_values (tokens : List CNFToken) :
    (clauses tokens).value = decodeFormulaClauses tokens ∧
    (clause tokens).value = decodeFormulaClause tokens ∧
    (∀ positive index, (literal positive index tokens).value =
      decodeFormulaLiteral positive index tokens) := by
  induction tokens with
  | nil => exact ⟨rfl,rfl,fun _ _ => rfl⟩
  | cons token rest ih =>
      rcases ih with ⟨hcs,hcl,hl⟩
      constructor
      · cases token with
        | f => rfl
        | t => rfl
        | sep =>
            change (clause rest).value.map _ = _
            rw [hcl]
            simp only [decodeFormulaClauses]
            cases decodeFormulaClause rest <;> rfl
        | finish => cases rest <;> rfl
      · constructor
        · cases token with
          | f => exact hl false 0
          | t => exact hl true 0
          | sep => rfl
          | finish =>
              change (clauses rest).value.map _ = _
              rw [hcs]
              simp only [decodeFormulaClause]
              cases decodeFormulaClauses rest <;> rfl
        · intro positive index
          cases token with
          | f =>
              change (clause rest).value.map _ = _
              rw [hcl]
              simp only [decodeFormulaLiteral]
              cases decodeFormulaClause rest <;> rfl
          | t => exact hl positive (index+1)
          | sep => rfl
          | finish => rfl

theorem clauses_value (tokens : List CNFToken) :
    (clauses tokens).value = decodeFormulaClauses tokens := (suffix_values tokens).1

theorem clause_value (tokens : List CNFToken) :
    (clause tokens).value = decodeFormulaClause tokens := (suffix_values tokens).2.1

theorem literal_value (positive : Bool) (index : Nat) (tokens : List CNFToken) :
    (literal positive index tokens).value = decodeFormulaLiteral positive index tokens :=
  (suffix_values tokens).2.2 positive index

private theorem suffix_costs (tokens : List CNFToken) :
    (clauses tokens).cost ≤ 6*tokens.length+1 ∧
    (clause tokens).cost ≤ 6*tokens.length+1 ∧
    (∀ positive index, (literal positive index tokens).cost ≤ 6*tokens.length+1) := by
  induction tokens with
  | nil => exact ⟨Nat.le_refl _,Nat.le_refl _,fun _ _ => Nat.le_refl _⟩
  | cons token rest ih =>
      rcases ih with ⟨hcs,hcl,hl⟩
      refine ⟨?_,?_,?_⟩
      · cases token <;> simp only [clauses,List.length_cons] <;> omega
      · have hf := hl false 0
        have ht := hl true 0
        cases token <;> simp only [clause,List.length_cons] <;> omega
      · intro positive index
        have ht := hl positive (index+1)
        cases token <;> simp only [literal,List.length_cons] <;> omega

theorem clauses_cost (tokens : List CNFToken) :
    (clauses tokens).cost ≤ 6*tokens.length+1 := (suffix_costs tokens).1

theorem clause_cost (tokens : List CNFToken) :
    (clause tokens).cost ≤ 6*tokens.length+1 := (suffix_costs tokens).2.1

theorem literal_cost (positive : Bool) (index : Nat) (tokens : List CNFToken) :
    (literal positive index tokens).cost ≤ 6*tokens.length+1 :=
  (suffix_costs tokens).2.2 positive index


end PNP.Concrete.NativeNormalization.MeasuredDecoderTokens
