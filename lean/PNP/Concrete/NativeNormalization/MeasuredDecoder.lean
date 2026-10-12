import PNP.Concrete.NativeNormalization.MeasuredDecoderTokens

namespace PNP.Concrete.NativeNormalization.MeasuredDecoder

open PNP.Concrete MeasuredReach MeasuredDecoderTokens

def header : Nat → List CNFToken → Measured (Option CNFFormula)
  | _,[] => ⟨none,1⟩
  | count,.f::rest =>
      let tail := clauses rest
      ⟨tail.value.map (fun cs => ⟨count,cs⟩),tail.cost+4⟩
  | count,.t::rest =>
      let tail := header (count+1) rest
      ⟨tail.value,tail.cost+3⟩
  | _,.sep::_ => ⟨none,2⟩
  | _,.finish::_ => ⟨none,2⟩

theorem header_value (count : Nat) (tokens : List CNFToken) :
    (header count tokens).value = decodeFormulaHeader count tokens := by
  induction tokens generalizing count with
  | nil => rfl
  | cons token rest ih =>
      cases token with
      | f =>
          change (clauses rest).value.map _ = _
          rw [clauses_value]
          simp only [decodeFormulaHeader]
          cases decodeFormulaClauses rest <;> rfl
      | t => exact ih (count+1)
      | sep => rfl
      | finish => rfl

theorem header_cost (count : Nat) (tokens : List CNFToken) :
    (header count tokens).cost ≤ 6*tokens.length+1 := by
  induction tokens generalizing count with
  | nil => exact Nat.le_refl _
  | cons token rest ih =>
      have hc := clauses_cost rest
      have ht := ih (count+1)
      cases token <;> simp only [header,List.length_cons] <;> omega

/-- Materialize tokens once, then parse the exact strict grammar. Rejection after
token decoding is charged too; no valid-input premise restricts this function. -/
def decode (bits : BitString) : Measured (Option CNFFormula) :=
  let parsed := pairs bits
  match parsed.value with
  | none => ⟨none,parsed.cost+1⟩
  | some tokens =>
      let result := header 0 tokens
      ⟨result.value,parsed.cost+result.cost+1⟩

theorem decode_value (bits : BitString) : (decode bits).value = decodeEncodedCNF bits := by
  cases hp : (pairs bits).value with
  | none =>
      simp only [decode,decodeEncodedCNF,← pairs_value bits,hp]
  | some tokens =>
      simp only [decode,decodeEncodedCNF,← pairs_value bits,hp,header_value,decodeCNFTokens]

theorem decode_cost (bits : BitString) : (decode bits).cost ≤ 5*bits.length+4 := by
  have hp := pairs_cost bits
  cases he : (pairs bits).value with
  | none =>
      simp only [decode,he]
      omega
  | some tokens =>
      have hl := pairs_length bits tokens he
      have hh := header_cost 0 tokens
      simp only [decode,he]
      omega

def workPolynomial : NatPolynomial :=
  .add (.mul (.constant 5) .variable) (.constant 4)

theorem workPolynomial_eval (m : Nat) : workPolynomial.eval m = 5*m+4 := rfl

theorem decode_polynomial (bits : BitString) :
    (decode bits).cost ≤ workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact decode_cost bits

/-- A source word/list-operation bound only. Concrete representation, arithmetic
and machine refinement remain separate obligations. -/
theorem decode_verified (bits : BitString) :
    (decode bits).value = decodeEncodedCNF bits ∧
      (decode bits).cost ≤ workPolynomial.eval bits.length :=
  ⟨decode_value bits,decode_polynomial bits⟩

theorem decode_canonical (F : CNFFormula) :
    (decode (encodeCNF F)).value = some F :=
  (decode_value _).trans (decodeEncodedCNF_canonical F)


end PNP.Concrete.NativeNormalization.MeasuredDecoder
