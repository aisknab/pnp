import PNP.ClauseSquare.Size
import PNP.Concrete.CNFDecoderGrammar

set_option autoImplicit false
namespace PNP.ClauseSquare.EncodedCost
open PNP.Concrete PNP.ClauseSquare

/-- Retain the source cost even of occurrences subsequently omitted as out of range. -/
def allOccurrences : List (List CNFLiteral) → Nat
  | [] => 0
  | c::cs => c.length + allOccurrences cs

def rowIndexSum : List CNFLiteral → Nat
  | [] => 0
  | l::ls => l.variableIndex+rowIndexSum ls

def indexSum : List (List CNFLiteral) → Nat
  | [] => 0
  | c::cs => rowIndexSum c+indexSum cs

theorem used_le_length (n : Nat) (c : List CNFLiteral) : used n c ≤ c.length := by
  induction c with
  | nil => exact Nat.le_refl 0
  | cons l ls ih =>
    rw [used,List.length_cons]; split <;> omega

theorem retained_le_all (n : Nat) (cs : List (List CNFLiteral)) :
    literalOccurrences n cs ≤ allOccurrences cs := by
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c cs ih => exact Nat.add_le_add (used_le_length n c) ih

theorem unary_length (n : Nat) : (encodeUnaryTokens n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [encodeUnaryTokens,List.length_cons,ih]

theorem single_literal_length (l : CNFLiteral) : (encodeLiteralTokens l).length=l.variableIndex+2 := by
  rw [encodeLiteralTokens,List.length_cons,unary_length]

theorem literals_tokens_length (c : List CNFLiteral) :
    (encodeLiteralListTokens c).length=2*c.length+rowIndexSum c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    rw [encodeLiteralListTokens,List.length_append,single_literal_length,ih,List.length_cons,rowIndexSum]
    omega

theorem clause_tokens_length (c : List CNFLiteral) :
    (encodeClauseTokens c).length=2+2*c.length+rowIndexSum c := by
  rw [encodeClauseTokens,List.length_cons,List.length_append,literals_tokens_length]
  simp only [List.length_cons,List.length_nil]; omega

theorem clauses_tokens_length (cs : List (List CNFLiteral)) :
    (encodeClauseListTokens cs).length=2*cs.length+2*allOccurrences cs+indexSum cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [encodeClauseListTokens,List.length_append,clause_tokens_length,ih,List.length_cons,allOccurrences,indexSum]
    omega

/-- Width unary, two delimiters per clause, sign and at least one index-token per
literal, two bits per token, and a single final pad bit. -/
theorem canonical_length (F : CNFFormula) : (encodeCNF F).length =
    2*F.variableCount+5+4*F.clauses.length+4*allOccurrences F.clauses+2*indexSum F.clauses := by
  rw [encodeCNF,List.length_append,encodeTokenPairs_length,encodeCNFTokens,List.length_append,
    List.length_append,unary_length,clauses_tokens_length]
  simp only [List.length_cons,List.length_nil]; omega

theorem accepted_length (bits : BitString) (F : CNFFormula)
    (hd : decodeEncodedCNF bits=some F) : bits.length =
    2*F.variableCount+5+4*F.clauses.length+4*allOccurrences F.clauses+2*indexSum F.clauses := by
  rw [← CNFRegisterDecoder.encoded_of_decode bits F hd]
  exact canonical_length F

theorem accepted_joint (bits : BitString) (F : CNFFormula) (hd : decodeEncodedCNF bits=some F) :
    2*(compile bits).n + 4*(compile bits).d ≤ bits.length+3 := by
  have hl := accepted_length bits F hd
  have hret := retained_le_all F.variableCount F.clauses
  rw [compile,hd,exact_dimension]
  change 2*F.variableCount + 4*(2 + F.clauses.length + literalOccurrences _ _) ≤ _
  omega

/-- Even an empty malformed word still produces the one-bit identity matrix. -/
theorem malformed_shape (bits : BitString) (hd : decodeEncodedCNF bits=none) :
    (compile bits).n=0 ∧ (compile bits).d=1 := by
  rw [compile,hd]; exact ⟨rfl,rfl⟩

theorem all_input_axes (bits : BitString) : (compile bits).n ≤ bits.length ∧
    (compile bits).d ≤ bits.length+1 := by
  cases hd : decodeEncodedCNF bits with
  | none =>
    obtain ⟨hn,he⟩ := malformed_shape bits hd
    rw [hn,he]; exact ⟨Nat.zero_le _,Nat.succ_le_succ (Nat.zero_le _)⟩
  | some F =>
    have kj := accepted_joint bits F hd
    have hl := accepted_length bits F hd
    have hn : (compile bits).n=F.variableCount := by rw [compile,hd]; rfl
    constructor
    · rw [hn]; omega
    · omega

end PNP.ClauseSquare.EncodedCost
