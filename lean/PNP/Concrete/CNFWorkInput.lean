/-
Copyright (c) 2026 PNP Labs.

The exact work-tape image of a canonically paired CNF formula and assignment
certificate.  This file is only an encoding bridge: it does not ask the work
machine to trust a decoded Lean value.
-/

import PNP.Concrete.CNF
import PNP.Concrete.WorkInput

namespace PNP.Concrete

namespace CNFToken

/-- Interpret a two-bit CNF token as the corresponding two-cell work symbol. -/
def workSymbol : CNFToken → WorkSymbol
  | .f => .zeroZero
  | .t => .oneOne
  | .sep => .zeroOne
  | .finish => .oneZero

theorem workSymbol_first_second (token : CNFToken) :
    token.workSymbol.first :: token.workSymbol.second :: [] =
      token.bits.map TapeSymbol.ofBool := by
  cases token <;> rfl

end CNFToken

/-- Work-symbol image of a complete token list. -/
def cnfTokenWorkSymbols : List CNFToken → List WorkSymbol
  | [] => []
  | token :: rest => token.workSymbol :: cnfTokenWorkSymbols rest

theorem encodeWorkRight_cnfTokenWorkSymbols (tokens : List CNFToken) :
    encodeWorkRight (cnfTokenWorkSymbols tokens) =
      (encodeTokenPairs tokens).map TapeSymbol.ofBool := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token with
      | f => exact congrArg (List.cons .zero ∘ List.cons .zero) ih
      | t => exact congrArg (List.cons .one ∘ List.cons .one) ih
      | sep => exact congrArg (List.cons .zero ∘ List.cons .one) ih
      | finish => exact congrArg (List.cons .one ∘ List.cons .zero) ih

theorem cnfTokenWorkSymbols_length (tokens : List CNFToken) :
    (cnfTokenWorkSymbols tokens).length = tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token rest ih => exact congrArg Nat.succ ih

theorem encodeTokenPairs_length (tokens : List CNFToken) :
    (encodeTokenPairs tokens).length = 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        change Nat.succ (Nat.succ (encodeTokenPairs rest).length) =
          Nat.succ (Nat.succ (2 * rest.length)) <;>
        exact congrArg Nat.succ (congrArg Nat.succ ih)

theorem encodeTokenPairs_append (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        change _ :: _ :: encodeTokenPairs (rest ++ right) =
          _ :: _ :: (encodeTokenPairs rest ++ encodeTokenPairs right) <;>
        exact congrArg (List.cons _) (congrArg (List.cons _) ih)

private theorem workSymbol_append_assoc {left middle right : List WorkSymbol} :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons symbol rest ih => exact congrArg (List.cons symbol) ih

private theorem tapeSymbol_append_assoc
    {left middle right : List TapeSymbol} :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons symbol rest ih => exact congrArg (List.cons symbol) ih

private theorem map_ofBool_append (left right : BitString) :
    (left ++ right).map TapeSymbol.ofBool =
      left.map TapeSymbol.ofBool ++ right.map TapeSymbol.ofBool := by
  induction left with
  | nil => rfl
  | cons bit rest ih => exact congrArg (List.cons (TapeSymbol.ofBool bit)) ih

private theorem map_ofBool_replicate_true (n : Nat) :
    (List.replicate n true).map TapeSymbol.ofBool =
      List.replicate n TapeSymbol.one := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons TapeSymbol.one) ih

private theorem replicate_one_succ_tail (n : Nat) :
    List.replicate (n + 1) TapeSymbol.one =
      List.replicate n TapeSymbol.one ++ [TapeSymbol.one] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change TapeSymbol.one :: List.replicate (n + 1) TapeSymbol.one =
        TapeSymbol.one :: (List.replicate n TapeSymbol.one ++ [TapeSymbol.one])
      exact congrArg (List.cons TapeSymbol.one) ih

private theorem replicate_one_add_two (n : Nat) :
    List.replicate (n + 2) TapeSymbol.one =
      List.replicate n TapeSymbol.one ++ [TapeSymbol.one, TapeSymbol.one] := by
  rw [show n + 2 = (n + 1) + 1 by rw [Nat.add_assoc]]
  rw [replicate_one_succ_tail, replicate_one_succ_tail]
  exact tapeSymbol_append_assoc

private theorem encodeWorkRight_replicate_true (n : Nat) :
    encodeWorkRight (List.replicate n WorkSymbol.oneOne) =
      List.replicate (2 * n) TapeSymbol.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change TapeSymbol.one :: TapeSymbol.one ::
          encodeWorkRight (List.replicate n WorkSymbol.oneOne) =
        List.replicate (2 * (n + 1)) TapeSymbol.one
      rw [ih, Nat.mul_add]
      rfl

/-- Odd raw formula word carried by the first canonical frame. -/
def paddedFormulaTokenBits (tokens : List CNFToken) : BitString :=
  encodeTokenPairs tokens ++ [false]

/-- Even raw certificate word carried by the second canonical frame. -/
def assignmentCertificateTokenBits (tokens : List CNFToken) : BitString :=
  encodeTokenPairs tokens ++ CNFToken.finish.bits

/-- Assignment tokens without the certificate's terminal `Finish`; separating
that token exposes the exact outer-frame alignment. -/
def assignmentValueTokens : BitString → List CNFToken
  | [] => []
  | value :: rest => assignmentToken value :: assignmentValueTokens rest

theorem assignmentValueTokens_length (assignment : BitString) :
    (assignmentValueTokens assignment).length = assignment.length := by
  induction assignment with
  | nil => rfl
  | cons value rest ih => exact congrArg Nat.succ ih

theorem encodeAssignmentTokens_eq_valueTokens (assignment : BitString) :
    encodeAssignmentTokens assignment =
      assignmentValueTokens assignment ++ [.finish] := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      change assignmentToken value :: encodeAssignmentTokens rest =
        assignmentToken value :: (assignmentValueTokens rest ++ [.finish])
      exact congrArg (List.cons (assignmentToken value)) ih

theorem paddedFormulaTokenBits_length (tokens : List CNFToken) :
    (paddedFormulaTokenBits tokens).length = 2 * tokens.length + 1 := by
  unfold paddedFormulaTokenBits
  rw [BitString.length_append_constructive, encodeTokenPairs_length]

theorem assignmentCertificateTokenBits_length (tokens : List CNFToken) :
    (assignmentCertificateTokenBits tokens).length =
      2 * tokens.length + 2 := by
  unfold assignmentCertificateTokenBits
  rw [BitString.length_append_constructive, encodeTokenPairs_length]
  rfl

theorem encodeFormula_eq_padded_tokens (formula : CNFFormula) :
    encodeFormula formula =
      paddedFormulaTokenBits (encodeFormulaTokens formula) := rfl

theorem encodeAssignmentCertificate_eq_token_bits (assignment : BitString) :
    encodeAssignmentCertificate assignment =
      assignmentCertificateTokenBits (assignmentValueTokens assignment) := by
  unfold encodeAssignmentCertificate assignmentCertificateTokenBits
  rw [encodeAssignmentTokens_eq_valueTokens]
  rw [encodeTokenPairs_append]
  rfl

/-- Exact packed layout of two canonical frames.  Formula strings have a
final zero pad, while certificate strings end in a complete `Finish` token;
the pad and the first bit of the second frame therefore form `Sep`. -/
def pairedTokenLayout (formulaTokens assignmentTokens : List CNFToken) :
    List WorkSymbol :=
  List.replicate formulaTokens.length WorkSymbol.oneOne ++
    WorkSymbol.oneZero ::
      (cnfTokenWorkSymbols formulaTokens ++
        WorkSymbol.zeroOne ::
          (List.replicate assignmentTokens.length WorkSymbol.oneOne ++
            WorkSymbol.oneZero ::
              (cnfTokenWorkSymbols assignmentTokens ++ [WorkSymbol.oneZero])))

private theorem encodeWorkRight_pairedTokenLayout_normalized
    (formulaTokens assignmentTokens : List CNFToken) :
    encodeWorkRight (pairedTokenLayout formulaTokens assignmentTokens) =
      List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
        TapeSymbol.one :: TapeSymbol.zero ::
          ((encodeTokenPairs formulaTokens).map TapeSymbol.ofBool ++
            TapeSymbol.zero :: TapeSymbol.one ::
              (List.replicate (2 * assignmentTokens.length) TapeSymbol.one ++
                TapeSymbol.one :: TapeSymbol.zero ::
                  ((encodeTokenPairs assignmentTokens).map TapeSymbol.ofBool ++
                    [TapeSymbol.one, TapeSymbol.zero]))) := by
  unfold pairedTokenLayout
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_replicate_true]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        encodeWorkRight
          (cnfTokenWorkSymbols formulaTokens ++
            WorkSymbol.zeroOne ::
              (List.replicate assignmentTokens.length WorkSymbol.oneOne ++
                WorkSymbol.oneZero ::
                  (cnfTokenWorkSymbols assignmentTokens ++ [WorkSymbol.oneZero]))) = _
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_cnfTokenWorkSymbols]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        ((encodeTokenPairs formulaTokens).map TapeSymbol.ofBool ++
          TapeSymbol.zero :: TapeSymbol.one ::
            encodeWorkRight
              (List.replicate assignmentTokens.length WorkSymbol.oneOne ++
                WorkSymbol.oneZero ::
                  (cnfTokenWorkSymbols assignmentTokens ++ [WorkSymbol.oneZero]))) = _
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_replicate_true]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        ((encodeTokenPairs formulaTokens).map TapeSymbol.ofBool ++
          TapeSymbol.zero :: TapeSymbol.one ::
            (List.replicate (2 * assignmentTokens.length) TapeSymbol.one ++
              TapeSymbol.one :: TapeSymbol.zero ::
                encodeWorkRight
                  (cnfTokenWorkSymbols assignmentTokens ++ [WorkSymbol.oneZero]))) = _
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_cnfTokenWorkSymbols]
  rfl

/-- The readable token layout encodes to exactly the raw canonical pair, with
no extra cell and no discarded cell. -/
theorem encodeWorkRight_pairedTokenLayout
    (formulaTokens assignmentTokens : List CNFToken) :
    encodeWorkRight (pairedTokenLayout formulaTokens assignmentTokens) =
      (BitString.pair (paddedFormulaTokenBits formulaTokens)
        (assignmentCertificateTokenBits assignmentTokens)).map
          TapeSymbol.ofBool := by
  rw [encodeWorkRight_pairedTokenLayout_normalized]
  unfold BitString.pair BitString.frame
  rw [map_ofBool_append]
  rw [map_ofBool_append, map_ofBool_append]
  rw [map_ofBool_replicate_true, map_ofBool_replicate_true]
  rw [paddedFormulaTokenBits_length, assignmentCertificateTokenBits_length]
  rw [replicate_one_succ_tail, replicate_one_add_two]
  unfold paddedFormulaTokenBits assignmentCertificateTokenBits
  rw [map_ofBool_append, map_ofBool_append]
  repeat' rw [tapeSymbol_append_assoc]
  rfl

/-- Packing the exact raw pair recovers the explicit token layout. -/
theorem packWorkSymbols_paired_flat_tokens
    (formulaTokens assignmentTokens : List CNFToken) :
    packWorkSymbols
        ((BitString.pair (paddedFormulaTokenBits formulaTokens)
          (assignmentCertificateTokenBits assignmentTokens)).map
            TapeSymbol.ofBool) =
      pairedTokenLayout formulaTokens assignmentTokens := by
  have hEncoded :=
    encodeWorkRight_pairedTokenLayout formulaTokens assignmentTokens
  have hPacked := congrArg packWorkSymbols hEncoded
  rw [packWorkSymbols_encodeWorkRight] at hPacked
  exact hPacked

/-- Specialisation to the canonical formula and assignment encoders. -/
theorem packWorkSymbols_encoded_cnf_assignment
    (formula : CNFFormula) (assignment : BitString) :
    packWorkSymbols
        ((BitString.pair (encodeFormula formula)
          (encodeAssignmentCertificate assignment)).map TapeSymbol.ofBool) =
      pairedTokenLayout (encodeFormulaTokens formula)
        (assignmentValueTokens assignment) := by
  rw [encodeFormula_eq_padded_tokens]
  rw [encodeAssignmentCertificate_eq_token_bits]
  exact packWorkSymbols_paired_flat_tokens _ _

/-- The paired work tape starts on the first symbol of the explicit canonical
layout.  The layout is nonempty because every formula-token header contributes
at least its outer `Finish`. -/
theorem pairedWorkTape_encoded_cnf_assignment
    (formula : CNFFormula) (assignment : BitString) :
    pairedWorkTape (encodeFormula formula)
        (encodeAssignmentCertificate assignment) =
      WorkTape.ofSymbols
        (pairedTokenLayout (encodeFormulaTokens formula)
          (assignmentValueTokens assignment)) := by
  unfold pairedWorkTape
  rw [packWorkSymbols_encoded_cnf_assignment]

end PNP.Concrete
