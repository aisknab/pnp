/-
Copyright (c) 2026 PNP Labs.

First-match transition contracts for the literal CNF work machine.  These
lemmas expose the finite rule table to the phase-invariant proof without
replacing any transition by a functional oracle.
-/

import PNP.Concrete.CNFWorkMachine

namespace PNP.Concrete

/-! ### Generic first-match facts -/

/-- Any successful first-match lookup really matches the queried key. -/
theorem cnfFindRuleCase {rules : List WorkRule} {state : Nat}
    {symbol : WorkSymbol} {rule : WorkRule}
    (h : findWorkRule rules state symbol = some rule) :
    rule.sourceState = state ∧ rule.readSymbol = symbol := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst : first.sourceState = state ∧
          first.readSymbol = symbol
      · have hHead := findWorkRule_cons_of_matches first rest state symbol hFirst
        have hRule : first = rule := Option.some.inj (hHead.symm.trans h)
        exact
          ⟨(congrArg WorkRule.sourceState hRule).symm.trans hFirst.1,
           (congrArg WorkRule.readSymbol hRule).symm.trans hFirst.2⟩
      · have hTail := findWorkRule_cons_of_not_matches first rest state
          symbol hFirst
        exact ih (hTail.symm.trans h)

/-! ### Total reject suffix -/

private theorem findWorkRule_rejectMap_of_mem (source : Nat)
    (symbols : List WorkSymbol) (symbol : WorkSymbol)
    (hMem : List.Mem symbol symbols) :
    findWorkRule (symbols.map (cnfRejectRule source)) source symbol =
      some (cnfRejectRule source symbol) := by
  induction symbols with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst : first = symbol
      · subst first
        exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
      · have hTail : List.Mem symbol rest := by
          cases hMem with
          | head => exact False.elim (hFirst rfl)
          | tail _ found => exact found
        have hSkip := findWorkRule_cons_of_not_matches
          (cnfRejectRule source first)
          (rest.map (cnfRejectRule source)) source symbol
          (by
            intro hMatches
            exact hFirst hMatches.2)
        exact hSkip.trans (ih hTail)

private theorem cnfWorkAlphabet_complete (symbol : WorkSymbol) :
    List.Mem symbol cnfWorkAlphabet := by
  cases symbol with
  | mk first second =>
      cases first with
      | blank =>
          cases second with
          | blank => exact List.Mem.head _
          | zero => exact List.Mem.tail _ (List.Mem.head _)
          | one => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      | zero =>
          cases second with
          | blank => exact List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.head _)))
          | zero => exact List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | one => exact List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.head _)))))
      | one =>
          cases second with
          | blank => exact List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
          | zero => exact List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.head _)))))))
          | one => exact List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

theorem findWorkRule_cnfRejectSuffix (source : Nat) (symbol : WorkSymbol) :
    findWorkRule (cnfRejectSuffix source) source symbol =
      some (cnfRejectRule source symbol) := by
  unfold cnfRejectSuffix
  exact findWorkRule_rejectMap_of_mem source cnfWorkAlphabet symbol
    (cnfWorkAlphabet_complete symbol)

theorem findWorkRule_cnfCompleteRules (source : Nat)
    (specific : List WorkRule) (symbol : WorkSymbol) :
    findWorkRule (cnfCompleteRules source specific) source symbol =
      match findWorkRule specific source symbol with
      | some rule => some rule
      | none => some (cnfRejectRule source symbol) := by
  cases hSpecific : findWorkRule specific source symbol with
  | some rule =>
      unfold cnfCompleteRules
      exact findWorkRule_append_of_some specific (cnfRejectSuffix source)
        source symbol rule hSpecific
  | none =>
      unfold cnfCompleteRules
      rw [findWorkRule_append_of_none specific (cnfRejectSuffix source)
        source symbol hSpecific]
      exact findWorkRule_cnfRejectSuffix source symbol

/-! ### Concrete boot and frame contracts -/


set_option maxRecDepth 100000 in
theorem cnfFind_boot_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.boot symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_bootLeft_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.bootLeft symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneFindCounter_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneFindCounter
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneToHeader_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneToHeader
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneFindPayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneFindPayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneBackPayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneBackPayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneBackHeader_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneBackHeader
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneCheckPayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneCheckPayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneRestorePayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneRestorePayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneGoBoundary_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameOneGoBoundary
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_boot_t :
    findWorkRule cnfWorkRules CNFWorkState.boot cnfT =
      some (cnfKeepRule CNFWorkState.boot cnfT CNFWorkState.bootLeft .left) := by
  rfl

set_option maxRecDepth 100000 in
theorem cnfFind_bootLeft_blank :
    findWorkRule cnfWorkRules CNFWorkState.bootLeft cnfBlank =
      some (cnfWorkRule CNFWorkState.bootLeft cnfBlank
        CNFWorkState.frameOneFindCounter cnfRootGuard .right) := by
  rfl

/-! ### Totality contracts for every remaining nonhalting phase state -/

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoFindCounter_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoFindCounter
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoToHeader_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoToHeader
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoFindPayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoFindPayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoBackPayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoBackPayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoBackHeader_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoBackHeader
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoCheckPayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoCheckPayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoEnsureBlank_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoEnsureBlank
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoAtRightGuard_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoAtRightGuard
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_frameTwoRestorePayload_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.frameTwoRestorePayload
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_seekLeftRoot_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.seekLeftRoot symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_seekFormulaStart_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.seekFormulaStart symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthFindFormula_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthFindFormula symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthToBoundary_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthToBoundary symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthPastCertificateCounter_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthPastCertificateCounter symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthFindAssignment_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthFindAssignment
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthBackAssignment_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthBackAssignment
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthBackCertificateCounter_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthBackCertificateCounter symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthBackFormula_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthBackFormula symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthDoneToBoundary_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthDoneToBoundary
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthDonePastCertificateCounter_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthDonePastCertificateCounter symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthDoneCheckAssignment_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthDoneCheckAssignment symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthRestoreAssignment_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthRestoreAssignment
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthRestoreCertificateCounter_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthRestoreCertificateCounter symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthRestoreBackFormula_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthRestoreBackFormula symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthRestoreSeekFormula_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      CNFWorkState.widthRestoreSeekFormula symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_widthRestoreFormula_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.widthRestoreFormula
      symbol = some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_clauseStart_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.clauseStart symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_clauseNeedLiteral_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.clauseNeedLiteral symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_clauseContinue_total (alreadySatisfied : Bool)
    (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.clauseContinue alreadySatisfied) symbol = some rule := by
  cases alreadySatisfied <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_finalCheck_total (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules CNFWorkState.finalCheck symbol =
      some rule := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalIndex_total (alreadySatisfied positive : Bool)
    (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalIndex alreadySatisfied positive) symbol = some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalIndexToBoundary_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalIndexToBoundary alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalIndexPastCertificateCounter_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalIndexPastCertificateCounter alreadySatisfied positive)
        symbol = some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalMarkAssignment_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalMarkAssignment alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalReturnAssignment_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalReturnAssignment alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalReturnCertificateCounter_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalReturnCertificateCounter alreadySatisfied positive)
        symbol = some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalReturnSeekSign_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalReturnSeekSign alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalReturnSeekIndex_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalLookupToBoundary_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalLookupToBoundary alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalLookupPastCertificateCounter_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalLookupPastCertificateCounter alreadySatisfied positive)
        symbol = some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalLookupAssignment_total
    (alreadySatisfied positive : Bool) (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalLookupAssignment alreadySatisfied positive) symbol =
        some rule := by
  cases alreadySatisfied <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalRestoreAssignment_total (result positive : Bool)
    (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalRestoreAssignment result positive) symbol =
        some rule := by
  cases result <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalRestoreCertificateCounter_total (result positive : Bool)
    (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalRestoreCertificateCounter result positive) symbol =
        some rule := by
  cases result <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalRestoreSeekSign_total (result positive : Bool)
    (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalRestoreSeekSign result positive) symbol = some rule := by
  cases result <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem cnfFind_literalRestoreIndex_total (result positive : Bool)
    (symbol : WorkSymbol) :
    ∃ rule, findWorkRule cnfWorkRules
      (CNFWorkState.literalRestoreIndex result positive) symbol = some rule := by
  cases result <;> cases positive <;> cases symbol with
  | mk first second => cases first <;> cases second <;> exact ⟨_, rfl⟩

/-! The out-of-range route is intentionally explicit: reaching the right
guard preserves the prior clause result, restores all marks, scans any
remaining unary `T` tail, and only then resumes at the index terminator. -/

set_option maxRecDepth 100000 in
theorem cnfFind_literalMarkAssignment_oob
    (alreadySatisfied positive : Bool) :
    findWorkRule cnfWorkRules
      (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
      cnfRootGuard =
    some (cnfKeepRule
      (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
      cnfRootGuard
      (CNFWorkState.literalRestoreAssignment alreadySatisfied positive) .left) := by
  cases alreadySatisfied <;> cases positive <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_literalLookupAssignment_oob
    (alreadySatisfied positive : Bool) :
    findWorkRule cnfWorkRules
      (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
      cnfRootGuard =
    some (cnfKeepRule
      (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
      cnfRootGuard
      (CNFWorkState.literalRestoreAssignment alreadySatisfied positive) .left) := by
  cases alreadySatisfied <;> cases positive <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_literalRestoreIndex_rawTail (result positive : Bool) :
    findWorkRule cnfWorkRules
      (CNFWorkState.literalRestoreIndex result positive) cnfT =
    some (cnfKeepRule (CNFWorkState.literalRestoreIndex result positive)
      cnfT (CNFWorkState.literalRestoreIndex result positive) .right) := by
  cases result <;> cases positive <;> rfl

end PNP.Concrete
