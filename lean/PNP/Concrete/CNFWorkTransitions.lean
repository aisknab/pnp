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

/- The first reconstruction used functions returning an expected rule for an
arbitrary work symbol.  Lean's generated two-discriminant matcher for those
functions carries `propext`, so the proof surface deliberately uses
existential totality plus fixed-symbol `rfl` contracts instead.

namespace CNFExpectedRule

def boot (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .one, .one => cnfKeepRule CNFWorkState.boot cnfT
      CNFWorkState.bootLeft .left
  | _, _ => cnfRejectRule CNFWorkState.boot symbol

def bootLeft (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .blank, .blank => cnfWorkRule CNFWorkState.bootLeft cnfBlank
      CNFWorkState.frameOneFindCounter cnfRootGuard .right
  | _, _ => cnfRejectRule CNFWorkState.bootLeft symbol

def frameOneFindCounter (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .blank, .zero => cnfKeepRule CNFWorkState.frameOneFindCounter
      cnfMarkFalse CNFWorkState.frameOneFindCounter .right
  | .one, .one => cnfWorkRule CNFWorkState.frameOneFindCounter cnfT
      CNFWorkState.frameOneToHeader cnfMarkFalse .right
  | .one, .zero => cnfKeepRule CNFWorkState.frameOneFindCounter
      cnfFinish CNFWorkState.frameOneCheckPayload .right
  | _, _ => cnfRejectRule CNFWorkState.frameOneFindCounter symbol

def frameOneToHeader (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .one, .one => cnfKeepRule CNFWorkState.frameOneToHeader cnfT
      CNFWorkState.frameOneToHeader .right
  | .blank, .zero => cnfKeepRule CNFWorkState.frameOneToHeader
      cnfMarkFalse CNFWorkState.frameOneToHeader .right
  | .one, .zero => cnfKeepRule CNFWorkState.frameOneToHeader
      cnfFinish CNFWorkState.frameOneFindPayload .right
  | _, _ => cnfRejectRule CNFWorkState.frameOneToHeader symbol

def frameOneFindPayload (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .blank, .zero => cnfKeepRule CNFWorkState.frameOneFindPayload
      cnfMarkFalse CNFWorkState.frameOneFindPayload .right
  | .blank, .one => cnfKeepRule CNFWorkState.frameOneFindPayload
      cnfMarkTrue CNFWorkState.frameOneFindPayload .right
  | .zero, .blank => cnfKeepRule CNFWorkState.frameOneFindPayload
      cnfRootGuard CNFWorkState.frameOneFindPayload .right
  | .one, .blank => cnfKeepRule CNFWorkState.frameOneFindPayload
      cnfBoundaryGuard CNFWorkState.frameOneFindPayload .right
  | .zero, .zero => cnfWorkRule CNFWorkState.frameOneFindPayload
      cnfF CNFWorkState.frameOneBackPayload cnfMarkFalse .left
  | .one, .one => cnfWorkRule CNFWorkState.frameOneFindPayload
      cnfT CNFWorkState.frameOneBackPayload cnfMarkTrue .left
  | .zero, .one => cnfWorkRule CNFWorkState.frameOneFindPayload
      cnfSep CNFWorkState.frameOneBackPayload cnfRootGuard .left
  | .one, .zero => cnfWorkRule CNFWorkState.frameOneFindPayload
      cnfFinish CNFWorkState.frameOneBackPayload cnfBoundaryGuard .left
  | _, _ => cnfRejectRule CNFWorkState.frameOneFindPayload symbol

def frameOneBackPayload (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .blank, .zero => cnfKeepRule CNFWorkState.frameOneBackPayload
      cnfMarkFalse CNFWorkState.frameOneBackPayload .left
  | .blank, .one => cnfKeepRule CNFWorkState.frameOneBackPayload
      cnfMarkTrue CNFWorkState.frameOneBackPayload .left
  | .zero, .blank => cnfKeepRule CNFWorkState.frameOneBackPayload
      cnfRootGuard CNFWorkState.frameOneBackPayload .left
  | .one, .blank => cnfKeepRule CNFWorkState.frameOneBackPayload
      cnfBoundaryGuard CNFWorkState.frameOneBackPayload .left
  | .one, .zero => cnfKeepRule CNFWorkState.frameOneBackPayload
      cnfFinish CNFWorkState.frameOneBackHeader .left
  | _, _ => cnfRejectRule CNFWorkState.frameOneBackPayload symbol

def frameOneBackHeader (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .one, .one => cnfKeepRule CNFWorkState.frameOneBackHeader cnfT
      CNFWorkState.frameOneBackHeader .left
  | .blank, .zero => cnfKeepRule CNFWorkState.frameOneBackHeader
      cnfMarkFalse CNFWorkState.frameOneBackHeader .left
  | .zero, .blank => cnfKeepRule CNFWorkState.frameOneBackHeader
      cnfRootGuard CNFWorkState.frameOneFindCounter .right
  | _, _ => cnfRejectRule CNFWorkState.frameOneBackHeader symbol

def frameOneCheckPayload (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .blank, .zero => cnfKeepRule CNFWorkState.frameOneCheckPayload
      cnfMarkFalse CNFWorkState.frameOneCheckPayload .right
  | .blank, .one => cnfKeepRule CNFWorkState.frameOneCheckPayload
      cnfMarkTrue CNFWorkState.frameOneCheckPayload .right
  | .zero, .blank => cnfKeepRule CNFWorkState.frameOneCheckPayload
      cnfRootGuard CNFWorkState.frameOneCheckPayload .right
  | .one, .blank => cnfKeepRule CNFWorkState.frameOneCheckPayload
      cnfBoundaryGuard CNFWorkState.frameOneCheckPayload .right
  | .zero, .one => cnfWorkRule CNFWorkState.frameOneCheckPayload
      cnfSep CNFWorkState.frameOneRestorePayload cnfBoundaryGuard .left
  | _, _ => cnfRejectRule CNFWorkState.frameOneCheckPayload symbol

def frameOneRestorePayload (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .blank, .zero => cnfWorkRule CNFWorkState.frameOneRestorePayload
      cnfMarkFalse CNFWorkState.frameOneRestorePayload cnfF .left
  | .blank, .one => cnfWorkRule CNFWorkState.frameOneRestorePayload
      cnfMarkTrue CNFWorkState.frameOneRestorePayload cnfT .left
  | .zero, .blank => cnfWorkRule CNFWorkState.frameOneRestorePayload
      cnfRootGuard CNFWorkState.frameOneRestorePayload cnfSep .left
  | .one, .blank => cnfWorkRule CNFWorkState.frameOneRestorePayload
      cnfBoundaryGuard CNFWorkState.frameOneRestorePayload cnfFinish .left
  | .one, .zero => cnfKeepRule CNFWorkState.frameOneRestorePayload
      cnfFinish CNFWorkState.frameOneGoBoundary .right
  | _, _ => cnfRejectRule CNFWorkState.frameOneRestorePayload symbol

def frameOneGoBoundary (symbol : WorkSymbol) : WorkRule :=
  match symbol.first, symbol.second with
  | .zero, .zero => cnfKeepRule CNFWorkState.frameOneGoBoundary cnfF
      CNFWorkState.frameOneGoBoundary .right
  | .one, .one => cnfKeepRule CNFWorkState.frameOneGoBoundary cnfT
      CNFWorkState.frameOneGoBoundary .right
  | .zero, .one => cnfKeepRule CNFWorkState.frameOneGoBoundary cnfSep
      CNFWorkState.frameOneGoBoundary .right
  | .one, .zero => cnfKeepRule CNFWorkState.frameOneGoBoundary
      cnfFinish CNFWorkState.frameOneGoBoundary .right
  | .one, .blank => cnfKeepRule CNFWorkState.frameOneGoBoundary
      cnfBoundaryGuard CNFWorkState.frameTwoFindCounter .right
  | _, _ => cnfRejectRule CNFWorkState.frameOneGoBoundary symbol

end CNFExpectedRule

set_option maxRecDepth 100000 in
theorem cnfFind_boot (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.boot symbol =
      some (CNFExpectedRule.boot symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_bootLeft (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.bootLeft symbol =
      some (CNFExpectedRule.bootLeft symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneFindCounter (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneFindCounter symbol =
      some (CNFExpectedRule.frameOneFindCounter symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneToHeader (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneToHeader symbol =
      some (CNFExpectedRule.frameOneToHeader symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneFindPayload (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneFindPayload symbol =
      some (CNFExpectedRule.frameOneFindPayload symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneBackPayload (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneBackPayload symbol =
      some (CNFExpectedRule.frameOneBackPayload symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneBackHeader (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneBackHeader symbol =
      some (CNFExpectedRule.frameOneBackHeader symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneCheckPayload (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneCheckPayload symbol =
      some (CNFExpectedRule.frameOneCheckPayload symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneRestorePayload (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneRestorePayload symbol =
      some (CNFExpectedRule.frameOneRestorePayload symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

set_option maxRecDepth 100000 in
theorem cnfFind_frameOneGoBoundary (symbol : WorkSymbol) :
    findWorkRule cnfWorkRules CNFWorkState.frameOneGoBoundary symbol =
      some (CNFExpectedRule.frameOneGoBoundary symbol) := by
  cases symbol with
  | mk first second => cases first <;> cases second <;> rfl

-/

private theorem cnfFind_total_at (state : Nat) (symbol : WorkSymbol)
    (h : ∃ rule, findWorkRule cnfWorkRules state symbol = some rule) :
    ∃ rule, findWorkRule cnfWorkRules state symbol = some rule := h

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

end PNP.Concrete
