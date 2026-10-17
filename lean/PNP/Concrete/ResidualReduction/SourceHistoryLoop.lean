import PNP.Concrete.ResidualReduction.SourceHistoryQuery

/-! One fixed loop matches the complete dimension-recursive reduction. Every
successful iteration obtains its own next family and retains its own source and
step; an absent step stops without claiming that the residual is unsatisfiable. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryLoop
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState

def success : Block 63 := .seq SourceHistoryRecord.block SourceHistoryAdvance.block
def stepCheck : Block 63 := .branch 61 SourceHistoryQuery.stop SourceHistoryQuery.stop success
def positive : Block 63 := .seq SourceHistoryQuery.block stepCheck
def body : Block 63 := .branch 57 SourceHistoryQuery.stop SourceHistoryQuery.stop positive
def block : Block 63 := .loop 62 body

def finished (n : Nat) (F : Family n) (h : List StepRecord) : Saved :=
  SourceHistoryState.stopped (data (reduce n F).core (h ++ (reduce n F).history))

def fuel : (n : Nat) → Family n → Nat
  | 0,_ => 5
  | n + 1,F =>
    match globalStep F with
    | none => SourceOriginalSuccessorRaw.budget (packet F).length + 65
    | some s => SourceOriginalSuccessorRaw.budget (packet F).length + 62 +
      SourceHistoryRecord.fuel F s + SourceHistoryAdvance.fuel n F.length s.pivot.val +
      fuel n s.output

theorem body_zero (F : Family 0) (h : List StepRecord) :
    Exec body (work [] [] (data F h)) 3 (work [] [] (SourceHistoryState.stopped (data F h))) :=
  Exec.empty rfl (SourceHistoryQuery.stop_exec (data F h))

theorem body_absent {n : Nat} (F : Family (n + 1)) (h : List StepRecord)
    (absent : globalStep F = none) :
    ∃ used, Exec body (work [] [] (data F h)) used (work [] [] (SourceHistoryState.stopped (data F h))) ∧
      used ≤ SourceOriginalSuccessorRaw.budget (packet F).length + 63 := by
  obtain ⟨used,query,bound⟩ := SourceHistoryQuery.block_exec (data F h)
  rw [SourceHistoryQuery.queried_positive,absent,SourceOriginalSuccessorState.step_none] at query
  let observed := {data F h with step := [false]}
  have check : Exec stepCheck (work [] [] observed) 3 (work [] [] (SourceHistoryState.stopped (data F h))) := by
    simpa only [stepCheck,SourceHistoryState.stopped,observed] using
      Exec.zero (empty := SourceHistoryQuery.stop) (one := success) rfl (SourceHistoryQuery.stop_exec observed)
  have dimension : (work [] [] (data F h)).get 57 = true :: List.replicate n true := by
    change List.replicate (n + 1) true = true :: List.replicate n true
    rw [List.replicate_succ]
  refine ⟨1 + (used + 3),Exec.one dimension (Exec.seq query check),?_⟩
  change used ≤ SourceOriginalSuccessorRaw.budget (packet F).length + 59 at bound
  omega

theorem body_selected {n : Nat} (F : Family (n + 1)) (h : List StepRecord)
    (s : ConstructedStep n F.length) (selected : globalStep F = some s) :
    ∃ used, Exec body (work [] [] (data F h)) used
      (work [] [] (data s.output (h ++ [⟨n,F,s⟩]))) ∧
      used ≤ SourceOriginalSuccessorRaw.budget (packet F).length + 61 +
        SourceHistoryRecord.fuel F s + SourceHistoryAdvance.fuel n F.length s.pivot.val := by
  obtain ⟨used,query,bound⟩ := SourceHistoryQuery.block_exec (data F h)
  rw [SourceHistoryQuery.queried_positive,selected] at query
  have check : Exec stepCheck (work [] [] (SourceHistoryRecord.before F h s))
      (1 + (SourceHistoryRecord.fuel F s + SourceHistoryAdvance.fuel n F.length s.pivot.val))
      (work [] [] (data s.output (h ++ [⟨n,F,s⟩]))) :=
    Exec.one rfl (Exec.seq (SourceHistoryRecord.block_exec F h s)
      (SourceHistoryAdvance.block_exec F h s (globalStep_sound F s selected).1))
  have dimension : (work [] [] (data F h)).get 57 = true :: List.replicate n true := by
    change List.replicate (n + 1) true = true :: List.replicate n true
    rw [List.replicate_succ]
  refine ⟨1 + (used + (1 + (SourceHistoryRecord.fuel F s +
      SourceHistoryAdvance.fuel n F.length s.pivot.val))),Exec.one dimension (Exec.seq query check),?_⟩
  change used ≤ SourceOriginalSuccessorRaw.budget (packet F).length + 59 at bound
  omega

theorem block_exec (n : Nat) (F : Family n) (h : List StepRecord) :
    ∃ used, Exec block (work [] [] (data F h)) used (work [] [] (finished n F h)) ∧
      used ≤ fuel n F := by
  induction n generalizing h with
  | zero =>
    have halt : Exec block (work [] [] (SourceHistoryState.stopped (data F h))) 1
        (work [] [] (SourceHistoryState.stopped (data F h))) := Exec.loopStop rfl
    have run := Exec.loopStep (source := (62 : Fin 63)) rfl (body_zero F h) halt
    refine ⟨5,?_,Nat.le_refl 5⟩
    simpa only [block,finished,reduce,keep,List.append_nil] using run
  | succ n ih =>
    cases selected : globalStep F with
    | none =>
      obtain ⟨used,run,bound⟩ := body_absent F h selected
      have halt : Exec block (work [] [] (SourceHistoryState.stopped (data F h))) 1
          (work [] [] (SourceHistoryState.stopped (data F h))) := Exec.loopStop rfl
      have loop := Exec.loopStep (source := (62 : Fin 63)) rfl run halt
      have target : finished (n + 1) F h = SourceHistoryState.stopped (data F h) := by
        unfold finished
        have reduced : reduce (n + 1) F = keep F := by simp only [reduce,selected]
        rw [reduced]
        simp only [keep,List.append_nil]
      refine ⟨1 + (used + 1),?_,?_⟩
      · rw [target]
        exact loop
      · simp only [fuel,selected]
        omega
    | some s =>
      obtain ⟨used,run,bound⟩ := body_selected F h s selected
      obtain ⟨later,tail,tailBound⟩ := ih s.output (h ++ [⟨n,F,s⟩])
      have loop := Exec.loopStep (source := (62 : Fin 63)) rfl run tail
      have target : finished (n + 1) F h = finished n s.output (h ++ [⟨n,F,s⟩]) := by
        unfold finished
        have reduced : reduce (n + 1) F = SourceChain.prepend F s (reduce n s.output) := by
          simp only [reduce,selected]
        rw [reduced]
        simp only [SourceChain.prepend,List.append_assoc,List.singleton_append]
      refine ⟨1 + (used + later),?_,?_⟩
      · rw [target]
        exact loop
      · simp only [fuel,selected]
        omega

end PNP.Concrete.ResidualReduction.SourceHistoryLoop
