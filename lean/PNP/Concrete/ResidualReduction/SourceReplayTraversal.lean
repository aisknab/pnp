import PNP.Concrete.ResidualReduction.SourceReplayWitness
import PNP.Concrete.ResidualReduction.SourceReplayProject

/-! Whole-history byte traversals with exact dependent-typed semantics.
Recovery traverses reverse history; projection traverses forward history.
Every step checks the actual witness width, and the final endpoint is checked
as well. This proves traversal compatibility, not arbitrary-history semantic
validity or the still-separate physical-machine implementation of the loop. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayTraversal
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceEncoding

def recoverOne (q : StepRecord) (input : BitString) : Option BitString :=
  ((pointCodec q.dimension).decode input).map fun z =>
    (pointCodec (q.dimension + 1)).encode
      (decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z)
def projectOne (q : StepRecord) (input : BitString) : Option BitString :=
  ((pointCodec (q.dimension + 1)).decode input).map fun x =>
    (pointCodec q.dimension).encode (encode q.step.pivot q.step.tail x)

def walk (step : StepRecord → BitString → Option BitString) :
    List StepRecord → BitString → Option BitString
  | [],input => some input
  | q :: rest,input => (step q input).bind (walk step rest)

theorem walk_append (step : StepRecord → BitString → Option BitString)
    (front back : List StepRecord) (input : BitString) :
    walk step (front ++ back) input = (walk step front input).bind (walk step back) := by
  induction front generalizing input with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.cons_append,walk,Option.bind_assoc]
    cases first : step q input with
    | none => rfl
    | some middle => exact ih middle

private theorem walk_singleton (step : StepRecord → BitString → Option BitString)
    (q : StepRecord) (input : BitString) : walk step [q] input = step q input := by
  cases first : step q input <;> simp only [walk,first,Option.bind_none,Option.bind_some]

theorem recover_finish (q : StepRecord) (n : Nat) (input : BitString) :
    (recoverOne q input).bind (pointCodec n).decode =
      if h : q.dimension + 1 = n then
        ((pointCodec q.dimension).decode input).map (fun z =>
          h ▸ decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z)
      else none := by
  by_cases same : q.dimension + 1 = n
  · rw [dif_pos same]
    cases parsed : (pointCodec q.dimension).decode input <;>
      simp only [recoverOne,parsed,Option.map_none,Option.bind_none,Option.map_some,
        Option.bind_some,SourceReplayWitness.decode_encoded,dif_pos same]
  · rw [dif_neg same]
    cases parsed : (pointCodec q.dimension).decode input <;>
      simp only [recoverOne,parsed,Option.map_none,Option.bind_none,Option.map_some,
        Option.bind_some,SourceReplayWitness.decode_encoded,dif_neg same]

theorem project_start (q : StepRecord) (n : Nat) (x : Point n) :
    projectOne q ((pointCodec n).encode x) =
      if h : n = q.dimension + 1 then
        some ((pointCodec q.dimension).encode (encode q.step.pivot q.step.tail (h ▸ x)))
      else none := by
  unfold projectOne
  rw [SourceReplayWitness.decode_encoded]
  by_cases same : n = q.dimension + 1
  · simp only [dif_pos same,Option.map_some]
  · simp only [dif_neg same,Option.map_none]

theorem recovery_contract (history : List StepRecord) (n d : Nat) (z : Point d) :
    (walk recoverOne history.reverse ((pointCodec d).encode z)).bind (pointCodec n).decode =
      liftHistory n d history z := by
  induction history generalizing n d with
  | nil => exact SourceReplayWitness.decode_encoded z
  | cons q rest ih =>
    rw [List.reverse_cons,walk_append]
    cases accumulated : walk recoverOne rest.reverse ((pointCodec d).encode z) with
    | none =>
      simp only [Option.bind_none]
      have tail := ih q.dimension d z
      rw [accumulated,Option.bind_none] at tail
      by_cases same : q.dimension + 1 = n
      · rw [liftHistory,dif_pos same,← tail]
        rfl
      · rw [liftHistory,dif_neg same]
    | some middle =>
      simp only [Option.bind_some,walk_singleton]
      rw [recover_finish]
      have tail := ih q.dimension d z
      rw [accumulated,Option.bind_some] at tail
      by_cases same : q.dimension + 1 = n
      · rw [dif_pos same,liftHistory,dif_pos same,tail]
      · rw [dif_neg same,liftHistory,dif_neg same]

theorem projection_contract (history : List StepRecord) (n d : Nat) (x : Point n) :
    (walk projectOne history ((pointCodec n).encode x)).bind (pointCodec d).decode =
      projectHistory n d history x := by
  induction history generalizing n d with
  | nil => exact SourceReplayWitness.decode_encoded x
  | cons q rest ih =>
    rw [walk,project_start]
    by_cases same : n = q.dimension + 1
    · rw [dif_pos same,Option.bind_some,projectHistory,dif_pos same]
      exact ih q.dimension d (encode q.step.pivot q.step.tail (same ▸ x))
    · simp only [dif_neg same,Option.bind_none,projectHistory]

def finish (n : Nat) (input : BitString) : Option BitString :=
  if SourceReplayWitness.valid n input then some input else none

theorem finish_eq (n : Nat) (input : BitString) :
    finish n input = ((pointCodec n).decode input).map (pointCodec n).encode := by
  cases parsed : (pointCodec n).decode input with
  | none =>
    have bad : SourceReplayWitness.valid n input = false := by
      cases flag : SourceReplayWitness.valid n input with
      | false => rfl
      | true =>
        obtain ⟨x,checked⟩ := SourceReplayWitness.decode_complete n input
          ((SourceReplayWitness.valid_iff_width n input).mp flag)
        rw [parsed] at checked
        cases checked
    simp only [finish,bad,Bool.false_eq_true,↓reduceIte,Option.map_none]
  | some x =>
    have good := (SourceReplayWitness.valid_iff_width n input).mpr
      (SourceReplayWitness.decode_width n input x parsed)
    have bytes := (decode_eq_some_iff (pointCodec n) input x).mp parsed
    simp only [finish,good,↓reduceIte,Option.map_some]
    exact congrArg some bytes.symm

private theorem bind_finish (result : Option BitString) (n : Nat) :
    result.bind (finish n) = (result.bind (pointCodec n).decode).map (pointCodec n).encode := by
  cases result with
  | none => rfl
  | some input => exact finish_eq n input

theorem recover_core (history : List StepRecord) (n d : Nat) (z : Point d) :
    (walk recoverOne history.reverse ((pointCodec d).encode z)).bind (finish n) =
      (liftHistory n d history z).map NativeSource.pointBytes := by
  rw [bind_finish,recovery_contract]
  have bytes : (pointCodec n).encode = NativeSource.pointBytes := funext (fun x => point_bytes x)
  rw [bytes]

theorem project_core (history : List StepRecord) (n d : Nat) (x : Point n) :
    (walk projectOne history ((pointCodec n).encode x)).bind (finish d) =
      (projectHistory n d history x).map (pointCodec d).encode := by
  rw [bind_finish,projection_contract]

def recover (n : Nat) (data witness : BitString) : Option BitString :=
  (dataCodec.decode data).bind fun d =>
    (finish d.dimension witness).bind fun input =>
      (walk recoverOne d.history.reverse input).bind (finish n)
def project (n : Nat) (data witness : BitString) : Option BitString :=
  (dataCodec.decode data).bind fun d =>
    (finish n witness).bind fun input =>
      (walk projectOne d.history input).bind (finish d.dimension)

theorem recover_eq (n : Nat) (data witness : BitString) :
    recover n data witness = recoverBytes n data witness := by
  cases decoded : dataCodec.decode data with
  | none => simp only [recover,recoverBytes,decoded,Option.bind_none]
  | some d =>
    simp only [recover,recoverBytes,decoded,Option.bind_some]
    rw [finish_eq]
    cases parsed : (pointCodec d.dimension).decode witness with
    | none => simp only [Option.map_none,Option.bind_none]
    | some z =>
      simp only [Option.map_some,Option.bind_some]
      exact recover_core d.history n d.dimension z

theorem project_eq (n : Nat) (data witness : BitString) :
    project n data witness = projectBytes n data witness := by
  cases decoded : dataCodec.decode data with
  | none => simp only [project,projectBytes,decoded,Option.bind_none]
  | some d =>
    simp only [project,projectBytes,decoded,Option.bind_some]
    rw [finish_eq]
    cases parsed : (pointCodec n).decode witness with
    | none => simp only [Option.map_none,Option.bind_none]
    | some x =>
      simp only [Option.map_some,Option.bind_some]
      exact project_core d.history n d.dimension x

def answer (input : BitString) : Option BitString :=
  (SourceReplayRequest.codec.decode input).bind fun r =>
    if r.recover then recover r.dimension r.data r.witness else project r.dimension r.data r.witness

theorem answer_eq (input : BitString) : answer input = SourceReplayRequest.answer input := by
  unfold answer SourceReplayRequest.answer SourceReplayRequest.evaluate
  simp only [recover_eq,project_eq]

theorem recoverOne_length (q : StepRecord) (input output : BitString)
    (success : recoverOne q input = some output) : output.length = input.length + 1 := by
  cases parsed : (pointCodec q.dimension).decode input with
  | none => simp only [recoverOne,parsed,Option.map_none] at success; cases success
  | some z =>
    have bytes : (pointCodec (q.dimension + 1)).encode
        (decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z) = output := by
      simpa only [recoverOne,parsed,Option.map_some,Option.some.injEq] using success
    have width := SourceReplayWitness.decode_width q.dimension input z parsed
    rw [← bytes,point_length,width]

theorem projectOne_length (q : StepRecord) (input output : BitString)
    (success : projectOne q input = some output) : output.length + 1 = input.length := by
  cases parsed : (pointCodec (q.dimension + 1)).decode input with
  | none => simp only [projectOne,parsed,Option.map_none] at success; cases success
  | some x =>
    have bytes : (pointCodec q.dimension).encode (encode q.step.pivot q.step.tail x) = output := by
      simpa only [projectOne,parsed,Option.map_some,Option.some.injEq] using success
    have width := SourceReplayWitness.decode_width (q.dimension + 1) input x parsed
    rw [← bytes,point_length,width]

theorem recovery_length (history : List StepRecord) (input output : BitString)
    (success : walk recoverOne history input = some output) :
    output.length = input.length + history.length := by
  induction history generalizing input output with
  | nil => cases success; exact (Nat.add_zero _).symm
  | cons q rest ih =>
    cases first : recoverOne q input with
    | none => simp only [walk,first,Option.bind_none] at success; cases success
    | some middle =>
      have tail : walk recoverOne rest middle = some output := by
        simpa only [walk,first,Option.bind_some] using success
      have a := recoverOne_length q input middle first
      have b := ih middle output tail
      simp only [List.length_cons]
      omega

theorem projection_length (history : List StepRecord) (input output : BitString)
    (success : walk projectOne history input = some output) :
    output.length + history.length = input.length := by
  induction history generalizing input output with
  | nil => cases success; exact Nat.add_zero _
  | cons q rest ih =>
    cases first : projectOne q input with
    | none => simp only [walk,first,Option.bind_none] at success; cases success
    | some middle =>
      have tail : walk projectOne rest middle = some output := by
        simpa only [walk,first,Option.bind_some] using success
      have a := projectOne_length q input middle first
      have b := ih middle output tail
      simp only [List.length_cons]
      omega

end PNP.Concrete.ResidualReduction.SourceReplayTraversal
