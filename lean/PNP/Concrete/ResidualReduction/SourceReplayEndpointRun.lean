import PNP.Concrete.ResidualReduction.SourceReplayEndpointCheck

/-! Guarded, all-count history execution in the closed endpoint workspace.
The initial and final witness widths are checked literally. A prior failure
skips the history and remains rejected. This is the execution consumer, not
yet the loader-to-consumer adapter, output codec or physical-runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointRun
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState

theorem work_enclose (count : Nat) (input point : BitString) (p : Parameters) (loopGood good : Bool) :
    work count input point p loopGood good =
      enclose (SourceReplayLoopMachine.work count input point p.recover loopGood) [] p good := rfl

def firstGood (p : Parameters) (point : BitString) (prior : Bool) : Bool :=
  prior && SourceReplayEndpointCheck.valid false p point
def iteration (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) : SourceReplayLoopFields.Result :=
  if good then SourceReplayLoopFields.scan p.recover count input point else ⟨input,point,false⟩
def gate : Block 40 := .branch 38 (.action (.clear 30)) (.action (.clear 30))
  (.seq (.action (.push 28 true)) (.seq (lift31 SourceReplayLoopMachine.block) (guard 28)))
def gateFuel (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) : Nat :=
  if good then SourceReplayLoopMachine.fuel p.recover count input point + 4 else 2

theorem gate_exec (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) :
    Exec gate (work count input point p false good) (gateFuel p count input point good)
      (work 0 (iteration p count input point good).input (iteration p count input point good).point p
        (iteration p count input point good).valid (iteration p count input point good).valid) := by
  cases good with
  | false =>
    have read := read_valid (SourceReplayState.blank input []) count point [] p false false
    exact Exec.empty read (clear_count_exec input point count p false false)
  | true =>
    let r := SourceReplayLoopFields.scan p.recover count input point
    have loop : Exec (lift31 SourceReplayLoopMachine.block) (work count input point p true true)
        (SourceReplayLoopMachine.fuel p.recover count input point)
        (work 0 r.input r.point p r.valid true) := by
      have checked := lift31_exec (SourceReplayLoopMachine.block_exec p.recover count input point) [] p true
      simpa only [SourceReplayLoopMachine.finalState,← work_enclose,r] using checked
    have combined : Exec (guard 28) (work 0 r.input r.point p r.valid true) 2
        (work 0 r.input r.point p r.valid r.valid) := by
      have checked := guard_exec (SourceReplayState.blank r.input []) 0 r.point [] p r.valid true r.valid 28
        (read_loop_valid (SourceReplayState.blank r.input []) 0 r.point [] p r.valid true)
      simpa only [work,Bool.true_and] using checked
    have read := read_valid (SourceReplayState.blank input []) count point [] p false true
    have checked : Exec gate (work count input point p false true)
        (1 + (1 + (SourceReplayLoopMachine.fuel p.recover count input point + 2)))
        (work 0 r.input r.point p r.valid r.valid) :=
      Exec.one read (Exec.seq (begin_loop_exec input point count p true) (Exec.seq loop combined))
    have cost : SourceReplayLoopMachine.fuel p.recover count input point + 4 =
        1 + (1 + (SourceReplayLoopMachine.fuel p.recover count input point + 2)) := by omega
    simpa only [gate,gateFuel,iteration,↓reduceIte,cost,r] using checked

def finalGood (p : Parameters) (r : SourceReplayLoopFields.Result) : Bool :=
  r.valid && SourceReplayEndpointCheck.valid true p r.point
def result (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) : Store 40 :=
  let r := iteration p count input point (firstGood p point prior)
  work 0 r.input r.point p r.valid (finalGood p r)
def block : Block 40 := .seq (SourceReplayEndpointCheck.block false)
  (.seq gate (SourceReplayEndpointCheck.block true))
def fuel (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) : Nat :=
  SourceReplayEndpointCheck.fuel false p point +
    (gateFuel p count input point (firstGood p point prior) +
      SourceReplayEndpointCheck.fuel true p (iteration p count input point (firstGood p point prior)).point)

theorem block_exec (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    Exec block (work count input point p false prior) (fuel p count input point prior)
      (result p count input point prior) := by
  let r := iteration p count input point (firstGood p point prior)
  exact Exec.seq (SourceReplayEndpointCheck.block_exec false input point count p false prior)
    (Exec.seq (gate_exec p count input point (firstGood p point prior))
      (SourceReplayEndpointCheck.block_exec true r.input r.point 0 p r.valid r.valid))

def answer (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) : Option BitString :=
  let r := iteration p count input point (firstGood p point prior)
  if finalGood p r then some r.point else none
def observed (r : Store 40) : Option BitString := if (r.get 38).isEmpty then none else some (r.get 26)

theorem observed_result (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    observed (result p count input point prior) = answer p count input point prior := by
  simp only [observed,result,work,read_valid,read_point,answer]
  cases accepted : finalGood p (iteration p count input point (firstGood p point prior)) <;> rfl

private theorem finish_eq (final : Bool) (p : Parameters) (point : BitString) :
    SourceReplayTraversal.finish (SourceReplayEndpointCheck.width final p) point =
      if SourceReplayEndpointCheck.valid final p point then some point else none := rfl

theorem answer_contract (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    answer p count input point prior =
      if prior then
        (SourceReplayTraversal.finish (SourceReplayEndpointCheck.width false p) point).bind fun first =>
          (SourceReplayLoopFields.observe (SourceReplayLoopFields.scan p.recover count input first)).bind fun pair =>
            SourceReplayTraversal.finish (SourceReplayEndpointCheck.width true p) pair.2
      else none := by
  cases prior <;> cases initial : SourceReplayEndpointCheck.valid false p point <;>
    cases replayed : (SourceReplayLoopFields.scan p.recover count input point).valid <;>
    simp only [answer,firstGood,iteration,finalGood,initial,replayed,SourceReplayLoopFields.observe,
      finish_eq,Bool.false_eq_true,↓reduceIte,Bool.true_and,Bool.false_and,Option.bind_none,Option.bind_some]

theorem rejected_prior (p : Parameters) (count : Nat) (input point : BitString) :
    observed (result p count input point false) = none := by
  rw [observed_result,answer_contract]
  rfl

theorem parsed_contract (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    answer p count input point prior =
      if prior then
        (SourceReplayTraversal.finish (SourceReplayEndpointCheck.width false p) point).bind fun first =>
          ((PNP.Concrete.NativeNormalization.NativeBitCodec.parseN SourceEncoding.recordCodec.parse count input).bind
            fun (records,cursor) =>
              (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne p.recover) records first).map
                fun output => (cursor,output)).bind fun pair =>
                  SourceReplayTraversal.finish (SourceReplayEndpointCheck.width true p) pair.2
      else none := by
  rw [answer_contract]
  simp only [SourceReplayLoopFields.parse_contract]

theorem iteration_bounds (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) :
    (iteration p count input point good).input.length ≤ input.length ∧
      (iteration p count input point good).point.length ≤ point.length + count := by
  cases good with
  | false => exact ⟨Nat.le_refl _,by change point.length ≤ point.length + count; omega⟩
  | true => exact SourceReplayLoopFields.bounds p.recover count input point

theorem gateFuel_bound (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) :
    gateFuel p count input point good ≤
      count * SourceReplayLoopMachine.allowance input.length (point.length + count) + 5 := by
  have checked := SourceReplayLoopMachine.fuel_bound p.recover count input point
  cases good <;> simp only [gateFuel,Bool.false_eq_true,↓reduceIte] <;> omega

theorem fuel_bound (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    fuel p count input point prior ≤
      count * SourceReplayLoopMachine.allowance input.length (point.length + count) +
        10 * (p.original + p.terminal) + 8 * point.length + 4 * count + 57 := by
  have first := SourceReplayEndpointCheck.fuel_bound false p point
  have middle := gateFuel_bound p count input point (firstGood p point prior)
  have last := SourceReplayEndpointCheck.fuel_bound true p (iteration p count input point (firstGood p point prior)).point
  have growth := (iteration_bounds p count input point (firstGood p point prior)).2
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceReplayEndpointRun
