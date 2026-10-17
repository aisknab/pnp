import PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState

/-! Initial/final exact-width witness checks in the endpoint workspace.
The unread history cursor is backed up and restored; the point, countdown,
direction and loop status are not changed. Prior rejection remains sticky. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointCheck
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState

def width (final : Bool) (p : Parameters) : Nat :=
  if final then (if p.recover then p.original else p.terminal)
  else (if p.recover then p.terminal else p.original)
def select (final : Bool) : Block 40 :=
  let projection : Fin 40 := if final then 39 else 36
  let recovery : Fin 40 := if final then 36 else 39
  .branch 35 (.action (.copy 2 projection)) (.action (.copy 2 projection)) (.action (.copy 2 recovery))

theorem select_exec (final : Bool) (input point : BitString) (count : Nat)
    (p : Parameters) (loopGood good : Bool) :
    Exec (select final) (full (SourceReplayState.blank point []) count point input p loopGood good) 2
      (full {SourceReplayState.blank point [] with remaining := List.replicate (width final p) true}
        count point input p loopGood good) := by
  let r := SourceReplayState.blank point []
  have original : Exec (.action (.copy (2 : Fin 40) 36)) (full r count point input p loopGood good) 1
      (full {r with remaining := List.replicate p.original true} count point input p loopGood good) :=
    SourceReplayEndpointState.copy_core_exec
      (Frame.join (framed r count point p loopGood) (middle input)) (saved p good) 2 1
      (List.replicate p.original true)
      (Frame.join (framed {r with remaining := List.replicate p.original true} count point p loopGood) (middle input)) rfl rfl
  have terminal : Exec (.action (.copy (2 : Fin 40) 39)) (full r count point input p loopGood good) 1
      (full {r with remaining := List.replicate p.terminal true} count point input p loopGood good) :=
    SourceReplayEndpointState.copy_core_exec
      (Frame.join (framed r count point p loopGood) (middle input)) (saved p good) 2 4
      (List.replicate p.terminal true)
      (Frame.join (framed {r with remaining := List.replicate p.terminal true} count point p loopGood) (middle input)) rfl rfl
  have read := read_mode r count point input p loopGood good
  cases final <;> cases direction : p.recover <;> rw [direction] at read <;>
    simp only [select,width,direction,Bool.false_eq_true,↓reduceIte] <;>
    first
    | exact Exec.zero read original
    | exact Exec.zero read terminal
    | exact Exec.one read original
    | exact Exec.one read terminal

def seed (final : Bool) : Block 40 :=
  .seq (.action (.copy 32 0)) (.seq (.action (.copy 0 26)) (select final))
theorem seed_exec (final : Bool) (input point : BitString) (count : Nat)
    (p : Parameters) (loopGood good : Bool) :
    Exec (seed final) (work count input point p loopGood good) 4
      (full {SourceReplayState.blank point [] with remaining := List.replicate (width final p) true}
        count point input p loopGood good) :=
  Exec.seq (backup_exec input point count p loopGood good)
    (Exec.seq (point_exec input point count p loopGood good) (select_exec final input point count p loopGood good))

def restore : Block 40 := .seq (.action (.copy 0 32)) (.action (.clear 32))
def block (final : Bool) : Block 40 := .seq (seed final) <|
  .seq (core9 SourceReplayWitness.block) <| .seq (guard 5) (.seq clear9 restore)
def fuel (final : Bool) (p : Parameters) (point : BitString) : Nat :=
  SourceReplayWitness.fuel (width final p) point + 18
def valid (final : Bool) (p : Parameters) (point : BitString) : Bool :=
  SourceReplayWitness.valid (width final p) point

theorem block_exec (final : Bool) (input point : BitString) (count : Nat)
    (p : Parameters) (loopGood good : Bool) :
    Exec (block final) (work count input point p loopGood good) (fuel final p point)
      (work count input point p loopGood (good && valid final p point)) := by
  let n := width final p
  let r := SourceReplayWitness.result (SourceReplayState.blank [] []) n point
  have first := seed_exec final input point count p loopGood good
  have checked : Exec (core9 SourceReplayWitness.block)
      (full {SourceReplayState.blank point [] with remaining := List.replicate n true}
        count point input p loopGood good)
      (SourceReplayWitness.fuel n point) (full r count point input p loopGood good) :=
    core9_exec (SourceReplayWitness.block_exec (SourceReplayState.blank [] []) n point)
      count point input p loopGood good
  have read : (full r count point input p loopGood good).get 5 =
      SourceReplayRecordState.flag (valid final p point) := rfl
  have restricted := guard_exec r count point input p loopGood good (valid final p point) 5 read
  have clean := clear9_exec r count point input p loopGood (good && valid final p point)
  have last := restore_exec input point count p loopGood (good && valid final p point)
  have cost : fuel final p point = 4 + (SourceReplayWitness.fuel n point + (2 + (10 + 2))) := by
    dsimp only [fuel,n]
    omega
  simpa only [block,cost,restore,n] using Exec.seq first (Exec.seq checked (Exec.seq restricted (Exec.seq clean last)))

theorem width_bound (final : Bool) (p : Parameters) : width final p ≤ p.original + p.terminal := by
  cases final <;> cases direction : p.recover <;>
    simp only [width,direction,Bool.false_eq_true,↓reduceIte] <;> omega

theorem fuel_bound (final : Bool) (p : Parameters) (point : BitString) :
    fuel final p point ≤ 5 * (p.original + p.terminal) + 4 * point.length + 26 := by
  have bound := SourceReplayWitness.fuel_bound (width final p) point
  have dimension := width_bound final p
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceReplayEndpointCheck
