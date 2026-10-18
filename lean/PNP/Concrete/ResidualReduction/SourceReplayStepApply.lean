import PNP.Concrete.ResidualReduction.SourceReplayStepPrepare

/-! Literal dispatch to the existing computed reconstruction/projecting
machines. Only the combined parser/witness success flag enters these branches.
Failure preserves the point; every exit clears the workspace and restores
the unread record stream for the next loop iteration. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayStepApply
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceReplayStepState

def fields (q : StepRecord) : SourceReplayRecordState.Saved :=
  SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true
def start (q : StepRecord) (point : BitString) (recover : Bool) (cursor : BitString) : Store 30 :=
  full (SourceReplayState.blank [] []) (mapped (fields q) point) (fields q) ⟨point,recover,true,cursor⟩
def copyPoint : Block 30 := .action (.copy 26 8)
def recoverBlock : Block 30 := .seq (lift16 SourceReplayDecode.block) copyPoint
def projectBlock : Block 30 := .seq (lift16 SourceReplayProject.block) copyPoint
def directionBlock : Block 30 := .branch 27 .skip projectBlock recoverBlock
def selectBlock : Block 30 := .branch 28 .skip .skip directionBlock
def block : Block 30 := .seq selectBlock finishBlock

theorem failure_exec (f : SourceReplayRecordState.Saved) (point cursor : BitString) (recover : Bool) :
    Exec block (full (SourceReplayState.blank [] []) (mapped f point) f ⟨point,recover,false,cursor⟩) 31
      (work cursor point recover false) := by
  let s : Saved := ⟨point,recover,false,cursor⟩
  let r := framed (SourceReplayState.work [] [] (mapped f point)) f
  have read : (enclose r s).get 28 = [] := rfl
  have branch : Exec selectBlock (enclose r s) 2 (enclose r s) := Exec.empty read (.skip _)
  exact Exec.seq branch (finish_exec r s)

def recoverFuel (q : StepRecord) (z : Point q.dimension) : Nat :=
  SourceReplayDecode.fuel q.dimension q.source.length q.step.pivot.val
    (SourceReplayState.value q.source q.step.weights q.step.pivot z)
def projectFuel (q : StepRecord) (x : Point (q.dimension + 1)) : Nat :=
  SourceReplayProject.fuel q.dimension q.step.pivot.val (cut q.dimension q.step.pivot x).1
def recovered (q : StepRecord) (z : Point q.dimension) : BitString :=
  (SourceEncoding.pointCodec (q.dimension + 1)).encode
    (decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z)
def projected (q : StepRecord) (x : Point (q.dimension + 1)) : BitString :=
  (SourceEncoding.pointCodec q.dimension).encode (encode q.step.pivot q.step.tail x)

theorem recover_exec (q : StepRecord) (z : Point q.dimension) (cursor : BitString) :
    Exec block (start q ((SourceEncoding.pointCodec q.dimension).encode z) true cursor)
      (recoverFuel q z + 32) (work cursor (recovered q z) true true) := by
  let point := (SourceEncoding.pointCodec q.dimension).encode z
  let f := fields q
  let a := mapped f point
  let s : Saved := ⟨point,true,true,cursor⟩
  let value := SourceReplayState.value q.source q.step.weights q.step.pivot z
  let after := SourceReplayState.evaluated a value
  let r := SourceReplayState.blank [] (recovered q z)
  have computed : Exec (lift16 SourceReplayDecode.block)
      (full (SourceReplayState.blank [] []) a f s) (recoverFuel q z) (full r after f s) :=
    lift16_exec (SourceReplayDecode.block_exec q.source q.step.weights q.step.pivot q.step.tail z) f s
  have copied : Exec copyPoint (full r after f s) 1 (full r after f {s with point := recovered q z}) :=
    copyPoint_exec r after f s
  have direction : Exec directionBlock (full (SourceReplayState.blank [] []) a f s)
      (1 + (recoverFuel q z + 1)) (full r after f {s with point := recovered q z}) :=
    Exec.one rfl (Exec.seq computed copied)
  have selected : Exec selectBlock (full (SourceReplayState.blank [] []) a f s)
      (1 + (1 + (recoverFuel q z + 1))) (full r after f {s with point := recovered q z}) :=
    Exec.one rfl direction
  have last := finish_exec (framed (SourceReplayState.full r after) f) {s with point := recovered q z}
  have cost : recoverFuel q z + 32 = (1 + (1 + (recoverFuel q z + 1))) + 29 := by omega
  simpa only [block,cost,start,point,f,a,s,work] using Exec.seq selected last

theorem project_exec (q : StepRecord) (x : Point (q.dimension + 1)) (cursor : BitString) :
    Exec block (start q ((SourceEncoding.pointCodec (q.dimension + 1)).encode x) false cursor)
      (projectFuel q x + 32) (work cursor (projected q x) false true) := by
  let point := (SourceEncoding.pointCodec (q.dimension + 1)).encode x
  let f := fields q
  let a := mapped f point
  let s : Saved := ⟨point,false,true,cursor⟩
  let r := SourceReplayState.blank [] (projected q x)
  have computed : Exec (lift16 SourceReplayProject.block)
      (full (SourceReplayState.blank [] []) a f s) (projectFuel q x) (full r a f s) :=
    lift16_exec (SourceReplayProject.block_exec q.step.pivot q.step.tail x a) f s
  have copied : Exec copyPoint (full r a f s) 1 (full r a f {s with point := projected q x}) :=
    copyPoint_exec r a f s
  have direction : Exec directionBlock (full (SourceReplayState.blank [] []) a f s)
      (1 + (projectFuel q x + 1)) (full r a f {s with point := projected q x}) :=
    Exec.zero rfl (Exec.seq computed copied)
  have selected : Exec selectBlock (full (SourceReplayState.blank [] []) a f s)
      (1 + (1 + (projectFuel q x + 1))) (full r a f {s with point := projected q x}) :=
    Exec.one rfl direction
  have last := finish_exec (framed (SourceReplayState.full r a) f) {s with point := projected q x}
  have cost : projectFuel q x + 32 = (1 + (1 + (projectFuel q x + 1))) + 29 := by omega
  simpa only [block,cost,start,point,f,a,s,work] using Exec.seq selected last

def mapOne (recover : Bool) (q : StepRecord) (point : BitString) : Option BitString :=
  if recover then SourceReplayTraversal.recoverOne q point else SourceReplayTraversal.projectOne q point
def mapFuel (recover : Bool) (q : StepRecord) (point : BitString) : Nat :=
  if recover then
    match (SourceEncoding.pointCodec q.dimension).decode point with
    | none => 0
    | some z => recoverFuel q z
  else
    match (SourceEncoding.pointCodec (q.dimension + 1)).decode point with
    | none => 0
    | some x => projectFuel q x

theorem mapFuel_bound (recover : Bool) (q : StepRecord) (point : BitString) (L : Nat)
    (dimension : q.dimension ≤ L) (rows : q.source.length ≤ L) :
    mapFuel recover q point ≤ (18 * L + 49) * L + 29 * L + 45 := by
  have pivot : q.step.pivot.val ≤ q.dimension := Nat.le_of_lt_succ q.step.pivot.isLt
  cases recover with
  | false =>
    simp only [mapFuel,Bool.false_eq_true,↓reduceIte]
    cases parsed : (SourceEncoding.pointCodec (q.dimension + 1)).decode point with
    | none => exact Nat.zero_le _
    | some x =>
      have bound := SourceReplayProject.fuel_bound q.dimension q.step.pivot.val
        (cut q.dimension q.step.pivot x).1 pivot
      change SourceReplayProject.fuel q.dimension q.step.pivot.val (cut q.dimension q.step.pivot x).1 ≤ _
      omega
  | true =>
    simp only [mapFuel,↓reduceIte]
    cases parsed : (SourceEncoding.pointCodec q.dimension).decode point with
    | none => exact Nat.zero_le _
    | some z =>
      have bound := SourceReplayDecode.bounded_cost q.dimension q.source.length q.step.pivot.val L
        (SourceReplayState.value q.source q.step.weights q.step.pivot z) dimension rows pivot
      exact bound

end PNP.Concrete.ResidualReduction.SourceReplayStepApply
