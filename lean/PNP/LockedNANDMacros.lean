/-
Copyright (c) 2026 PNP Labs.

Concrete Boolean semantics for the locked-NAND macros in report Section 17 and
Appendix A.

Unlike the earlier bridge layers, this file does not represent the macro truth
laws by string handles.  It defines every displayed NAND gate and proves the
key distinguished-output identities by exhaustive Boolean case analysis.  It
also checks, by reduction inside Lean, that the exposed outputs of each macro
instance have pairwise-distinct truth signatures and are neither constant nor
positive projections.
-/

import PNP.NANDSemantics

namespace PNP

/-- Boolean equality as a Boolean-valued function. -/
def boolEq (a b : Bool) : Bool :=
  (a && b) || (!a && !b)

structure Bool2 where
  x1 : Bool
  x2 : Bool
  deriving Repr, DecidableEq

structure Bool3 where
  x1 : Bool
  x2 : Bool
  x3 : Bool
  deriving Repr, DecidableEq

structure Bool4 where
  x1 : Bool
  x2 : Bool
  x3 : Bool
  x4 : Bool
  deriving Repr, DecidableEq

/-- Lexicographic Boolean rows in the report's displayed order. -/
def boolRows2 : List Bool2 := [
  { x1 := false, x2 := false },
  { x1 := false, x2 := true },
  { x1 := true, x2 := false },
  { x1 := true, x2 := true }
]

def boolRows3 : List Bool3 := [
  { x1 := false, x2 := false, x3 := false },
  { x1 := false, x2 := false, x3 := true },
  { x1 := false, x2 := true, x3 := false },
  { x1 := false, x2 := true, x3 := true },
  { x1 := true, x2 := false, x3 := false },
  { x1 := true, x2 := false, x3 := true },
  { x1 := true, x2 := true, x3 := false },
  { x1 := true, x2 := true, x3 := true }
]

def boolRows4 : List Bool4 := [
  { x1 := false, x2 := false, x3 := false, x4 := false },
  { x1 := false, x2 := false, x3 := false, x4 := true },
  { x1 := false, x2 := false, x3 := true, x4 := false },
  { x1 := false, x2 := false, x3 := true, x4 := true },
  { x1 := false, x2 := true, x3 := false, x4 := false },
  { x1 := false, x2 := true, x3 := false, x4 := true },
  { x1 := false, x2 := true, x3 := true, x4 := false },
  { x1 := false, x2 := true, x3 := true, x4 := true },
  { x1 := true, x2 := false, x3 := false, x4 := false },
  { x1 := true, x2 := false, x3 := false, x4 := true },
  { x1 := true, x2 := false, x3 := true, x4 := false },
  { x1 := true, x2 := false, x3 := true, x4 := true },
  { x1 := true, x2 := true, x3 := false, x4 := false },
  { x1 := true, x2 := true, x3 := false, x4 := true },
  { x1 := true, x2 := true, x3 := true, x4 := false },
  { x1 := true, x2 := true, x3 := true, x4 := true }
]

def signature2 (f : Bool → Bool → Bool) : List Bool :=
  boolRows2.map (fun x => f x.x1 x.x2)


def signature3 (f : Bool → Bool → Bool → Bool) : List Bool :=
  boolRows3.map (fun x => f x.x1 x.x2 x.x3)


def signature4 (f : Bool → Bool → Bool → Bool → Bool) : List Bool :=
  boolRows4.map (fun x => f x.x1 x.x2 x.x3 x.x4)

structure EqualityMacroOutputs where
  a1 : Bool
  a2 : Bool
  a3 : Bool
  a4 : Bool
  a5 : Bool
  a6 : Bool
  a7 : Bool
  a8 : Bool
  a9 : Bool
  a10 : Bool
  deriving Repr, DecidableEq

/-- The ten-gate equality macro `M=` from report Section 17.2. -/
def equalityMacro (r u s : Bool) : EqualityMacroOutputs :=
  let a1 := boolNand r u
  let a2 := boolNand r s
  let a3 := boolNand a1 a1
  let a4 := boolNand a3 s
  let a5 := boolNand r a1
  let a6 := boolNand a5 a5
  let a7 := boolNand a6 a2
  let a8 := boolNand a4 a7
  let a9 := boolNand r r
  let a10 := boolNand a9 u
  { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 }

/-- The equality macro's distinguished output is the active-lock equality
predicate stated in the report. -/
theorem equalityMacro_distinguished_spec (r u s : Bool) :
    (equalityMacro r u s).a8 = (r && boolEq u s) := by
  cases r <;> cases u <;> cases s <;> decide

structure ConstantOneMacroOutputs where
  b1 : Bool
  b2 : Bool
  deriving Repr, DecidableEq

/-- The two-gate constant-one macro `M1`. -/
def constantOneMacro (r u : Bool) : ConstantOneMacroOutputs :=
  let b1 := boolNand r u
  let b2 := boolNand b1 b1
  { b1, b2 }


theorem constantOneMacro_distinguished_spec (r u : Bool) :
    (constantOneMacro r u).b2 = (r && u) := by
  cases r <;> cases u <;> decide

structure ConstantZeroMacroOutputs where
  d1 : Bool
  d2 : Bool
  d3 : Bool
  deriving Repr, DecidableEq

/-- The three-gate constant-zero macro `M0`. -/
def constantZeroMacro (r u : Bool) : ConstantZeroMacroOutputs :=
  let d1 := boolNand r u
  let d2 := boolNand r d1
  let d3 := boolNand d2 d2
  { d1, d2, d3 }


theorem constantZeroMacro_distinguished_spec (r u : Bool) :
    (constantZeroMacro r u).d3 = (r && !u) := by
  cases r <;> cases u <;> decide

structure TraceMacroOutputs where
  q1 : Bool
  q2 : Bool
  q3 : Bool
  q4 : Bool
  q5 : Bool
  q6 : Bool
  q7 : Bool
  q8 : Bool
  q9 : Bool
  q10 : Bool
  q11 : Bool
  q12 : Bool
  q13 : Bool
  q14 : Bool
  q15 : Bool
  q16 : Bool
  q17 : Bool
  q18 : Bool
  deriving Repr, DecidableEq

/-- The eighteen-gate NAND trace-check macro `MN`. -/
def traceMacro (lock trace u v : Bool) : TraceMacroOutputs :=
  let q1 := boolNand lock trace
  let q2 := boolNand q1 q1
  let q3 := boolNand lock u
  let q4 := boolNand lock v
  let q5 := boolNand q2 q3
  let q6 := boolNand q2 u
  let q7 := boolNand q6 q6
  let q8 := boolNand q7 q4
  let q9 := boolNand lock q1
  let q10 := boolNand q9 q9
  let q11 := boolNand q10 u
  let q12 := boolNand q11 q11
  let q13 := boolNand q12 v
  let q14 := boolNand q5 q8
  let q15 := boolNand q14 q14
  let q16 := boolNand q15 q13
  let q17 := boolNand lock lock
  let q18 := boolNand q17 trace
  { q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18 }

/-- The trace macro's distinguished output is the active-lock NAND equation. -/
theorem traceMacro_distinguished_spec (lock trace u v : Bool) :
    (traceMacro lock trace u v).q16 =
      (lock && boolEq trace (boolNand u v)) := by
  cases lock <;> cases trace <;> cases u <;> cases v <;> decide

/-- The report's four-gate final conjunction. -/
def finalConjunction4 (z traceChecks outputBit : Bool) : Bool :=
  let n1 := boolNand traceChecks outputBit
  let andTraceOutput := boolNand n1 n1
  let n2 := boolNand z andTraceOutput
  boolNand n2 n2


theorem finalConjunction4_spec (z traceChecks outputBit : Bool) :
    finalConjunction4 z traceChecks outputBit =
      (z && traceChecks && outputBit) := by
  cases z <;> cases traceChecks <;> cases outputBit <;> decide

/-- The final lock is essential when the trace checks and output bit are true. -/
theorem finalConjunction4_final_lock_separation :
    finalConjunction4 false true true ≠ finalConjunction4 true true true := by
  decide

/-- Truth signatures for all ten exposed equality-macro outputs. -/
def equalityMacroSignatures : List (List Bool) := [
  signature3 (fun r u s => (equalityMacro r u s).a1),
  signature3 (fun r u s => (equalityMacro r u s).a2),
  signature3 (fun r u s => (equalityMacro r u s).a3),
  signature3 (fun r u s => (equalityMacro r u s).a4),
  signature3 (fun r u s => (equalityMacro r u s).a5),
  signature3 (fun r u s => (equalityMacro r u s).a6),
  signature3 (fun r u s => (equalityMacro r u s).a7),
  signature3 (fun r u s => (equalityMacro r u s).a8),
  signature3 (fun r u s => (equalityMacro r u s).a9),
  signature3 (fun r u s => (equalityMacro r u s).a10)
]


def constantOneMacroSignatures : List (List Bool) := [
  signature2 (fun r u => (constantOneMacro r u).b1),
  signature2 (fun r u => (constantOneMacro r u).b2)
]


def constantZeroMacroSignatures : List (List Bool) := [
  signature2 (fun r u => (constantZeroMacro r u).d1),
  signature2 (fun r u => (constantZeroMacro r u).d2),
  signature2 (fun r u => (constantZeroMacro r u).d3)
]


def traceMacroSignatures : List (List Bool) := [
  signature4 (fun l t u v => (traceMacro l t u v).q1),
  signature4 (fun l t u v => (traceMacro l t u v).q2),
  signature4 (fun l t u v => (traceMacro l t u v).q3),
  signature4 (fun l t u v => (traceMacro l t u v).q4),
  signature4 (fun l t u v => (traceMacro l t u v).q5),
  signature4 (fun l t u v => (traceMacro l t u v).q6),
  signature4 (fun l t u v => (traceMacro l t u v).q7),
  signature4 (fun l t u v => (traceMacro l t u v).q8),
  signature4 (fun l t u v => (traceMacro l t u v).q9),
  signature4 (fun l t u v => (traceMacro l t u v).q10),
  signature4 (fun l t u v => (traceMacro l t u v).q11),
  signature4 (fun l t u v => (traceMacro l t u v).q12),
  signature4 (fun l t u v => (traceMacro l t u v).q13),
  signature4 (fun l t u v => (traceMacro l t u v).q14),
  signature4 (fun l t u v => (traceMacro l t u v).q15),
  signature4 (fun l t u v => (traceMacro l t u v).q16),
  signature4 (fun l t u v => (traceMacro l t u v).q17),
  signature4 (fun l t u v => (traceMacro l t u v).q18)
]


def constantSignatures2 : List (List Bool) := [
  List.replicate 4 false,
  List.replicate 4 true
]


def constantSignatures3 : List (List Bool) := [
  List.replicate 8 false,
  List.replicate 8 true
]


def constantSignatures4 : List (List Bool) := [
  List.replicate 16 false,
  List.replicate 16 true
]


def positiveProjectionSignatures2 : List (List Bool) := [
  signature2 (fun r _ => r),
  signature2 (fun _ u => u)
]


def positiveProjectionSignatures3 : List (List Bool) := [
  signature3 (fun r _ _ => r),
  signature3 (fun _ u _ => u),
  signature3 (fun _ _ s => s)
]


def positiveProjectionSignatures4 : List (List Bool) := [
  signature4 (fun l _ _ _ => l),
  signature4 (fun _ t _ _ => t),
  signature4 (fun _ _ u _ => u),
  signature4 (fun _ _ _ v => v)
]

/-- Appendix-A single-instance distinctness checks. -/
theorem equalityMacroSignatures_nodup : equalityMacroSignatures.Nodup := by
  decide


theorem constantOneMacroSignatures_nodup : constantOneMacroSignatures.Nodup := by
  decide


theorem constantZeroMacroSignatures_nodup : constantZeroMacroSignatures.Nodup := by
  decide


theorem traceMacroSignatures_nodup : traceMacroSignatures.Nodup := by
  decide

/-- Appendix-A constant/projection exclusion checks. -/
theorem equalityMacroSignatures_nonconstant_nonprojection :
    equalityMacroSignatures.all (fun sig =>
      !(constantSignatures3.contains sig) &&
      !(positiveProjectionSignatures3.contains sig)) = true := by
  decide


theorem constantOneMacroSignatures_nonconstant_nonprojection :
    constantOneMacroSignatures.all (fun sig =>
      !(constantSignatures2.contains sig) &&
      !(positiveProjectionSignatures2.contains sig)) = true := by
  decide


theorem constantZeroMacroSignatures_nonconstant_nonprojection :
    constantZeroMacroSignatures.all (fun sig =>
      !(constantSignatures2.contains sig) &&
      !(positiveProjectionSignatures2.contains sig)) = true := by
  decide


theorem traceMacroSignatures_nonconstant_nonprojection :
    traceMacroSignatures.all (fun sig =>
      !(constantSignatures4.contains sig) &&
      !(positiveProjectionSignatures4.contains sig)) = true := by
  decide

/-- A proof-bearing summary of the concrete macro facts checked in this file. -/
structure LockedNANDMacroCertificate : Prop where
  equalityDistinguished : ∀ r u s,
    (equalityMacro r u s).a8 = (r && boolEq u s)
  constantOneDistinguished : ∀ r u,
    (constantOneMacro r u).b2 = (r && u)
  constantZeroDistinguished : ∀ r u,
    (constantZeroMacro r u).d3 = (r && !u)
  traceDistinguished : ∀ l t u v,
    (traceMacro l t u v).q16 = (l && boolEq t (boolNand u v))
  finalConjunction : ∀ z t y,
    finalConjunction4 z t y = (z && t && y)
  finalLockEssential :
    finalConjunction4 false true true ≠ finalConjunction4 true true true
  equalityOutputsDistinct : equalityMacroSignatures.Nodup
  constantOneOutputsDistinct : constantOneMacroSignatures.Nodup
  constantZeroOutputsDistinct : constantZeroMacroSignatures.Nodup
  traceOutputsDistinct : traceMacroSignatures.Nodup
  equalityOutputsNonconstantNonprojection :
    equalityMacroSignatures.all (fun sig =>
      !(constantSignatures3.contains sig) &&
      !(positiveProjectionSignatures3.contains sig)) = true
  constantOneOutputsNonconstantNonprojection :
    constantOneMacroSignatures.all (fun sig =>
      !(constantSignatures2.contains sig) &&
      !(positiveProjectionSignatures2.contains sig)) = true
  constantZeroOutputsNonconstantNonprojection :
    constantZeroMacroSignatures.all (fun sig =>
      !(constantSignatures2.contains sig) &&
      !(positiveProjectionSignatures2.contains sig)) = true
  traceOutputsNonconstantNonprojection :
    traceMacroSignatures.all (fun sig =>
      !(constantSignatures4.contains sig) &&
      !(positiveProjectionSignatures4.contains sig)) = true

/-- The concrete locked-NAND macro certificate, constructed entirely by Lean. -/
def lockedNANDMacroCertificate : LockedNANDMacroCertificate :=
  { equalityDistinguished := equalityMacro_distinguished_spec
    constantOneDistinguished := constantOneMacro_distinguished_spec
    constantZeroDistinguished := constantZeroMacro_distinguished_spec
    traceDistinguished := traceMacro_distinguished_spec
    finalConjunction := finalConjunction4_spec
    finalLockEssential := finalConjunction4_final_lock_separation
    equalityOutputsDistinct := equalityMacroSignatures_nodup
    constantOneOutputsDistinct := constantOneMacroSignatures_nodup
    constantZeroOutputsDistinct := constantZeroMacroSignatures_nodup
    traceOutputsDistinct := traceMacroSignatures_nodup
    equalityOutputsNonconstantNonprojection :=
      equalityMacroSignatures_nonconstant_nonprojection
    constantOneOutputsNonconstantNonprojection :=
      constantOneMacroSignatures_nonconstant_nonprojection
    constantZeroOutputsNonconstantNonprojection :=
      constantZeroMacroSignatures_nonconstant_nonprojection
    traceOutputsNonconstantNonprojection :=
      traceMacroSignatures_nonconstant_nonprojection }

end PNP
