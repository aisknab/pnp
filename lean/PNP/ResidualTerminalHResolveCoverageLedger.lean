/-
Copyright (c) 2026 PNP Labs.

Executable finite-family coverage ledger for the HResolve branch of the pinned
manuscript's no-lower boundary.  Every supplied candidate is classified by
decidable exact, gain, and blocker predicates in that priority order.  The
NoHereditary checker also verifies that the supplied candidate enumeration has
no duplicates and accepts only when every candidate is classified blocked.

This is a bounded HResolve coverage result over an arbitrary supplied finite
family and supplied decidable predicates.  It does not construct the governed
hereditary family from terminal data, prove that the predicates implement the
manuscript's HN grammar, BWL exactness, H-disjointness, exact-minimum or gain
semantics, discharge BudgetResolve or the complete no-lower ledger, establish
unconditional ZeroSlack or polynomial PCCMin, remove a project assumption,
prove SAT in P, or prove P = NP.
-/

import PNP.ResidualRoutes

namespace PNP
namespace DirectWire

/-! ## Executable route classification -/

/-- The four outcomes exposed by the bounded HResolve coverage classifier. -/
inductive TerminalHResolveRoute where
  | exact
  | gain
  | blocked
  | unresolved
deriving DecidableEq, Repr

/-- Classify one supplied hereditary candidate in exact, gain, blocker, then
    unresolved priority order.  There is no caller-supplied route tag. -/
def terminalHResolveClassify {Candidate : Type}
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (candidate : Candidate) : TerminalHResolveRoute :=
  if exact candidate then .exact
  else if gain candidate then .gain
  else if blocked candidate then .blocked
  else .unresolved

/-- Exact classification is equivalent to the supplied exact predicate. -/
theorem terminalHResolveClassify_eq_exact_iff {Candidate : Type}
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (candidate : Candidate) :
    terminalHResolveClassify exact gain blocked candidate = .exact ↔
      exact candidate := by
  by_cases exactRoute : exact candidate
  · simp [terminalHResolveClassify, exactRoute]
  · by_cases gainRoute : gain candidate
    · simp [terminalHResolveClassify, exactRoute, gainRoute]
    · by_cases blockedRoute : blocked candidate
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]

/-- Gain classification is the first non-exact constructive route. -/
theorem terminalHResolveClassify_eq_gain_iff {Candidate : Type}
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (candidate : Candidate) :
    terminalHResolveClassify exact gain blocked candidate = .gain ↔
      ¬exact candidate ∧ gain candidate := by
  by_cases exactRoute : exact candidate
  · simp [terminalHResolveClassify, exactRoute]
  · by_cases gainRoute : gain candidate
    · simp [terminalHResolveClassify, exactRoute, gainRoute]
    · by_cases blockedRoute : blocked candidate
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]

/-- Blocked classification requires both constructive routes to be absent and
    a positive blocker certificate predicate. -/
theorem terminalHResolveClassify_eq_blocked_iff {Candidate : Type}
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (candidate : Candidate) :
    terminalHResolveClassify exact gain blocked candidate = .blocked ↔
      ¬exact candidate ∧ ¬gain candidate ∧ blocked candidate := by
  by_cases exactRoute : exact candidate
  · simp [terminalHResolveClassify, exactRoute]
  · by_cases gainRoute : gain candidate
    · simp [terminalHResolveClassify, exactRoute, gainRoute]
    · by_cases blockedRoute : blocked candidate
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]

/-- Unresolved is fail-closed: no constructive route and no positive blocker
    predicate were found for the candidate. -/
theorem terminalHResolveClassify_eq_unresolved_iff {Candidate : Type}
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (candidate : Candidate) :
    terminalHResolveClassify exact gain blocked candidate = .unresolved ↔
      ¬exact candidate ∧ ¬gain candidate ∧ ¬blocked candidate := by
  by_cases exactRoute : exact candidate
  · simp [terminalHResolveClassify, exactRoute]
  · by_cases gainRoute : gain candidate
    · simp [terminalHResolveClassify, exactRoute, gainRoute]
    · by_cases blockedRoute : blocked candidate
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]
      · simp [terminalHResolveClassify, exactRoute, gainRoute, blockedRoute]

/-! ## Finite-family NoHereditary ledger -/

/-- An explicit finite hereditary candidate enumeration.  Uniqueness is not a
    trusted field: the checker below recomputes `List.Nodup`. -/
structure TerminalHResolveFamily (Candidate : Type) where
  candidates : List Candidate

/-- The generated route ledger has exactly one computed row for every supplied
    candidate occurrence. -/
def TerminalHResolveFamily.routeLedger {Candidate : Type}
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked] :
    List (Candidate × TerminalHResolveRoute) :=
  family.candidates.map fun candidate =>
    (candidate, terminalHResolveClassify exact gain blocked candidate)

/-- Proposition recognized by the executable NoHereditary sidecar checker. -/
def TerminalHResolveFamily.NoHereditarySidecarAccepted {Candidate : Type}
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop) : Prop :=
  family.candidates.Nodup ∧
    ∀ candidate, candidate ∈ family.candidates →
      ¬exact candidate ∧ ¬gain candidate ∧ blocked candidate

/-- Recompute candidate uniqueness and every blocked route.  No caller can
    provide a sidecar-success flag or route tag. -/
def TerminalHResolveFamily.checkNoHereditarySidecar {Candidate : Type}
    [DecidableEq Candidate]
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked] : Bool :=
  decide family.candidates.Nodup &&
    family.candidates.all fun candidate =>
      decide (terminalHResolveClassify exact gain blocked candidate = .blocked)

/-- Every generated route-ledger row is tied to a supplied candidate and its
    recomputed classifier result. -/
theorem TerminalHResolveFamily.routeLedger_sound {Candidate : Type}
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    {row : Candidate × TerminalHResolveRoute}
    (member : row ∈ family.routeLedger exact gain blocked) :
    ∃ candidate, candidate ∈ family.candidates ∧
      row = (candidate, terminalHResolveClassify exact gain blocked candidate) := by
  rcases List.mem_map.mp member with ⟨candidate, candidateMember, rowEq⟩
  exact ⟨candidate, candidateMember, rowEq.symm⟩

/-- Every supplied candidate gets its computed route-ledger row. -/
theorem TerminalHResolveFamily.routeLedger_complete {Candidate : Type}
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    {candidate : Candidate}
    (member : candidate ∈ family.candidates) :
    (candidate, terminalHResolveClassify exact gain blocked candidate) ∈
      family.routeLedger exact gain blocked := by
  exact List.mem_map.mpr ⟨candidate, member, rfl⟩

/-- The Boolean sidecar boundary is exact: it accepts precisely a unique
    supplied enumeration whose every candidate has neither constructive route
    and carries a positive blocker predicate. -/
theorem TerminalHResolveFamily.checkNoHereditarySidecar_eq_true_iff
    {Candidate : Type} [DecidableEq Candidate]
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked] :
    family.checkNoHereditarySidecar exact gain blocked = true ↔
      family.NoHereditarySidecarAccepted exact gain blocked := by
  constructor
  · intro checked
    have checks :
        decide family.candidates.Nodup = true ∧
          family.candidates.all (fun candidate =>
            decide (terminalHResolveClassify exact gain blocked candidate =
              .blocked)) = true := by
      simpa only [TerminalHResolveFamily.checkNoHereditarySidecar,
        Bool.and_eq_true] using checked
    refine ⟨of_decide_eq_true checks.1, ?_⟩
    intro candidate member
    have routeChecked := (List.all_eq_true.mp checks.2) candidate member
    exact (terminalHResolveClassify_eq_blocked_iff
      exact gain blocked candidate).mp (of_decide_eq_true routeChecked)
  · rintro ⟨unique, everyBlocked⟩
    have allBlocked :
        family.candidates.all (fun candidate =>
          decide (terminalHResolveClassify exact gain blocked candidate =
            .blocked)) = true := by
      apply List.all_eq_true.mpr
      intro candidate member
      apply decide_eq_true
      exact (terminalHResolveClassify_eq_blocked_iff
        exact gain blocked candidate).mpr (everyBlocked candidate member)
    simpa only [TerminalHResolveFamily.checkNoHereditarySidecar,
      Bool.and_eq_true] using And.intro (decide_eq_true unique) allBlocked

/-- An accepted NoHereditary sidecar excludes an exact route for every
    candidate in the supplied finite family. -/
theorem TerminalHResolveFamily.not_exact_of_checkedNoHereditarySidecar
    {Candidate : Type} [DecidableEq Candidate]
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (accepted : family.checkNoHereditarySidecar exact gain blocked = true)
    {candidate : Candidate} (member : candidate ∈ family.candidates) :
    ¬exact candidate :=
  ((family.checkNoHereditarySidecar_eq_true_iff
    exact gain blocked).mp accepted).2 candidate member |>.1

/-- An accepted NoHereditary sidecar excludes a strict-gain route for every
    candidate in the supplied finite family. -/
theorem TerminalHResolveFamily.not_gain_of_checkedNoHereditarySidecar
    {Candidate : Type} [DecidableEq Candidate]
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (accepted : family.checkNoHereditarySidecar exact gain blocked = true)
    {candidate : Candidate} (member : candidate ∈ family.candidates) :
    ¬gain candidate :=
  ((family.checkNoHereditarySidecar_eq_true_iff
    exact gain blocked).mp accepted).2 candidate member |>.2.1

/-- Named endpoint for the bounded HResolve ledger: sidecar acceptance rules
    out both constructive routes for every candidate actually enumerated. -/
theorem terminal_hresolve_checked_sidecar_excludes_constructive_routes
    {Candidate : Type} [DecidableEq Candidate]
    (family : TerminalHResolveFamily Candidate)
    (exact gain blocked : Candidate → Prop)
    [DecidablePred exact] [DecidablePred gain] [DecidablePred blocked]
    (accepted : family.checkNoHereditarySidecar exact gain blocked = true) :
    ∀ candidate, candidate ∈ family.candidates →
      ¬exact candidate ∧ ¬gain candidate := by
  intro candidate member
  exact ⟨family.not_exact_of_checkedNoHereditarySidecar
      exact gain blocked accepted member,
    family.not_gain_of_checkedNoHereditarySidecar
      exact gain blocked accepted member⟩

end DirectWire
end PNP
