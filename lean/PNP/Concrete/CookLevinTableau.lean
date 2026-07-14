/-
Copyright (c) 2026 PNP Labs.

Exact bounded execution tableaux for the concrete finite-rule machine.

This file fixes the semantic object that later Cook--Levin clauses must
encode.  A tableau contains the ordinary raw-machine configurations, starts
from one fixed canonical input/certificate pair, and advances by the literal
first-match `step?` interpreter.  Missing transitions repeat the stuck
configuration, so a stuck nonhalting endpoint remains a timeout.

This file does not emit a CNF formula or claim a polynomial reduction.
-/

import PNP.Concrete.CookLevinLayout

namespace PNP.Concrete

namespace CookLevin

/-! ### Exact bounded traces -/

/-- Totalize one raw transition by repeating a halted or stuck endpoint. -/
def advance (machine : Machine) (config : Configuration) : Configuration :=
  match step? machine config with
  | none => config
  | some next => next

/-- The configurations strictly after the supplied initial configuration,
with exactly one entry per unit of fuel. -/
def traceTail (machine : Machine) : Nat → Configuration → List Configuration
  | 0, _ => []
  | fuel + 1, config =>
      let next := advance machine config
      next :: traceTail machine fuel next

/-- The complete bounded tableau, including time zero. -/
def trace (machine : Machine) (fuel : Nat)
    (initial : Configuration) : List Configuration :=
  initial :: traceTail machine fuel initial

theorem traceTail_length (machine : Machine) (fuel : Nat)
    (initial : Configuration) :
    (traceTail machine fuel initial).length = fuel := by
  induction fuel generalizing initial with
  | zero => rfl
  | succ fuel ih =>
      change Nat.succ (traceTail machine fuel (advance machine initial)).length =
        Nat.succ fuel
      exact congrArg Nat.succ (ih (advance machine initial))

theorem trace_length (machine : Machine) (fuel : Nat)
    (initial : Configuration) :
    (trace machine fuel initial).length = fuel + 1 := by
  change Nat.succ (traceTail machine fuel initial).length = fuel + 1
  rw [traceTail_length]

theorem run_succ_eq_run_advance (machine : Machine) (fuel : Nat)
    (config : Configuration) :
    run machine (fuel + 1) config =
      run machine fuel (advance machine config) := by
  unfold advance
  rw [run_succ]
  cases hStep : step? machine config with
  | none =>
      exact (run_eq_self_of_step?_eq_none machine config fuel hStep).symm
  | some next => rfl

/-- Fold a nonempty tableau tail to its final configuration. -/
def endpointFrom : Configuration → List Configuration → Configuration
  | current, [] => current
  | _, next :: rest => endpointFrom next rest

/-- Read a tableau endpoint, using the stated initial configuration only for
the impossible empty-tableau case. -/
def tableauEndpoint (initial : Configuration) :
    List Configuration → Configuration
  | [] => initial
  | first :: rest => endpointFrom first rest

theorem endpointFrom_traceTail (machine : Machine) (fuel : Nat)
    (initial : Configuration) :
    endpointFrom initial (traceTail machine fuel initial) =
      run machine fuel initial := by
  induction fuel generalizing initial with
  | zero => rfl
  | succ fuel ih =>
      change endpointFrom (advance machine initial)
          (traceTail machine fuel (advance machine initial)) =
        run machine (fuel + 1) initial
      rw [ih, run_succ_eq_run_advance]

theorem tableauEndpoint_trace (machine : Machine) (fuel : Nat)
    (initial : Configuration) :
    tableauEndpoint initial (trace machine fuel initial) =
      run machine fuel initial := by
  exact endpointFrom_traceTail machine fuel initial

/-! ### Intrinsic transition validity and uniqueness -/

/-- Every listed successor is the literal totalized raw successor of the
previous configuration. -/
def FollowsFrom (machine : Machine) :
    Configuration → List Configuration → Prop
  | _, [] => True
  | previous, next :: rest =>
      next = advance machine previous ∧ FollowsFrom machine next rest

/-- A bounded tableau starts at the stated configuration, contains exactly
`fuel` successors, and follows the concrete interpreter at every step. -/
def ValidTableau (machine : Machine) (initial : Configuration)
    (fuel : Nat) (tableau : List Configuration) : Prop :=
  ∃ rest,
    tableau = initial :: rest ∧
      rest.length = fuel ∧
      FollowsFrom machine initial rest

theorem traceTail_followsFrom (machine : Machine) (fuel : Nat)
    (initial : Configuration) :
    FollowsFrom machine initial (traceTail machine fuel initial) := by
  induction fuel generalizing initial with
  | zero => exact True.intro
  | succ fuel ih =>
      exact ⟨rfl, ih (advance machine initial)⟩

theorem canonicalTableau_valid (machine : Machine) (fuel : Nat)
    (initial : Configuration) :
    ValidTableau machine initial fuel (trace machine fuel initial) := by
  exact ⟨traceTail machine fuel initial, rfl,
    traceTail_length machine fuel initial,
    traceTail_followsFrom machine fuel initial⟩

theorem followsFrom_eq_traceTail (machine : Machine)
    (previous : Configuration) (rest : List Configuration)
    (hFollows : FollowsFrom machine previous rest) :
    rest = traceTail machine rest.length previous := by
  induction rest generalizing previous with
  | nil => rfl
  | cons next rest ih =>
      rcases hFollows with ⟨hNext, hRest⟩
      rw [hNext] at hRest
      change next :: rest =
        advance machine previous ::
          traceTail machine rest.length (advance machine previous)
      rw [hNext]
      exact congrArg (List.cons (advance machine previous))
        (ih (advance machine previous) hRest)

/-- Transition validity is complete and sound: for fixed machine, input, and
fuel there is exactly one valid tableau, namely the concrete execution trace.
-/
theorem validTableau_iff_eq_trace (machine : Machine)
    (initial : Configuration) (fuel : Nat) (tableau : List Configuration) :
    ValidTableau machine initial fuel tableau ↔
      tableau = trace machine fuel initial := by
  constructor
  · intro hValid
    rcases hValid with ⟨rest, hTableau, hLength, hFollows⟩
    rw [hTableau]
    change initial :: rest = initial :: traceTail machine fuel initial
    apply congrArg (List.cons initial)
    rw [followsFrom_eq_traceTail machine initial rest hFollows]
    rw [hLength]
  · intro hTableau
    rw [hTableau]
    exact canonicalTableau_valid machine fuel initial

theorem tableauEndpoint_of_valid (machine : Machine)
    (initial : Configuration) (fuel : Nat) (tableau : List Configuration)
    (hValid : ValidTableau machine initial fuel tableau) :
    tableauEndpoint initial tableau = run machine fuel initial := by
  rw [(validTableau_iff_eq_trace machine initial fuel tableau).mp hValid]
  exact tableauEndpoint_trace machine fuel initial

/-! ### Exact verdict transport for one fixed certificate -/

/-- Classify one already-computed raw configuration exactly as
`boundedDecide` classifies the endpoint of a run. -/
def configurationVerdict (machine : Machine)
    (config : Configuration) : Verdict :=
  if config.state == machine.acceptState then
    .accept
  else if config.state == machine.rejectState then
    .reject
  else
    .timeout

/-- Fixed source input, fixed certificate, and fixed raw transition budget.
The machine receives the same canonical pair used by the concrete NP model.
-/
structure FixedTableauInstance where
  machine : Machine
  input : BitString
  certificate : BitString
  fuel : Nat
deriving DecidableEq, Repr

namespace FixedTableauInstance

def rawInput (fixed : FixedTableauInstance) : BitString :=
  BitString.pair fixed.input fixed.certificate

def initial (fixed : FixedTableauInstance) : Configuration :=
  startConfig fixed.machine fixed.rawInput

def canonicalTableau (fixed : FixedTableauInstance) :
    List Configuration :=
  trace fixed.machine fixed.fuel fixed.initial

def Valid (fixed : FixedTableauInstance)
    (tableau : List Configuration) : Prop :=
  ValidTableau fixed.machine fixed.initial fixed.fuel tableau

def tableauVerdict (fixed : FixedTableauInstance)
    (tableau : List Configuration) : Verdict :=
  configurationVerdict fixed.machine
    (tableauEndpoint fixed.initial tableau)

def Accepting (fixed : FixedTableauInstance)
    (tableau : List Configuration) : Prop :=
  fixed.Valid tableau ∧ fixed.tableauVerdict tableau = .accept

theorem canonicalTableau_valid (fixed : FixedTableauInstance) :
    fixed.Valid fixed.canonicalTableau :=
  CookLevin.canonicalTableau_valid
    fixed.machine fixed.fuel fixed.initial

theorem valid_iff_eq_canonical (fixed : FixedTableauInstance)
    (tableau : List Configuration) :
    fixed.Valid tableau ↔ tableau = fixed.canonicalTableau :=
  validTableau_iff_eq_trace
    fixed.machine fixed.initial fixed.fuel tableau

theorem tableauEndpoint_of_valid (fixed : FixedTableauInstance)
    (tableau : List Configuration) (hValid : fixed.Valid tableau) :
    tableauEndpoint fixed.initial tableau =
      run fixed.machine fixed.fuel fixed.initial :=
  CookLevin.tableauEndpoint_of_valid
    fixed.machine fixed.initial fixed.fuel tableau hValid

theorem tableauVerdict_of_valid (fixed : FixedTableauInstance)
    (tableau : List Configuration) (hValid : fixed.Valid tableau) :
    fixed.tableauVerdict tableau =
      boundedDecide fixed.machine fixed.fuel fixed.rawInput := by
  unfold tableauVerdict configurationVerdict
  rw [tableauEndpoint_of_valid fixed tableau hValid]
  rfl

/-- For a fixed certificate, existential acceptance of a valid tableau is
exactly concrete finite-machine acceptance.  No proof certificate or host
oracle is an input to either direction. -/
theorem exists_accepting_iff_boundedDecide_accept
    (fixed : FixedTableauInstance) :
    (∃ tableau, fixed.Accepting tableau) ↔
      boundedDecide fixed.machine fixed.fuel fixed.rawInput =
        .accept := by
  constructor
  · intro existsTableau
    rcases existsTableau with ⟨tableau, hValid, hAccept⟩
    rw [tableauVerdict_of_valid fixed tableau hValid] at hAccept
    exact hAccept
  · intro hAccept
    refine ⟨fixed.canonicalTableau, fixed.canonicalTableau_valid, ?_⟩
    rw [tableauVerdict_of_valid fixed fixed.canonicalTableau
      fixed.canonicalTableau_valid]
    exact hAccept

end FixedTableauInstance

end CookLevin

end PNP.Concrete
