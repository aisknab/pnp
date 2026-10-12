/-
Copyright (c) 2026 PNP Labs.

One encoded-input polynomial covers all internally derived cut fields.
The bound includes matching, terminal exploration, both derived counts and
both selections. Store growth is charged between phases, including scratch.
Malformed raw inputs are covered as well as canonical formula packets.
-/
import PNP.Concrete.NormalizerCutPrepared

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister

attribute [local irreducible] MatchingDriver.State.store

theorem initial_bounded (input : BitString) : (initial input).store.Bounded input.length := by
  have core := BitRegister.initial_bounded CutTrace.program input
  rw [CutTrace.initial_registers] at core
  dsimp only [initial, State.store, State.frame]
  exact Frame.join_bounded _ _ core (Store.empty_bounded 3 input.length)

attribute [local irreducible] State.store

def initializeSize : NatPolynomial := .add (.linear 1 0) CutTrace.sourceFuel
def clausesFuel : NatPolynomial := clausesBound.substitute initializeSize
def afterClausesSize : NatPolynomial := .add initializeSize clausesFuel
def variablesFuel : NatPolynomial := variablesBound.substitute afterClausesSize
def prepareFuel : NatPolynomial := .add CutTrace.sourceFuel (.add clausesFuel variablesFuel)
def prepareSize : NatPolynomial := .add (.linear 1 0) prepareFuel

theorem initializeSize_eval (size : Nat) :
    initializeSize.eval size = size + CutTrace.sourceFuel.eval size := by
  change (1 * size + 0) + CutTrace.sourceFuel.eval size = _
  rw [Nat.one_mul, Nat.add_zero]
theorem clausesFuel_eval (size : Nat) :
    clausesFuel.eval size = clausesBound.eval (initializeSize.eval size) :=
  NatPolynomial.eval_substitute _ _ _
theorem afterClausesSize_eval (size : Nat) :
    afterClausesSize.eval size = initializeSize.eval size + clausesFuel.eval size := rfl
theorem variablesFuel_eval (size : Nat) :
    variablesFuel.eval size = variablesBound.eval (afterClausesSize.eval size) :=
  NatPolynomial.eval_substitute _ _ _
theorem prepareFuel_eval (size : Nat) :
    prepareFuel.eval size = CutTrace.sourceFuel.eval size + (clausesFuel.eval size + variablesFuel.eval size) := rfl
theorem prepareSize_eval (size : Nat) :
    prepareSize.eval size = size + prepareFuel.eval size := by
  change (1 * size + 0) + prepareFuel.eval size = _
  rw [Nat.one_mul, Nat.add_zero]

theorem initializeSteps_bound (input : BitString) :
    initializeSteps input ≤ CutTrace.sourceFuel.eval input.length :=
  CutTrace.sourceSteps_bound input
theorem initialized_bounded (input : BitString) :
    (initialized input).store.Bounded (initializeSize.eval input.length) := by
  have executed := (initialize_exec input).bounded input.length (initial_bounded input)
  apply Store.bounded_mono (store := (initialized input).store) executed
  rw [initializeSize_eval]
  exact Nat.add_le_add_left (initializeSteps_bound input) input.length
theorem clausesSteps_input_bound (input : BitString) :
    clausesSteps (initialized input) ≤ clausesFuel.eval input.length := by
  rw [clausesFuel_eval]
  exact clausesSteps_bound (initialized input) (initializeSize.eval input.length) (initialized_bounded input)
theorem afterClauses_bounded (input : BitString) :
    (afterClauses input).store.Bounded (afterClausesSize.eval input.length) := by
  have executed := (deriveClauses_exec (initialized input)).bounded
    (initializeSize.eval input.length) (initialized_bounded input)
  apply Store.bounded_mono (store := (afterClauses input).store) executed
  rw [afterClausesSize_eval]
  exact Nat.add_le_add_left (clausesSteps_input_bound input) _
theorem variablesSteps_input_bound (input : BitString) :
    variablesSteps (afterClauses input) ≤ variablesFuel.eval input.length := by
  rw [variablesFuel_eval]
  exact variablesSteps_bound (afterClauses input) (afterClausesSize.eval input.length) (afterClauses_bounded input)
theorem prepareSteps_bound (input : BitString) :
    prepareSteps input ≤ prepareFuel.eval input.length := by
  rw [prepareFuel_eval]
  exact Nat.add_le_add (initializeSteps_bound input)
    (Nat.add_le_add (clausesSteps_input_bound input) (variablesSteps_input_bound input))
theorem prepared_bounded (input : BitString) :
    (prepared input).store.Bounded (prepareSize.eval input.length) := by
  have executed := (prepare_exec input).bounded input.length (initial_bounded input)
  apply Store.bounded_mono (store := (prepared input).store) executed
  rw [prepareSize_eval]
  exact Nat.add_le_add_left (prepareSteps_bound input) input.length

end PNP.Concrete.NormalizerBlocks.CutDriver
