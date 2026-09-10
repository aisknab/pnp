/-
Copyright (c) 2026 PNP Labs.

Finite compilation of a fixed number of mixed-radix coordinate splits.
Radices and coordinates are tape data; only the split count and initial
register offset select the program. All original registers are preserved.

This supplies the shared arithmetic for rectangular region-local decoders.
It does not yet link the region entry, read input bits, construct all local
constraints or implement the complete Cook-Levin formula-builder loop.
-/

import PNP.Concrete.CookLevinBuilderRegionCoordinateDivision

namespace PNP.Concrete.CookLevin.BuilderRegionRadixDecoder

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

def doneMachine : WorkMachine :=
  { rules := [], startState := 0, acceptState := 0, rejectState := 1 }

/-- The count is fixed when the finite program is built, not read from its input. -/
def machine : Nat → Nat → WorkMachine
  | 0, _ => doneMachine
  | count + 1, offset => WorkMachineChain.machine (BuilderRegionCoordinateDivision.machine offset)
      (machine count (offset + 7))

/-- The first radix is nearest the coordinate in the initial physical frame. -/
def inputValues (older radices newer : List Nat) (coordinate : Nat) : List Nat :=
  older ++ radices.reverse ++ newer ++ [coordinate]

/-- Seven retained fields lie between the next radix and the new quotient. -/
def nextNewer (newer : List Nat) (coordinate radix : Nat) : List Nat :=
  radix :: (newer ++ [coordinate, 0, 0, (coordinate / radix) * radix, coordinate % radix, radix])

theorem nextNewer_length (newer : List Nat) (coordinate radix : Nat) :
    (nextNewer newer coordinate radix).length = newer.length + 7 := by
  simp only [nextNewer, List.length_cons, List.length_append, List.length_nil]

def finalValues (older : List Nat) : List Nat → List Nat → Nat → List Nat
  | [], newer, coordinate => older ++ newer ++ [coordinate]
  | radix :: rest, newer, coordinate =>
      finalValues older rest (nextNewer newer coordinate radix) (coordinate / radix)

def extraValues : List Nat → Nat → List Nat
  | [], _ => []
  | radix :: rest, coordinate => BuilderRegionCoordinateDivision.scratchValues coordinate radix ++
      extraValues rest (coordinate / radix)

def workSteps : List Nat → List Nat → Nat → Nat
  | [], _, _ => 0
  | radix :: rest, newer, coordinate => BuilderRegionCoordinateDivision.workSteps newer coordinate radix + 1 +
      workSteps rest (nextNewer newer coordinate radix) (coordinate / radix)

def initialConfiguration (offset : Nat) (older radices newer : List Nat)
    (coordinate : Nat) (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine radices.length offset)
    (endTape (inputValues older radices newer coordinate) workspace [])

def finalConfiguration (offset : Nat) (older radices newer : List Nat)
    (coordinate : Nat) (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := (machine radices.length offset).acceptState,
    tape := endTape (finalValues older radices newer coordinate) workspace [] }

theorem finalValues_eq (older radices newer : List Nat) (coordinate : Nat) :
    finalValues older radices newer coordinate =
      inputValues older radices newer coordinate ++ extraValues radices coordinate := by
  induction radices generalizing newer coordinate with
  | nil => simp only [finalValues, inputValues, extraValues, List.reverse_nil, List.append_nil]
  | cons radix rest ih =>
    rw [finalValues, ih]
    simp only [inputValues, nextNewer, extraValues, BuilderRegionCoordinateDivision.scratchValues,
      List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- Execute every requested split; radices and results never generate control. -/
theorem workRunExact (offset : Nat) (older radices newer : List Nat) (coordinate : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset)
    (hPositive : ∀ radix ∈ radices, 0 < radix) :
    workRunExact? (machine radices.length offset) (workSteps radices newer coordinate)
      (initialConfiguration offset older radices newer coordinate workspace) =
      some (finalConfiguration offset older radices newer coordinate workspace) := by
  induction radices generalizing offset newer coordinate with
  | nil =>
    simp only [initialConfiguration, finalConfiguration, workSteps, finalValues, inputValues,
      List.length_nil, machine, doneMachine, List.reverse_nil, List.append_nil,
      workRunExact?, workStartConfiguration]
  | cons radix rest ih =>
    have hRadix := hPositive radix List.mem_cons_self
    have hRest : ∀ value ∈ rest, 0 < value :=
      fun value hMem => hPositive value (List.mem_cons_of_mem radix hMem)
    have hNextLength : (nextNewer newer coordinate radix).length = offset + 7 := by
      rw [nextNewer_length, hLength]
    have hDivide := BuilderRegionCoordinateDivision.workRunExact offset (older ++ rest.reverse)
      newer coordinate radix workspace hLength hRadix
    have hNext := ih (offset + 7) (nextNewer newer coordinate radix) (coordinate / radix) hNextLength hRest
    have hFirst :
        workRunExact? (BuilderRegionCoordinateDivision.machine offset)
          (BuilderRegionCoordinateDivision.workSteps newer coordinate radix)
          (workStartConfiguration (BuilderRegionCoordinateDivision.machine offset)
            (endTape (inputValues older (radix :: rest) newer coordinate) workspace [])) =
          some {
            state := (BuilderRegionCoordinateDivision.machine offset).acceptState
            tape := endTape (inputValues older rest (nextNewer newer coordinate radix) (coordinate / radix)) workspace []
          } := by
      simpa only [BuilderRegionCoordinateDivision.initialConfiguration,
        BuilderRegionCoordinateDivision.finalConfiguration, BuilderRegionCoordinateDivision.inputValues,
        BuilderRegionCoordinateDivision.finalValues, BuilderRegionCoordinateDivision.scratchValues,
        inputValues, nextNewer, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using hDivide
    have hAll := chain_run (BuilderRegionCoordinateDivision.machine offset) (machine rest.length (offset + 7))
      (BuilderRegionCoordinateDivision.workSteps newer coordinate radix)
      (workSteps rest (nextNewer newer coordinate radix) (coordinate / radix)) _ _ _ hFirst hNext
    simpa only [machine, workSteps, initialConfiguration, finalConfiguration, finalValues, List.length_cons] using hAll

theorem run_compile_exact (offset : Nat) (older radices newer : List Nat) (coordinate : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset)
    (hPositive : ∀ radix ∈ radices, 0 < radix) :
    run (compileWorkMachine (machine radices.length offset)) (6 * workSteps radices newer coordinate)
      (encodeWorkConfiguration (initialConfiguration offset older radices newer coordinate workspace)) =
      encodeWorkConfiguration (finalConfiguration offset older radices newer coordinate workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact offset older radices newer coordinate workspace hLength hPositive)

theorem final_tape (offset : Nat) (older radices newer : List Nat) (coordinate : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration offset older radices newer coordinate workspace).tape =
      endTape (inputValues older radices newer coordinate ++ extraValues radices coordinate) workspace [] := by
  simp only [finalConfiguration, finalValues_eq]

def digits : List Nat → Nat → List Nat
  | [], _ => []
  | radix :: rest, coordinate => coordinate % radix :: digits rest (coordinate / radix)

def finalQuotient : List Nat → Nat → Nat
  | [], coordinate => coordinate
  | radix :: rest, coordinate => finalQuotient rest (coordinate / radix)

def reconstruct : List Nat → List Nat → Nat → Nat
  | [], _, quotient => quotient
  | _, [], quotient => quotient
  | radix :: rest, digit :: digits, quotient => digit + radix * reconstruct rest digits quotient

theorem digits_length (radices : List Nat) (coordinate : Nat) :
    (digits radices coordinate).length = radices.length := by
  induction radices generalizing coordinate with
  | nil => rfl
  | cons radix rest ih => simp only [digits, List.length_cons, ih]

theorem reconstruct_eq (radices : List Nat) (coordinate : Nat) :
    reconstruct radices (digits radices coordinate) (finalQuotient radices coordinate) = coordinate := by
  induction radices generalizing coordinate with
  | nil => rfl
  | cons radix rest ih =>
    simp only [reconstruct, digits, finalQuotient, ih]
    exact Nat.mod_add_div coordinate radix

/-- Read the remainder from each six-register result packet. This is a
specification of written data, not a runtime shortcut. -/
def packetDigits : List Nat → List Nat
  | _ :: _ :: _ :: digit :: _ :: _ :: rest => digit :: packetDigits rest
  | _ => []

theorem packetDigits_extraValues (radices : List Nat) (coordinate : Nat) :
    packetDigits (extraValues radices coordinate) = digits radices coordinate := by
  induction radices generalizing coordinate with
  | nil => rfl
  | cons radix rest ih =>
    simp only [extraValues, BuilderRegionCoordinateDivision.scratchValues,
      List.cons_append, List.nil_append, packetDigits, digits, ih]

theorem final_quotient (older radices newer : List Nat) (coordinate : Nat) :
    (finalValues older radices newer coordinate).reverse.headD 0 = finalQuotient radices coordinate := by
  induction radices generalizing newer coordinate with
  | nil =>
    simp only [finalValues, finalQuotient, List.reverse_append]
    rfl
  | cons radix rest ih => exact ih (nextNewer newer coordinate radix) (coordinate / radix)

theorem reconstruct_written_packets (older radices newer : List Nat) (coordinate : Nat) :
    reconstruct radices (packetDigits (extraValues radices coordinate))
      ((finalValues older radices newer coordinate).reverse.headD 0) = coordinate := by
  rw [packetDigits_extraValues, final_quotient]
  exact reconstruct_eq radices coordinate

/-- Every physical division appends its own six-field result packet. -/
theorem extraValues_length (radices : List Nat) (coordinate : Nat) :
    (extraValues radices coordinate).length = 6 * radices.length := by
  induction radices generalizing coordinate with
  | nil => rfl
  | cons radix rest ih =>
    simp only [extraValues, List.length_append, BuilderRegionCoordinateDivision.scratchValues,
      List.length_cons, List.length_nil, ih]
    omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧ program.acceptState ≠ program.rejectState

private theorem good (count offset : Nat) : Good (machine count offset) := by
  induction count generalizing offset with
  | zero =>
    change Good doneMachine
    refine ⟨List.Pairwise.nil, ?_, by decide⟩
    intro rule hMem
    cases hMem
  | succ count ih =>
    have hNext := ih (offset + 7)
    exact ⟨WorkMachineChain.rules_pairwise_query_distinct _ _
      (BuilderRegionCoordinateDivision.rules_pairwise_query_distinct offset) hNext.1
      (BuilderRegionCoordinateDivision.noRuleAtAccept offset),
      WorkMachineChain.noRuleAtAccept _ _ hNext.2.1,
      WorkMachineChain.machine_acceptState_ne_rejectState _ _ hNext.2.2⟩

theorem rules_pairwise_query_distinct (count offset : Nat) :
    (machine count offset).rules.Pairwise WorkMachineChain.QueryDistinct := (good count offset).1

theorem noRuleAtAccept (count offset : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine count offset) := (good count offset).2.1

theorem acceptState_ne_rejectState (count offset : Nat) :
    (machine count offset).acceptState ≠ (machine count offset).rejectState := (good count offset).2.2

theorem noRuleAtReject (count offset : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine count offset) (machine count offset).rejectState := by
  induction count generalizing offset with
  | zero => intro rule hMem; cases hMem
  | succ count ih =>
    exact WorkMachineChain.noRuleAtAccept (BuilderRegionCoordinateDivision.machine offset)
      { machine count (offset + 7) with acceptState := (machine count (offset + 7)).rejectState } (ih (offset + 7))

theorem nextNewer_span_le (newer : List Nat) (coordinate radix bound : Nat)
    (hNewer : newer.length + newer.sum ≤ bound) (hCoordinate : coordinate ≤ bound) (hRadix : radix ≤ bound) :
    (nextNewer newer coordinate radix).length + (nextNewer newer coordinate radix).sum ≤ 5 * bound + 7 := by
  have hReconstruct := BuilderRegionCoordinateDivision.quotient_remainder_reconstruct coordinate radix
  simp only [nextNewer, List.length_cons, List.length_append, List.length_nil,
    List.sum_cons, List.sum_append, List.sum_nil]
  omega

def workBound : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, bound => BuilderRegionCoordinateDivision.workBound bound + 1 + workBound count (5 * bound + 7)

theorem workSteps_le (radices newer : List Nat) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hNewer : newer.length + newer.sum ≤ bound)
    (hRadices : ∀ radix ∈ radices, radix ≤ bound)
    (hPositive : ∀ radix ∈ radices, 0 < radix) :
    workSteps radices newer coordinate ≤ workBound radices.length bound := by
  induction radices generalizing newer coordinate bound with
  | nil => exact Nat.le_refl _
  | cons radix rest ih =>
    have hRadix := hRadices radix List.mem_cons_self
    have hFirst := BuilderRegionCoordinateDivision.workSteps_le newer coordinate radix bound
      hCoordinate hRadix hNewer (hPositive radix List.mem_cons_self)
    have hCoordinate' : coordinate / radix ≤ 5 * bound + 7 :=
      Nat.le_trans (BuilderRegionCoordinateDivision.quotient_le coordinate radix) (by omega)
    have hNewer' := nextNewer_span_le newer coordinate radix bound hNewer hCoordinate hRadix
    have hRest : ∀ value ∈ rest, value ≤ 5 * bound + 7 := by
      intro value hMem
      have hValue := hRadices value (List.mem_cons_of_mem radix hMem)
      omega
    have hPositiveRest : ∀ value ∈ rest, 0 < value :=
      fun value hMem => hPositive value (List.mem_cons_of_mem radix hMem)
    have hNext := ih (nextNewer newer coordinate radix) (coordinate / radix) (5 * bound + 7)
      hCoordinate' hNewer' hRest hPositiveRest
    simp only [workSteps, workBound, List.length_cons]
    omega

theorem extraValues_span_le (radices : List Nat) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hRadices : ∀ radix ∈ radices, radix ≤ bound) :
    (extraValues radices coordinate).length + (extraValues radices coordinate).sum ≤
      radices.length * (3 * bound + 6) := by
  induction radices generalizing coordinate with
  | nil => simpa only [extraValues, List.length_nil, List.sum_nil, Nat.zero_mul, Nat.zero_add] using (Nat.le_refl 0)
  | cons radix rest ih =>
    have hFirst := BuilderRegionCoordinateDivision.scratch_span_le coordinate radix bound hCoordinate
      (hRadices radix List.mem_cons_self)
    have hNext := ih (coordinate / radix)
      (Nat.le_trans (BuilderRegionCoordinateDivision.quotient_le coordinate radix) hCoordinate)
      (fun value hMem => hRadices value (List.mem_cons_of_mem radix hMem))
    have hCount : (rest.length + 1) * (3 * bound + 6) =
        rest.length * (3 * bound + 6) + (3 * bound + 6) := Nat.succ_mul _ _
    simp only [extraValues, List.length_append, List.sum_append, List.length_cons]
    rw [hCount]
    omega

theorem final_register_span_le (older radices newer : List Nat) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hRadices : ∀ radix ∈ radices, radix ≤ bound) :
    (registerWord (finalValues older radices newer coordinate)).length ≤
      (registerWord (inputValues older radices newer coordinate)).length + radices.length * (3 * bound + 6) := by
  have hExtra := extraValues_span_le radices coordinate bound hCoordinate hRadices
  simp only [finalValues_eq, registerWord_append, List.length_append, registerWord_length]
  omega

private def nextBound (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 5) bound) (.constant 7)

def rawTimePolynomial : Nat → NatPolynomial → NatPolynomial
  | 0, _ => .constant 0
  | count + 1, bound => .add (BuilderRegionCoordinateDivision.rawTimePolynomial bound)
      (.add (.constant 6) (rawTimePolynomial count (nextBound bound)))

theorem rawTimePolynomial_eval (count : Nat) (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial count bound).eval input = 6 * workBound count (bound.eval input) := by
  induction count generalizing bound with
  | zero => rfl
  | succ count ih =>
    simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
      BuilderRegionCoordinateDivision.rawTimePolynomial_eval, ih, workBound, nextBound,
      NatPolynomial.eval_mul, Nat.mul_add, Nat.mul_one, Nat.add_assoc]

theorem rawTimePolynomial_le (radices newer : List Nat) (coordinate input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hNewer : newer.length + newer.sum ≤ bound.eval input)
    (hRadices : ∀ radix ∈ radices, radix ≤ bound.eval input) (hPositive : ∀ radix ∈ radices, 0 < radix) :
    6 * workSteps radices newer coordinate ≤ (rawTimePolynomial radices.length bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le radices newer coordinate (bound.eval input)
    hCoordinate hNewer hRadices hPositive)

end PNP.Concrete.CookLevin.BuilderRegionRadixDecoder
