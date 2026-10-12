/-
Copyright (c) 2026 PNP Labs.

One closed finite frontend program joins the header, constants, full gate loop,
output validation and packing. Every source bitstring reaches acceptance with
an explicit successful record or the malformed-input data record.
-/

import PNP.Concrete.NANDFrontendOutput

namespace PNP.Concrete.NANDFrontend

open BitRegister

def program : Program 9 :=
  ⟨headerCode 0 113 666 ++ constantsCode 113 177 ++ gateLoopCode 177 492 666 ++
      outputCode 492 665 666 ++ [.accept, .clear 8 667, .push 8 false 668, .accept],
    0, 0, 8⟩

theorem program_code_length : program.code.length = 669 := by
  simp only [program, List.length_append, headerCode_length, constantsCode_length,
    gateLoopCode_length, outputCode_length]
  rfl

theorem program_segments :
    Segment program 0 (headerCode 0 113 666) ∧
      Segment program 113 (constantsCode 113 177) ∧
      Segment program 177 (gateLoopCode 177 492 666) ∧
      Segment program 492 (outputCode 492 665 666) ∧
      BitRegister.lookup program.code 665 = some .accept ∧
      BitRegister.lookup program.code 666 = some (.clear 8 667) ∧
      BitRegister.lookup program.code 667 = some (.push 8 false 668) ∧
      BitRegister.lookup program.code 668 = some .accept := by
  have whole : Segment program 0 (headerCode 0 113 666 ++
      (constantsCode 113 177 ++ (gateLoopCode 177 492 666 ++
        (outputCode 492 665 666 ++ [.accept, .clear 8 667, .push 8 false 668, .accept])))) := by
    simpa only [program, List.append_assoc] using Segment.full program
  have header := Segment.head _ _ whole
  have rest1 := Segment.tail _ _ whole
  rw [headerCode_length] at rest1
  change Segment program 113 _ at rest1
  have constants := Segment.head _ _ rest1
  have rest2 := Segment.tail _ _ rest1
  rw [constantsCode_length] at rest2
  change Segment program 177 _ at rest2
  have gates := Segment.head _ _ rest2
  have rest3 := Segment.tail _ _ rest2
  rw [gateLoopCode_length] at rest3
  change Segment program 492 _ at rest3
  have output := Segment.head _ _ rest3
  have ending := Segment.tail _ _ rest3
  rw [outputCode_length] at ending
  change Segment program 665 _ at ending
  exact ⟨header, constants, gates, output,
    ending 0 (by change 0 < 4; decide),
    ending 1 (by change 1 < 4; decide),
    ending 2 (by change 2 < 4; decide),
    ending 3 (by change 3 < 4; decide)⟩

def initialized (r : Registers) : Registers := withConstants (headerResult r).state

def afterTraversal (r : Registers) : BlockResult := gateLoopResult (initialized r)

def frontendResult (r : Registers) : BlockResult :=
  match (headerResult r).valid with
  | false => headerResult r
  | true =>
      match (afterTraversal r).valid with
      | false =>
          ⟨(headerResult r).fuel + (constantsFuel (headerResult r).state + (afterTraversal r).fuel),
            (afterTraversal r).state, false⟩
      | true =>
          let output := outputResult (afterTraversal r).state
          ⟨(headerResult r).fuel +
              (constantsFuel (headerResult r).state + ((afterTraversal r).fuel + output.fuel)),
            output.state, output.valid⟩

theorem frontend_result_run (r : Registers) :
    BitRegister.run program (frontendResult r).fuel (r.state 0) =
      (frontendResult r).state.state (readerExit (frontendResult r).valid 665 666) := by
  have ps := program_segments
  have header := header_result_run program 0 113 666 r ps.1
  have constants := constants_run program 113 177 (headerResult r).state ps.2.1
  change BitRegister.run program (constantsFuel (headerResult r).state)
    ((headerResult r).state.state 113) = (initialized r).state 177 at constants
  have loop := gateLoop_result_run program 177 492 666 (initialized r) ps.2.2.1
  change BitRegister.run program (afterTraversal r).fuel ((initialized r).state 177) =
    (afterTraversal r).state.state (readerExit (afterTraversal r).valid 492 666) at loop
  have output := output_result_run program 492 665 666 (afterTraversal r).state ps.2.2.2.1
  cases hh : (headerResult r).valid with
  | false => simpa only [frontendResult, hh, readerExit] using header
  | true =>
      simp only [hh, readerExit] at header
      cases hg : (afterTraversal r).valid with
      | false =>
          simp only [frontendResult, hh, hg, readerExit]
          rw [BitRegister.run_add, header, BitRegister.run_add, constants]
          simpa only [hg, readerExit] using loop
      | true =>
          simp only [hg, readerExit] at loop
          simp only [frontendResult, hh, hg]
          rw [BitRegister.run_add, header, BitRegister.run_add, constants,
            BitRegister.run_add, loop]
          exact output

def frontendFuel (r : Registers) : Nat :=
  (frontendResult r).fuel + readerExit (frontendResult r).valid 1 3

def frontendFinal (r : Registers) : Registers :=
  match (frontendResult r).valid with
  | false => {(frontendResult r).state with output := [false]}
  | true => (frontendResult r).state

theorem frontend_run (r : Registers) :
    BitRegister.run program (frontendFuel r) (r.state 0) =
      ⟨.accepted, (frontendFinal r).store⟩ := by
  have ps := program_segments
  unfold frontendFuel
  rw [BitRegister.run_add, frontend_result_run]
  cases valid : (frontendResult r).valid <;>
    simp only [readerExit, frontendFinal, valid, BitRegister.run, BitRegister.step, Registers.state,
      ps.2.2.2.2.1, ps.2.2.2.2.2.1, ps.2.2.2.2.2.2.1, ps.2.2.2.2.2.2.2,
      Instruction.execute, Instruction.nextControl, Instruction.update,
      Registers.store, Store.get, Store.set, Store.indexCases]

def initialRegisters (input : BitString) : Registers :=
  ⟨input, [], [], [], [], [], [], [], []⟩

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = (initialRegisters input).state 0 := rfl

theorem frontend_accepts (input : BitString) :
    (BitRegister.run program (frontendFuel (initialRegisters input))
      (BitRegister.initial program input)).control = .accepted := by
  rw [initial_registers, frontend_run]

theorem frontend_output (input : BitString) :
    (BitRegister.run program (frontendFuel (initialRegisters input))
      (BitRegister.initial program input)).store.get 8 = (frontendFinal (initialRegisters input)).output := by
  rw [initial_registers, frontend_run]
  rfl

end PNP.Concrete.NANDFrontend
