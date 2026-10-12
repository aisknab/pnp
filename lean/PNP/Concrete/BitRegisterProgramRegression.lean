import PNP.Concrete.BitRegisterProgram

open PNP.Concrete
open PNP.Concrete.BitRegister

private def testProgram : Program 2 :=
  { code := [.copy 1 0 1, .push 1 true 2, .pop 1 3, .accept]
    entry := 0
    input := 0
    output := 1 }

example : (run testProgram 4 (initial testProgram [false, true])).control =
    .accepted := rfl
example : (run testProgram 4 (initial testProgram [false, true])).store.get 1 =
    [false, true] := rfl
example : (run testProgram 4 (initial testProgram [false, true])).store.get 0 =
    [false, true] := rfl
example : (run testProgram 3 (initial testProgram [])).control = .running 3 := rfl
example : (run testProgram 4 (initial testProgram [])).store.get 1 = [] := rfl
example : (run testProgram 100 (initial testProgram [true])).store.get 1 = [true] := by
  have hfour : run testProgram 4 (initial testProgram [true]) =
      ⟨.accepted, Store.cons [true] (Store.cons [true] Store.nil)⟩ := rfl
  change (run testProgram (4 + 96) (initial testProgram [true])).store.get 1 = [true]
  rw [BitRegister.run_add, hfour, run_accepted]
  rfl

private def branching : Program 1 :=
  { code := [.branch 0 1 2 3, .accept, .reject, .pop 0 1]
    entry := 0, input := 0, output := 0 }

example : (run branching 2 (initial branching [])).control = .accepted := rfl
example : (run branching 2 (initial branching [false])).control = .rejected := rfl
example : (run branching 3 (initial branching [true, false])).store.get 0 =
    [false] := rfl
example : (run branching 3 (initial branching [true])).control = .accepted := rfl

private def invalidJump : Program 1 :=
  { code := [.jump 7], entry := 0, input := 0, output := 0 }

example : (run invalidJump 1 (initial invalidJump [])).control = .running 7 := rfl
example : (run invalidJump 2 (initial invalidJump [])).control = .rejected := rfl

private def aliasing : Program 1 :=
  { code := [.copy 0 0 1, .clear 0 2, .pop 0 3, .accept]
    entry := 0, input := 0, output := 0 }

example : (run aliasing 1 (initial aliasing [true, false])).store.get 0 =
    [true, false] := rfl
example : (run aliasing 4 (initial aliasing [true, false])).store.get 0 = [] := rfl
example : (Store.cons [] (Store.cons [false, true] Store.nil)).encode =
    [Store.separator, Store.bitSymbol false, Store.bitSymbol true, Store.separator] := rfl

#print axioms Store.bounded_mono
#print axioms Store.get_length_le
#print axioms Store.set_bounded
#print axioms Store.get_set_same
#print axioms Store.span_le
#print axioms Store.encode_length
#print axioms Store.initialTape_span_le
#print axioms Instruction.update_bounded
#print axioms initial_bounded
#print axioms step_bounded
#print axioms run_bounded
#print axioms BitRegister.run_add
#print axioms run_accepted
#print axioms run_rejected
#print axioms input_run_encoded_span
#print axioms input_run_tape_span
