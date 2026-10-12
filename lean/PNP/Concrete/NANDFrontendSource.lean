/-
Copyright (c) 2026 PNP Labs.

Complete raw circuit-reference reading. Source indices are derived from the
encoded reference and the preserved original input width, not supplied as
correctness premises.
-/

import PNP.Concrete.NANDFrontendUnary

namespace PNP.Concrete.NANDFrontend

open BitRegister

inductive SourceTag where
  | input | low | high | gate
deriving Repr

def SourceTag.token : SourceTag → LockedNAND.Token
  | .input => .input
  | .low => .constantFalse
  | .high => .constantTrue
  | .gate => .gate

def SourceTag.offset : SourceTag → Nat
  | .input => 45
  | .low => 46
  | .high => 47
  | .gate => 49

def SourceTag.setupFuel : SourceTag → Nat
  | .input => 1
  | .low => 1
  | .high => 2
  | .gate => 3

def SourceTag.seed : SourceTag → BitString → BitString
  | .input, _ => []
  | .low, inputs => inputs
  | .high, inputs => true :: inputs
  | .gate, inputs => true :: true :: inputs

def SourceTag.after : SourceTag → Nat → Nat → Nat
  | .input, base, _ => base + 52
  | .low, _, next => next
  | .high, _, next => next
  | .gate, base, _ => base + 52

def sourceTree (base failure : Nat) : ReadTree :=
  tokenTree failure failure failure (base + 45) (base + 46) (base + 47) (base + 49) failure
    failure failure failure failure failure failure failure failure

def sourceSetup (base : Nat) (operand : Operand) (next : Nat) : List (Instruction 9) :=
  [.clear operand.slot (base + 52),
   .copy operand.slot 1 next,
   .copy operand.slot 1 (base + 48),
   .push operand.slot true next,
   .copy operand.slot 1 (base + 50),
   .push operand.slot true (base + 51),
   .push operand.slot true (base + 52)]

def sourceCode (base : Nat) (operand : Operand) (next failure : Nat) : List (Instruction 9) :=
  (sourceTree base failure).code base failure ++ sourceSetup base operand next ++
    unaryCode (base + 52) operand next failure

theorem sourceCode_length (base : Nat) (operand : Operand) (next failure : Nat) :
    (sourceCode base operand next failure).length = 98 := rfl

theorem source_segments (program : Program 9) (base : Nat) (operand : Operand) (next failure : Nat)
    (placed : Segment program base (sourceCode base operand next failure)) :
    Segment program base ((sourceTree base failure).code base failure) ∧
      Segment program (base + 45) (sourceSetup base operand next) ∧
      Segment program (base + 52) (unaryCode (base + 52) operand next failure) := by
  have tree := Segment.head ((sourceTree base failure).code base failure)
    (sourceSetup base operand next ++ unaryCode (base + 52) operand next failure)
    (by simpa only [sourceCode, List.append_assoc] using placed)
  have setup := Segment.slice ((sourceTree base failure).code base failure)
    (sourceSetup base operand next) (unaryCode (base + 52) operand next failure) placed
  have unary := Segment.tail
    ((sourceTree base failure).code base failure ++ sourceSetup base operand next)
    (unaryCode (base + 52) operand next failure) placed
  rw [ReadTree.code_length] at setup
  rw [List.length_append, ReadTree.code_length] at unary
  exact ⟨tree, setup, unary⟩

theorem source_start (program : Program 9) (base : Nat) (operand : Operand)
    (next failure : Nat) (r : Registers) (tag : SourceTag) (rest : BitString)
    (placed : Segment program base (sourceCode base operand next failure)) :
    BitRegister.run program (8 + tag.setupFuel)
        (({r with input := tag.token.bits ++ rest}).state base) =
      (operand.write {r with input := rest} (tag.seed r.inputs)).state (tag.after base next) := by
  have segments := source_segments program base operand next failure placed
  have firstSteps : BitRegister.run program 8
      (({r with input := tag.token.bits ++ rest}).state base) =
        ({r with input := rest}).state (base + tag.offset) := by
    have h := ReadTree.run program (sourceTree base failure) base failure r
      (tag.token.bits ++ rest) segments.1
    cases tag <;> simpa only [SourceTag.token, SourceTag.offset, LockedNAND.Token.bits,
      List.cons_append, List.nil_append, sourceTree, tokenTree, ReadTree.scan, ReadTree.entry,
      Bool.false_eq_true, ↓reduceIte] using h
  have ps := segments.2.1
  have h45 : BitRegister.lookup program.code (base + 45) = some (.clear operand.slot (base + 52)) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 0 (by change 0 < 7; decide)
  have h46 : BitRegister.lookup program.code (base + 46) = some (.copy operand.slot 1 next) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 1 (by change 1 < 7; decide)
  have h47 : BitRegister.lookup program.code (base + 47) = some (.copy operand.slot 1 (base + 48)) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 2 (by change 2 < 7; decide)
  have h48 : BitRegister.lookup program.code (base + 48) = some (.push operand.slot true next) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 3 (by change 3 < 7; decide)
  have h49 : BitRegister.lookup program.code (base + 49) = some (.copy operand.slot 1 (base + 50)) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 4 (by change 4 < 7; decide)
  have h50 : BitRegister.lookup program.code (base + 50) = some (.push operand.slot true (base + 51)) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 5 (by change 5 < 7; decide)
  have h51 : BitRegister.lookup program.code (base + 51) = some (.push operand.slot true (base + 52)) := by
    simpa only [sourceSetup, BitRegister.lookup, Nat.add_assoc] using
      ps 6 (by change 6 < 7; decide)
  rw [BitRegister.run_add, firstSteps]
  cases tag <;> cases operand <;>
    simp only [SourceTag.setupFuel, SourceTag.offset, SourceTag.seed, SourceTag.after,
      BitRegister.run, BitRegister.step, Registers.state, h45, h46, h47, h48, h49, h50, h51,
      Instruction.execute, Instruction.nextControl, Instruction.update,
      Registers.store, Store.get, Store.set, Store.indexCases, Operand.slot, Operand.write]

structure SourceResult where
  fuel : Nat
  rest : BitString
  value : BitString
  valid : Bool
deriving Repr

def sourceAfter (tag : SourceTag) (inputs rest : BitString) : SourceResult :=
  match tag with
  | .input =>
      let u := unaryScan rest
      ⟨9 + u.fuel, u.rest, List.replicate u.added true, u.valid⟩
  | .low => ⟨9, rest, inputs, true⟩
  | .high => ⟨10, rest, true :: inputs, true⟩
  | .gate =>
      let u := unaryScan rest
      ⟨11 + u.fuel, u.rest, List.replicate u.added true ++ true :: true :: inputs, u.valid⟩

def sourceScan (inputs old : BitString) : BitString → SourceResult
  | false :: false :: true :: true :: rest => sourceAfter .input inputs rest
  | false :: true :: false :: false :: rest => sourceAfter .low inputs rest
  | false :: true :: false :: true :: rest => sourceAfter .high inputs rest
  | false :: true :: true :: false :: rest => sourceAfter .gate inputs rest
  | _ :: _ :: _ :: _ :: rest => ⟨8, rest, old, false⟩
  | input => ⟨2 * input.length + 1, [], old, false⟩

def sourceResultRegisters (operand : Operand) (r : Registers) (result : SourceResult) : Registers :=
  operand.write {r with input := result.rest} result.value

theorem source_tag_run (program : Program 9) (base : Nat) (operand : Operand)
    (next failure : Nat) (r : Registers) (tag : SourceTag) (rest : BitString)
    (placed : Segment program base (sourceCode base operand next failure)) :
    BitRegister.run program (sourceAfter tag r.inputs rest).fuel
        (({r with input := tag.token.bits ++ rest}).state base) =
      (sourceResultRegisters operand r (sourceAfter tag r.inputs rest)).state
        (readerExit (sourceAfter tag r.inputs rest).valid next failure) := by
  have start := source_start program base operand next failure r tag rest placed
  have pu := (source_segments program base operand next failure placed).2.2
  cases tag with
  | low => exact start
  | high => exact start
  | input =>
      change BitRegister.run program (9 + (unaryScan rest).fuel) _ = _
      simp only [SourceTag.setupFuel] at start
      rw [BitRegister.run_add, start]
      have h := unary_run program (base + 52) operand next failure (operand.write r []) rest pu
      simpa only [SourceTag.seed, SourceTag.after, sourceAfter, sourceResultRegisters,
        unaryResultRegisters, Operand.write_input, Operand.value_write,
        Operand.write_write, List.append_nil] using h
  | gate =>
      change BitRegister.run program (11 + (unaryScan rest).fuel) _ = _
      simp only [SourceTag.setupFuel] at start
      rw [BitRegister.run_add, start]
      have h := unary_run program (base + 52) operand next failure
        (operand.write r (true :: true :: r.inputs)) rest pu
      simpa only [SourceTag.seed, SourceTag.after, sourceAfter, sourceResultRegisters,
        unaryResultRegisters, Operand.write_input, Operand.value_write,
        Operand.write_write] using h

theorem source_run (program : Program 9) (base : Nat) (operand : Operand)
    (next failure : Nat) (r : Registers) (input : BitString)
    (placed : Segment program base (sourceCode base operand next failure)) :
    BitRegister.run program (sourceScan r.inputs (operand.value r) input).fuel
        (({r with input := input}).state base) =
      (sourceResultRegisters operand r (sourceScan r.inputs (operand.value r) input)).state
        (readerExit (sourceScan r.inputs (operand.value r) input).valid next failure) := by
  have treeRun := ReadTree.run program (sourceTree base failure) base failure r input
    (source_segments program base operand next failure placed).1
  match input with
  | [] =>
      simpa only [sourceScan, sourceTree, tokenTree, ReadTree.scan, ReadTree.entry,
        sourceResultRegisters, Operand.write_input, Operand.write_value, readerExit,
        List.length_nil] using treeRun
  | [a] =>
      cases a <;>
        simpa only [sourceScan, sourceTree, tokenTree, ReadTree.scan, ReadTree.entry,
          sourceResultRegisters, Operand.write_input, Operand.write_value, readerExit,
          Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil] using treeRun
  | [a, b] =>
      cases a <;> cases b <;>
        simpa only [sourceScan, sourceTree, tokenTree, ReadTree.scan, ReadTree.entry,
          sourceResultRegisters, Operand.write_input, Operand.write_value, readerExit,
          Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil] using treeRun
  | [a, b, c] =>
      cases a <;> cases b <;> cases c <;>
        simpa only [sourceScan, sourceTree, tokenTree, ReadTree.scan, ReadTree.entry,
          sourceResultRegisters, Operand.write_input, Operand.write_value, readerExit,
          Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil] using treeRun
  | a :: b :: c :: d :: rest =>
      cases a <;> cases b <;> cases c <;> cases d
      all_goals first
        | exact source_tag_run program base operand next failure r .input rest placed
        | exact source_tag_run program base operand next failure r .low rest placed
        | exact source_tag_run program base operand next failure r .high rest placed
        | exact source_tag_run program base operand next failure r .gate rest placed
        | simpa only [sourceScan, sourceTree, tokenTree, ReadTree.scan, ReadTree.entry,
            sourceResultRegisters, Operand.write_input, Operand.write_value, readerExit,
            Bool.false_eq_true, ↓reduceIte] using treeRun

theorem sourceScan_bounds (inputs old input : BitString) :
    (sourceScan inputs old input).fuel ≤ 3 * input.length + 1 ∧
      (sourceScan inputs old input).rest.length ≤ input.length := by
  match input with
  | [] => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | [a] => cases a <;> change 3 ≤ 4 ∧ 0 ≤ 1 <;> decide
  | [a, b] => cases a <;> cases b <;> change 5 ≤ 7 ∧ 0 ≤ 2 <;> decide
  | [a, b, c] => cases a <;> cases b <;> cases c <;> change 7 ≤ 10 ∧ 0 ≤ 3 <;> decide
  | a :: b :: c :: d :: rest =>
      have bounds := unaryScan_bounds rest
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp only [sourceScan, sourceAfter, List.length_cons] <;> constructor <;> omega

theorem sourceScan_success (inputs old input : BitString)
    (valid : (sourceScan inputs old input).valid = true) :
    (sourceScan inputs old input).rest.length < input.length ∧
      (sourceScan inputs old input).value.length ≤ inputs.length + input.length + 2 := by
  match input with
  | [] => cases valid
  | [a] => cases a <;> cases valid
  | [a, b] => cases a <;> cases b <;> cases valid
  | [a, b, c] => cases a <;> cases b <;> cases c <;> cases valid
  | a :: b :: c :: d :: rest =>
      have bounds := (unaryScan_bounds rest).2
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp only [sourceScan, sourceAfter, List.length_cons, List.length_append,
          List.length_replicate] at valid ⊢
      all_goals first
        | solve
          | cases valid
        | constructor <;> omega


theorem unaryWord_add (first second : Nat) :
    List.replicate (first + second) true =
      List.replicate first true ++ List.replicate second true := by
  induction first with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ first ih =>
      simpa only [Nat.succ_add, List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

def sourceReadFuel : LockedNAND.RawSource → Nat
  | .input index => 9 + (9 * index + 8)
  | .constant false => 9
  | .constant true => 10
  | .gate index => 11 + (9 * index + 8)

theorem sourceScan_canonical (inputs : Nat) (source : LockedNAND.RawSource)
    (old suffix : BitString) :
    sourceScan (List.replicate inputs true) old
        (LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens source) ++ suffix) =
      ⟨sourceReadFuel source, suffix, List.replicate (sourceIndex inputs source) true, true⟩ := by
  cases source with
  | input index =>
      simp only [LockedNAND.encodeSourceTokens, LockedNAND.encodeTokens, LockedNAND.Token.bits,
        List.cons_append, List.nil_append, sourceScan, sourceAfter, unaryScan_canonical,
        sourceReadFuel, sourceIndex]
  | constant bit =>
      cases bit <;>
        simp only [LockedNAND.encodeSourceTokens, LockedNAND.encodeTokens, LockedNAND.Token.bits,
          List.cons_append, List.nil_append, sourceScan, sourceAfter, sourceReadFuel,
          sourceIndex, List.replicate_succ]
  | gate index =>
      simp only [LockedNAND.encodeSourceTokens, LockedNAND.encodeTokens, LockedNAND.Token.bits,
        List.cons_append, List.nil_append, sourceScan, sourceAfter, unaryScan_canonical,
        sourceReadFuel, sourceIndex]
      rw [show inputs + 2 + index = index + (inputs + 1 + 1) by omega, unaryWord_add]
      rfl

end PNP.Concrete.NANDFrontend
