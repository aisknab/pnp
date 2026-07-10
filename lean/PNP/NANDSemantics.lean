/-
Copyright (c) 2026 PNP Labs.

Total, intrinsically topological semantics for finite direct-wire NAND programs.
Gate inputs can refer only to primary inputs, constants, or earlier gates.  A
direct-wire output word selects already available sources and therefore adds no
gates of its own.
-/

namespace PNP

/-- Boolean NAND, shared by the circuit semantics and the concrete macros. -/
def boolNand (a b : Bool) : Bool :=
  !(a && b)

namespace DirectWire

/-- A Boolean assignment indexed by a finite set. -/
abbrev Valuation (width : Nat) := Fin width → Bool

/-- The open Boolean function denoted by a circuit with free inputs. -/
abbrev OpenFunction (inputs outputs : Nat) :=
  Valuation inputs → Valuation outputs

/-- A source available before gate `gates` is appended. -/
inductive Source (inputs gates : Nat) where
  | input : Fin inputs → Source inputs gates
  | constant : Bool → Source inputs gates
  | gate : Fin gates → Source inputs gates
  deriving Repr, DecidableEq

/-- One NAND gate whose two sources are already available. -/
structure Gate (inputs priorGates : Nat) where
  left : Source inputs priorGates
  right : Source inputs priorGates
  deriving Repr, DecidableEq

/-- A program indexed by its exact gate count.  `snoc` enforces topology. -/
inductive Program (inputs : Nat) : Nat → Type where
  | empty : Program inputs 0
  | snoc {gates : Nat} :
      Program inputs gates → Gate inputs gates → Program inputs (gates + 1)

/-- Output wires indexed by their exact output width. -/
structure DirectWireWord (inputs gates outputs : Nat) where
  source : Fin outputs → Source inputs gates

/-- Add one final value to a finite valuation. -/
def Valuation.snoc {width : Nat} (earlier : Valuation width) (last : Bool) :
    Valuation (width + 1) := fun i =>
  if h : i.val < width then earlier ⟨i.val, h⟩ else last

@[simp] theorem Valuation.snoc_last {width : Nat}
    (earlier : Valuation width) (last : Bool) :
    Valuation.snoc earlier last (Fin.last width) = last := by
  unfold Valuation.snoc
  split
  · rename_i h
    exact False.elim (Nat.lt_irrefl width h)
  · rfl

@[simp] theorem Valuation.snoc_castSucc {width : Nat}
    (earlier : Valuation width) (last : Bool) (i : Fin width) :
    Valuation.snoc earlier last i.castSucc = earlier i := by
  unfold Valuation.snoc
  split
  · rfl
  · rename_i h
    exact False.elim (h i.isLt)

/-- Total interpretation of an already available source. -/
def Source.eval {inputs gates : Nat} (source : Source inputs gates)
    (input : Valuation inputs) (gateValues : Valuation gates) : Bool :=
  match source with
  | .input i => input i
  | .constant value => value
  | .gate i => gateValues i

/-- Total interpretation of one gate from the values available before it. -/
def Gate.eval {inputs gates : Nat} (gate : Gate inputs gates)
    (input : Valuation inputs) (gateValues : Valuation gates) : Bool :=
  boolNand (gate.left.eval input gateValues) (gate.right.eval input gateValues)

/-- Total evaluation of all gates in topological order. -/
def Program.eval {inputs gates : Nat} (program : Program inputs gates)
    (input : Valuation inputs) (i : Fin gates) : Bool :=
  match program with
  | .empty => Fin.elim0 i
  | .snoc initial gate =>
      let earlier : Valuation _ := fun j => Program.eval initial input j
      earlier.snoc (gate.eval input earlier) i

/-- The number of NAND gates represented by a program. -/
def Program.size {inputs gates : Nat} : Program inputs gates → Nat
  | .empty => 0
  | .snoc initial _ => initial.size + 1

/-- The gate-count size of an implementation pair; output wiring is free. -/
def DirectWireWord.size {inputs gates outputs : Nat}
    (_word : DirectWireWord inputs gates outputs) (program : Program inputs gates) : Nat :=
  program.size

@[simp] theorem DirectWireWord.size_eq_program {inputs gates outputs : Nat}
    (word : DirectWireWord inputs gates outputs) (program : Program inputs gates) :
    word.size program = program.size := rfl

@[simp] theorem Program.size_empty {inputs : Nat} :
    (Program.empty : Program inputs 0).size = 0 := rfl

@[simp] theorem Program.size_snoc {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates) :
    (Program.snoc initial gate).size = initial.size + 1 := rfl

theorem Program.size_eq_gateCount {inputs gates : Nat}
    (program : Program inputs gates) : program.size = gates := by
  induction program with
  | empty => rfl
  | snoc initial gate ih =>
      exact congrArg (fun size => size + 1) ih

theorem DirectWireWord.size_eq_gateCount {inputs gates outputs : Nat}
    (word : DirectWireWord inputs gates outputs) (program : Program inputs gates) :
    word.size program = gates := by
  exact Program.size_eq_gateCount program

/-- Appending a gate preserves every earlier gate value. -/
@[simp] theorem Program.eval_snoc_castSucc {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (input : Valuation inputs) (i : Fin gates) :
    (Program.snoc initial gate).eval input i.castSucc = initial.eval input i := by
  exact Valuation.snoc_castSucc (initial.eval input)
    (gate.eval input (initial.eval input)) i

/-- The newly appended position evaluates to the NAND of its two sources. -/
@[simp] theorem Program.eval_snoc_last {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (input : Valuation inputs) :
    (Program.snoc initial gate).eval input (Fin.last gates) =
      gate.eval input (initial.eval input) := by
  exact Valuation.snoc_last (initial.eval input)
    (gate.eval input (initial.eval input))

/-- Evaluate the free output wiring after all gates have been evaluated. -/
def DirectWireWord.eval {inputs gates outputs : Nat}
    (program : Program inputs gates) (word : DirectWireWord inputs gates outputs)
    (input : Valuation inputs) : Valuation outputs :=
  fun output => (word.source output).eval input (program.eval input)

/-- The open function denoted by a program and its free output wiring. -/
def semantics {inputs gates outputs : Nat}
    (program : Program inputs gates) (word : DirectWireWord inputs gates outputs) :
    OpenFunction inputs outputs :=
  fun input => word.eval program input

/-- Pointwise semantic equivalence allows implementations with different sizes. -/
def Equivalent {inputs outputs leftGates rightGates : Nat}
    (leftProgram : Program inputs leftGates)
    (leftWord : DirectWireWord inputs leftGates outputs)
    (rightProgram : Program inputs rightGates)
    (rightWord : DirectWireWord inputs rightGates outputs) : Prop :=
  ∀ input output,
    semantics leftProgram leftWord input output =
      semantics rightProgram rightWord input output

theorem Equivalent.refl {inputs outputs gates : Nat}
    (program : Program inputs gates) (word : DirectWireWord inputs gates outputs) :
    Equivalent program word program word := by
  intro input output
  rfl

theorem Equivalent.symm {inputs outputs leftGates rightGates : Nat}
    {leftProgram : Program inputs leftGates}
    {leftWord : DirectWireWord inputs leftGates outputs}
    {rightProgram : Program inputs rightGates}
    {rightWord : DirectWireWord inputs rightGates outputs}
    (equivalent : Equivalent leftProgram leftWord rightProgram rightWord) :
    Equivalent rightProgram rightWord leftProgram leftWord := by
  intro input output
  exact (equivalent input output).symm

theorem Equivalent.trans {inputs outputs firstGates secondGates thirdGates : Nat}
    {firstProgram : Program inputs firstGates}
    {firstWord : DirectWireWord inputs firstGates outputs}
    {secondProgram : Program inputs secondGates}
    {secondWord : DirectWireWord inputs secondGates outputs}
    {thirdProgram : Program inputs thirdGates}
    {thirdWord : DirectWireWord inputs thirdGates outputs}
    (firstSecond : Equivalent firstProgram firstWord secondProgram secondWord)
    (secondThird : Equivalent secondProgram secondWord thirdProgram thirdWord) :
    Equivalent firstProgram firstWord thirdProgram thirdWord := by
  intro input output
  exact (firstSecond input output).trans (secondThird input output)

/-- Output-only projections cost no NAND gates. -/
def projectionWord {inputs outputs : Nat} (pick : Fin outputs → Fin inputs) :
    DirectWireWord inputs 0 outputs :=
  ⟨fun output => .input (pick output)⟩

theorem projectionWord_spec {inputs outputs : Nat}
    (pick : Fin outputs → Fin inputs) (input : Valuation inputs) (output : Fin outputs) :
    semantics Program.empty (projectionWord pick) input output = input (pick output) := rfl

theorem projectionWord_zero_cost {inputs outputs : Nat}
    (pick : Fin outputs → Fin inputs) :
    (projectionWord pick).size (Program.empty : Program inputs 0) = 0 := by
  rfl

/-- Output constants cost no NAND gates. -/
def constantWord {inputs outputs : Nat} (value : Bool) :
    DirectWireWord inputs 0 outputs :=
  ⟨fun _ => .constant value⟩

theorem constantWord_spec {inputs outputs : Nat}
    (value : Bool) (input : Valuation inputs) (output : Fin outputs) :
    semantics Program.empty (constantWord value) input output = value := rfl

theorem constantWord_zero_cost {inputs outputs : Nat} (value : Bool) :
    (constantWord (inputs := inputs) (outputs := outputs) value).size Program.empty = 0 := by
  rfl

/-- Repeat any already available source into any number of outputs. -/
def repeatedSourceWord {inputs gates outputs : Nat} (wire : Source inputs gates) :
    DirectWireWord inputs gates outputs :=
  ⟨fun _ => wire⟩

theorem repeatedSourceWord_spec {inputs gates outputs : Nat}
    (program : Program inputs gates) (wire : Source inputs gates)
    (input : Valuation inputs) (output : Fin outputs) :
    semantics program (repeatedSourceWord wire) input output =
      wire.eval input (program.eval input) := rfl

theorem repeatedSourceWord_no_added_cost {inputs gates outputs : Nat}
    (program : Program inputs gates) (wire : Source inputs gates) :
    (repeatedSourceWord (outputs := outputs) wire).size program = program.size := by
  rfl

/-- The sole index of `Fin 1`, written without a type-class numeral instance. -/
def fin1Zero : Fin 1 :=
  ⟨0, Nat.zero_lt_succ 0⟩

/-- The first index of `Fin 2`. -/
def fin2Zero : Fin 2 :=
  ⟨0, Nat.zero_lt_succ 1⟩

/-- The second index of `Fin 2`. -/
def fin2One : Fin 2 :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

/-- A concrete zero-gate identity circuit. -/
def identityProgram : Program 1 0 := .empty

def identityWord : DirectWireWord 1 0 1 :=
  ⟨fun _ => .input fin1Zero⟩

theorem identityCircuit_spec (input : Valuation 1) :
    semantics identityProgram identityWord input fin1Zero = input fin1Zero := rfl

/-- A concrete one-gate, two-input NAND circuit. -/
def nandProgram : Program 2 1 :=
  .snoc .empty ⟨.input fin2Zero, .input fin2One⟩

def nandWord : DirectWireWord 2 1 1 :=
  ⟨fun _ => .gate fin1Zero⟩

theorem nandCircuit_size : nandProgram.size = 1 := rfl

theorem nandCircuit_spec (input : Valuation 2) :
    semantics nandProgram nandWord input fin1Zero =
      boolNand (input fin2Zero) (input fin2One) := rfl

/-- A concrete one-gate NOT circuit, using the input twice. -/
def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input fin1Zero, .input fin1Zero⟩

def notWord : DirectWireWord 1 1 1 :=
  ⟨fun _ => .gate fin1Zero⟩

theorem notCircuit_size : notProgram.size = 1 := rfl

theorem notCircuit_spec (input : Valuation 1) :
    semantics notProgram notWord input fin1Zero = !input fin1Zero := by
  change notProgram.eval input fin1Zero = !input fin1Zero
  rw [show fin1Zero = Fin.last 0 by rfl]
  unfold notProgram
  rw [Program.eval_snoc_last]
  change boolNand (input fin1Zero) (input fin1Zero) = !input fin1Zero
  cases input fin1Zero <;> rfl

/-- A concrete two-gate AND circuit: NAND followed by self-NAND. -/
def andProgram : Program 2 2 :=
  .snoc nandProgram ⟨.gate fin1Zero, .gate fin1Zero⟩

def andWord : DirectWireWord 2 2 1 :=
  ⟨fun _ => .gate fin2One⟩

theorem andCircuit_size : andProgram.size = 2 := rfl

theorem andCircuit_spec (input : Valuation 2) :
    semantics andProgram andWord input fin1Zero =
      (input fin2Zero && input fin2One) := by
  change andProgram.eval input fin2One = (input fin2Zero && input fin2One)
  rw [show fin2One = Fin.last 1 by rfl]
  unfold andProgram
  rw [Program.eval_snoc_last]
  change boolNand (nandProgram.eval input fin1Zero)
      (nandProgram.eval input fin1Zero) =
    (input fin2Zero && input fin2One)
  rw [show fin1Zero = Fin.last 0 by rfl]
  unfold nandProgram
  rw [Program.eval_snoc_last]
  change boolNand (boolNand (input fin2Zero) (input fin2One))
      (boolNand (input fin2Zero) (input fin2One)) =
    (input fin2Zero && input fin2One)
  cases input fin2Zero <;> cases input fin2One <;> rfl

/-- Proof-bearing summary of the foundational direct-wire semantics. -/
structure DirectWireSemanticsCertificate : Prop where
  sizeTracksIndex : ∀ {inputs gates} (program : Program inputs gates),
    program.size = gates
  wordSizeTracksIndex : ∀ {inputs gates outputs}
      (word : DirectWireWord inputs gates outputs) (program : Program inputs gates),
    word.size program = gates
  earlierValuesPreserved : ∀ {inputs gates} (initial : Program inputs gates)
      (gate : Gate inputs gates) (input : Valuation inputs) (i : Fin gates),
    (Program.snoc initial gate).eval input i.castSucc = initial.eval input i
  newGateEvaluated : ∀ {inputs gates} (initial : Program inputs gates)
      (gate : Gate inputs gates) (input : Valuation inputs),
    (Program.snoc initial gate).eval input (Fin.last gates) =
      gate.eval input (initial.eval input)
  equivalenceReflexive : ∀ {inputs outputs gates} (program : Program inputs gates)
      (word : DirectWireWord inputs gates outputs), Equivalent program word program word
  equivalenceSymmetric : ∀ {inputs outputs leftGates rightGates : Nat}
      {leftProgram : Program inputs leftGates}
      {leftWord : DirectWireWord inputs leftGates outputs}
      {rightProgram : Program inputs rightGates}
      {rightWord : DirectWireWord inputs rightGates outputs},
    Equivalent leftProgram leftWord rightProgram rightWord →
      Equivalent rightProgram rightWord leftProgram leftWord
  equivalenceTransitive : ∀ {inputs outputs firstGates secondGates thirdGates : Nat}
      {firstProgram : Program inputs firstGates}
      {firstWord : DirectWireWord inputs firstGates outputs}
      {secondProgram : Program inputs secondGates}
      {secondWord : DirectWireWord inputs secondGates outputs}
      {thirdProgram : Program inputs thirdGates}
      {thirdWord : DirectWireWord inputs thirdGates outputs},
    Equivalent firstProgram firstWord secondProgram secondWord →
      Equivalent secondProgram secondWord thirdProgram thirdWord →
      Equivalent firstProgram firstWord thirdProgram thirdWord
  projectionSemantics : ∀ {inputs outputs : Nat} (pick : Fin outputs → Fin inputs)
      (input : Valuation inputs) (output : Fin outputs),
    semantics Program.empty (projectionWord pick) input output = input (pick output)
  constantSemantics : ∀ {inputs outputs : Nat} (value : Bool)
      (input : Valuation inputs) (output : Fin outputs),
    semantics Program.empty (constantWord value) input output = value
  repeatedSourceSemantics : ∀ {inputs gates outputs : Nat}
      (program : Program inputs gates) (wire : Source inputs gates)
      (input : Valuation inputs) (output : Fin outputs),
    semantics program (repeatedSourceWord wire) input output =
      wire.eval input (program.eval input)
  projectionIsFree : ∀ {inputs outputs} (pick : Fin outputs → Fin inputs),
    (projectionWord pick).size (Program.empty : Program inputs 0) = 0
  constantsAreFree : ∀ {inputs outputs : Nat} (value : Bool),
    (constantWord (inputs := inputs) (outputs := outputs) value).size Program.empty = 0
  repeatedOutputsAddNoGates : ∀ {inputs gates outputs : Nat}
      (program : Program inputs gates) (wire : Source inputs gates),
    (repeatedSourceWord (outputs := outputs) wire).size program = program.size
  identitySemantics : ∀ input,
    semantics identityProgram identityWord input fin1Zero = input fin1Zero
  nandSemantics : ∀ input,
    semantics nandProgram nandWord input fin1Zero =
      boolNand (input fin2Zero) (input fin2One)
  notSemantics : ∀ input,
    semantics notProgram notWord input fin1Zero = !input fin1Zero
  andSemantics : ∀ input,
    semantics andProgram andWord input fin1Zero =
      (input fin2Zero && input fin2One)

/-- The checked certificate for the direct-wire NAND foundation. -/
def directWireSemanticsCertificate : DirectWireSemanticsCertificate :=
  { sizeTracksIndex := Program.size_eq_gateCount
    wordSizeTracksIndex := DirectWireWord.size_eq_gateCount
    earlierValuesPreserved := Program.eval_snoc_castSucc
    newGateEvaluated := Program.eval_snoc_last
    equivalenceReflexive := Equivalent.refl
    equivalenceSymmetric := Equivalent.symm
    equivalenceTransitive := Equivalent.trans
    projectionSemantics := projectionWord_spec
    constantSemantics := constantWord_spec
    repeatedSourceSemantics := repeatedSourceWord_spec
    projectionIsFree := projectionWord_zero_cost
    constantsAreFree := constantWord_zero_cost
    repeatedOutputsAddNoGates := repeatedSourceWord_no_added_cost
    identitySemantics := identityCircuit_spec
    nandSemantics := nandCircuit_spec
    notSemantics := notCircuit_spec
    andSemantics := andCircuit_spec }

end DirectWire
end PNP
