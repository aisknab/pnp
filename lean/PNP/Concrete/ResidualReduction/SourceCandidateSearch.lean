import PNP.Concrete.ResidualReduction.SourceCandidateLoad
import PNP.Concrete.ResidualReduction.SourceGlobalSelector

/-! An actual ordered first-success loop. The generic execution proof is
instantiated with the closed line and plane programs; its query contract is
not a new proof authority. A success clears the pending stream immediately.
Empty and all-failing searches return a freshly initialised absent answer. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateSearch
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held full)
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)

def words {α : Type} (encode : α → BitString) : List α → BitString
  | [] => []
  | a :: rest => encode a ++ words encode rest
def optional {β : Type} (payload : β → BitString) : Option β → BitString
  | none => [false]
  | some value => true :: payload value
def first {α β : Type} (answer : α → Option β) : List α → Option (α × β)
  | [] => none
  | a :: rest => match answer a with
    | none => first answer rest
    | some value => some (a,value)
def current (base : Data) (normal packet output : BitString) : Data :=
  {base with normals := normal, packet := packet, output := output}
def Correct {α β : Type} (base : Data) (encode : α → BitString) (payload : β → BitString)
    (hit : Option (α × β)) (d : Data) : Prop :=
  d.dimension = base.dimension ∧ d.count = base.count ∧ d.family = base.family ∧
    match hit with
    | none => d.output = [false]
    | some (a,value) => d.normals = encode a ∧ d.output = true :: payload value

theorem first_exact {α β : Type} (answer : α → Option β) (xs : List α) :
    first answer xs =
      SourceChain.firstSome (fun a => (answer a).map (fun value => (a,value))) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : answer a <;> simp only [first, SourceChain.firstSome, h, Option.map_none,
      Option.map_some, ih]

theorem first_map {α β γ : Type} (answer : α → Option β) (f : α × β → γ) (xs : List α) :
    (first answer xs).map f =
      SourceChain.firstSome (fun a => (answer a).map (fun value => f (a,value))) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : answer a <;> simp only [first, SourceChain.firstSome, h, Option.map_none,
      Option.map_some, ih]

theorem pending_get (r : Store 38) (d : Data) (t : Held) : (full r d t).get 44 = t.pending :=
  Frame.get_frame (SourceSelectionInvocation.full r d) t.store 0
theorem output_get (r : Store 38) (d : Data) (t : Held) : (full r d t).get 43 = d.output := by
  have first := Frame.get_core (SourceSelectionInvocation.full r d) t.store (43 : Fin 44)
  have second := Frame.get_frame r d.store (5 : Fin 6)
  exact first.trans second

private theorem set_saved {extra count : Nat} (core : Store count) (frame : Store extra)
    (i : Fin extra) (word : BitString) :
    (Frame.join core frame).set (Frame.frameIndex count i) word =
      Frame.join core (frame.set i word) := by
  induction core with
  | nil =>
    have position : Frame.frameIndex 0 i = i := by
      apply Fin.ext
      exact Nat.zero_add i.val
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) i = (Frame.frameIndex count i).succ := by
      apply Fin.ext
      change count + 1 + i.val = count + i.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

private theorem clear_saved {count extra : Nat} (r : Store count) (d : Store extra) (i : Fin extra) :
    Exec (.action (.clear (Frame.frameIndex count i))) (Frame.join r d) 1
      (Frame.join r (d.set i [])) := by
  have checked := Exec.action (.clear (Frame.frameIndex count i)) (Frame.join r d)
  simpa only [Action.update, Action.instruction, Instruction.update, set_saved] using checked
private theorem push_saved {count extra : Nat} (r : Store count) (d : Store extra)
    (i : Fin extra) (b : Bool) :
    Exec (.action (.push (Frame.frameIndex count i) b)) (Frame.join r d) 1
      (Frame.join r (d.set i (b :: d.get i))) := by
  have checked := Exec.action (.push (Frame.frameIndex count i) b) (Frame.join r d)
  simpa only [Action.update, Action.instruction, Instruction.update, Frame.get_frame,
    set_saved] using checked

def initialise : Block 46 :=
  Frame.block 2 (.seq (.action (.clear (43 : Fin 44))) (.action (.push 43 false)))
theorem initialise_exec (r : Store 38) (d : Data) (t : Held) :
    Exec initialise (full r d t) 2 (full r {d with output := [false]} t) := by
  have first := clear_saved r d.store (5 : Fin 6)
  have second := push_saved r ({d with output := []} : Data).store (5 : Fin 6) false
  exact Frame.execution (Exec.seq first second) t.store

def decision : Block 46 := .branch 43 .skip .skip (.action (.clear 44))
theorem decision_none (r : Store 38) (d : Data) (t : Held) (h : d.output = [false]) :
    Exec decision (full r d t) 2 (full r d t) :=
  Exec.zero ((output_get r d t).trans h) (.skip _)
theorem decision_some (r : Store 38) (d : Data) (t : Held) (rest : BitString)
    (h : d.output = true :: rest) :
    Exec decision (full r d t) 2 (full r d {t with pending := []}) :=
  Exec.one ((output_get r d t).trans h)
    (clear_saved (SourceSelectionInvocation.full r d) t.store 0)

def step (query : Block 44) : Block 46 :=
  .seq SourceCandidateLoad.block (.seq (Frame.block 2 query) decision)
def loop (query : Block 44) : Block 46 := .loop 44 (step query)
def block (query : Block 44) : Block 46 := .seq initialise (loop query)
def loopBound (width budget count : Nat) : Nat :=
  (SourceCandidateLoad.fuel width + budget + 3) * count + 1

def QueryContract {α β : Type} (query : Block 44) (base : Data)
    (encode : α → BitString) (answer : α → Option β) (payload : β → BitString)
    (budget : Nat) : Prop :=
  ∀ a (r : Store 38) packet, ∃ used after,
    Exec query (SourceSelectionInvocation.full r (current base (encode a) packet [false])) used
      (SourceSelectionInvocation.full after
        (SourceSelectionInvocation.returned (current base (encode a) packet [false])
          (optional payload (answer a)))) ∧ used ≤ budget

theorem words_present {α : Type} (encode : α → BitString) (a : α) (xs : List α)
    (width : Nat) (positive : 0 < width) (size : (encode a).length = width) :
    ∃ bit rest, words encode (a :: xs) = bit :: rest := by
  cases h : encode a with
  | nil =>
    rw [h] at size
    exact False.elim (by simp only [List.length_nil] at size; omega)
  | cons bit rest => exact ⟨bit, rest ++ words encode xs, by rw [words,h]; rfl⟩

theorem loop_exec {α β : Type} (query : Block 44) (base : Data) (encode : α → BitString)
    (answer : α → Option β) (payload : β → BitString) (width budget : Nat)
    (positive : 0 < width) (checked : QueryContract query base encode answer payload budget)
    (xs : List α) :
    ∀ (r : Store 38) normal packet, (∀ a ∈ xs, (encode a).length = width) →
    ∃ used after d,
      Exec (loop query) (full r (current base normal packet [false])
        ⟨words encode xs, List.replicate width true⟩) used
        (full after d ⟨[],List.replicate width true⟩) ∧
      Correct base encode payload (first answer xs) d ∧ used ≤ loopBound width budget xs.length := by
  induction xs with
  | nil =>
    intro r normal packet _
    refine ⟨1,r,current base normal packet [false],Exec.loopStop (pending_get _ _ _),?_,?_⟩
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · simp only [loopBound,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons a xs ih =>
    intro r normal packet sizes
    have size := sizes a List.mem_cons_self
    have sizes' : ∀ b ∈ xs, (encode b).length = width :=
      fun b hb => sizes b (List.mem_cons_of_mem a hb)
    let before := current base (encode a) packet [false]
    let core := SourceCandidateLoad.core (SourceCandidateLoad.loaded (encode a) (words encode xs))
    have loaded := SourceCandidateLoad.block_exec r (current base normal packet [false])
      (encode a) (words encode xs)
    rw [size] at loaded
    obtain ⟨used,middle,call,headBound⟩ := checked a core packet
    have called := Frame.execution call (Held.store ⟨words encode xs,List.replicate width true⟩)
    obtain ⟨bit,tail,nonempty⟩ := words_present encode a xs width positive size
    have present : (full r (current base normal packet [false])
        ⟨words encode (a :: xs),List.replicate width true⟩).get 44 = bit :: tail :=
      (pending_get _ _ _).trans nonempty
    cases h : answer a with
    | none =>
      simp only [h,optional] at called
      let next := current base (encode a) (SourceSelectionInvocation.word before) [false]
      have choose := decision_none middle next ⟨words encode xs,List.replicate width true⟩ rfl
      have head : Exec (step query) (full r (current base normal packet [false])
          ⟨words encode (a :: xs),List.replicate width true⟩)
          (SourceCandidateLoad.fuel width + (used + 2))
          (full middle next ⟨words encode xs,List.replicate width true⟩) :=
        Exec.seq loaded (Exec.seq called choose)
      obtain ⟨tailUsed,last,d,rest,correct,tailBound⟩ :=
        ih middle (encode a) (SourceSelectionInvocation.word before) sizes'
      refine ⟨1 + (SourceCandidateLoad.fuel width + (used + 2) + tailUsed),last,d,
        Exec.loopStep present head rest,?_,?_⟩
      · simpa only [first,h] using correct
      · simp only [loopBound,List.length_cons,Nat.mul_add,Nat.mul_one] at tailBound ⊢
        omega
    | some value =>
      simp only [h,optional] at called
      let next := current base (encode a) (SourceSelectionInvocation.word before) (true :: payload value)
      have choose := decision_some middle next ⟨words encode xs,List.replicate width true⟩
        (payload value) rfl
      have head : Exec (step query) (full r (current base normal packet [false])
          ⟨words encode (a :: xs),List.replicate width true⟩)
          (SourceCandidateLoad.fuel width + (used + 2))
          (full middle next ⟨[],List.replicate width true⟩) :=
        Exec.seq loaded (Exec.seq called choose)
      have stopped : Exec (loop query) (full middle next ⟨[],List.replicate width true⟩) 1
          (full middle next ⟨[],List.replicate width true⟩) := Exec.loopStop (pending_get _ _ _)
      refine ⟨1 + (SourceCandidateLoad.fuel width + (used + 2) + 1),middle,next,
        Exec.loopStep present head stopped,?_,?_⟩
      · exact ⟨rfl,rfl,rfl,by simp only [first,h]; exact ⟨rfl,rfl⟩⟩
      · simp only [loopBound,List.length_cons,Nat.mul_add,Nat.mul_one]
        omega

theorem block_exec {α β : Type} (query : Block 44) (base : Data) (encode : α → BitString)
    (answer : α → Option β) (payload : β → BitString) (width budget : Nat)
    (positive : 0 < width) (checked : QueryContract query base encode answer payload budget)
    (xs : List α) (sizes : ∀ a ∈ xs, (encode a).length = width)
    (r : Store 38) (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec (block query) (full r (current base normal packet oldOutput)
        ⟨words encode xs,List.replicate width true⟩) used
        (full after d ⟨[],List.replicate width true⟩) ∧
      Correct base encode payload (first answer xs) d ∧
      used ≤ 2 + loopBound width budget xs.length := by
  have init := initialise_exec r (current base normal packet oldOutput)
    ⟨words encode xs,List.replicate width true⟩
  obtain ⟨used,after,d,rest,correct,bound⟩ :=
    loop_exec query base encode answer payload width budget positive checked xs r normal packet sizes
  exact ⟨2 + used,after,d,Exec.seq init rest,correct,by omega⟩

end PNP.Concrete.ResidualReduction.SourceCandidateSearch
