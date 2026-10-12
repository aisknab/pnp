/-
Copyright (c) 2026 PNP Labs.

Copy lowering to a closed finite instruction table with one compiler-owned
scratch register. The two loops preserve bit order, restore the source, and
leave scratch empty. Copying a register onto itself is the identity path.

The exact bound below counts finite register instructions. Concrete tape
costs must still be obtained through the all-instruction simulation; this
module alone is not a tape-runtime theorem.
-/

import PNP.Concrete.BitRegisterProgram

namespace PNP.Concrete.BitRegister

namespace Store

@[simp] theorem get_cons_zero {count : Nat} (first : BitString) (rest : Store count) :
    (Store.cons first rest).get (0 : Fin (count + 1)) = first := by rfl

@[simp] theorem get_cons_succ {count : Nat} (first : BitString) (rest : Store count)
    (index : Fin count) : (Store.cons first rest).get index.succ = rest.get index := by rfl

@[simp] theorem set_cons_zero {count : Nat} (first : BitString) (rest : Store count)
    (value : BitString) :
    (Store.cons first rest).set (0 : Fin (count + 1)) value = Store.cons value rest := by rfl

@[simp] theorem set_cons_succ {count : Nat} (first : BitString) (rest : Store count)
    (index : Fin count) (value : BitString) :
    (Store.cons first rest).set index.succ value = Store.cons first (rest.set index value) := by rfl

theorem ext {count : Nat} (left right : Store count)
    (same : ∀ index, left.get index = right.get index) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons first rest ih =>
      cases right with
      | cons other tail =>
          have hFirst := same 0
          change first = other at hFirst
          subst other
          have hTail : rest = tail := ih tail (fun index => same index.succ)
          exact congrArg (Store.cons first) hTail

@[simp] theorem get_set {count : Nat} (store : Store count)
    (destination index : Fin count) (value : BitString) :
    (store.set destination value).get index =
      if index = destination then value else store.get index := by
  induction store with
  | nil => exact Fin.elim0 destination
  | @cons width first rest ih =>
      have zero_ne_succ (index : Fin width) : (0 : Fin (width + 1)) ≠ index.succ :=
        Ne.symm (Fin.succ_ne_zero index)
      cases destination using Fin.cases <;> cases index using Fin.cases <;>
        simp [ih, Fin.succ_ne_zero, zero_ne_succ]

@[simp] theorem set_get {count : Nat} (store : Store count) (index : Fin count) :
    store.set index (store.get index) = store := by
  apply ext
  intro selected
  by_cases h : selected = index
  · subst selected; simp
  · simp [h]

@[simp] theorem set_set_same {count : Nat} (store : Store count) (index : Fin count)
    (first second : BitString) :
    (store.set index first).set index second = store.set index second := by
  apply ext
  intro selected
  by_cases h : selected = index <;> simp [h]

end Store

namespace CopyProgram

/-- Fifteen actual instructions; neither loop is unrolled using an input length. -/
def body {count : Nat} (destination source scratch : Fin count) : Program count :=
  { code :=
      [ .clear destination 1,
        .clear scratch 2,
        .branch source 7 3 5,
        .pop source 4,
        .push scratch false 2,
        .pop source 6,
        .push scratch true 2,
        .branch scratch 14 8 11,
        .pop scratch 9,
        .push source false 10,
        .push destination false 7,
        .pop scratch 12,
        .push source true 13,
        .push destination true 7,
        .accept ]
    entry := 0, input := source, output := destination }

theorem initialize_run {count : Nat} (destination source scratch : Fin count)
    (store : Store count) :
    BitRegister.run (body destination source scratch) 2 ⟨.running 0, store⟩ =
      ⟨.running 2, (store.set destination []).set scratch []⟩ := by
  rfl

theorem reverse_step {count : Nat} (destination source scratch : Fin count)
    (separate : source ≠ scratch) (store : Store count) (bit : Bool) (rest : BitString)
    (head : store.get source = bit :: rest) :
    BitRegister.run (body destination source scratch) 3 ⟨.running 2, store⟩ =
      ⟨.running 2, (store.set source rest).set scratch (bit :: store.get scratch)⟩ := by
  have other : scratch ≠ source := Ne.symm separate
  cases bit <;>
    simp [BitRegister.run, step, body, lookup, Instruction.execute, Instruction.nextControl,
      Instruction.update, head, other]

theorem reverse_loop {count : Nat} (destination source scratch : Fin count)
    (separate : source ≠ scratch) (store : Store count) (bits accumulated : BitString)
    (sourceValue : store.get source = bits) (scratchValue : store.get scratch = accumulated) :
    BitRegister.run (body destination source scratch) (3 * bits.length + 1)
      ⟨.running 2, store⟩ =
    ⟨.running 7, (store.set source []).set scratch (bits.reverse ++ accumulated)⟩ := by
  have other : scratch ≠ source := Ne.symm separate
  induction bits generalizing store accumulated with
  | nil =>
      have hSource : store.set source [] = store := by
        rw [← sourceValue]; exact Store.set_get store source
      have hScratch : store.set scratch accumulated = store := by
        rw [← scratchValue]; exact Store.set_get store scratch
      simp [BitRegister.run, step, body, lookup, Instruction.execute, Instruction.nextControl,
        Instruction.update, sourceValue, hSource, hScratch]
  | cons bit rest ih =>
      let moved := (store.set source rest).set scratch (bit :: accumulated)
      have hFirst := reverse_step destination source scratch separate store bit rest sourceValue
      rw [scratchValue] at hFirst
      have hSource : moved.get source = rest := by simp [moved, separate]
      have hScratch : moved.get scratch = bit :: accumulated := by simp [moved]
      have hTail := ih moved (bit :: accumulated) hSource hScratch
      have hSteps : 3 * (bit :: rest).length + 1 = 3 + (3 * rest.length + 1) := by
        simp only [List.length_cons]; omega
      rw [hSteps, BitRegister.run_add, hFirst]
      rw [hTail]
      have hStore :
          (moved.set source []).set scratch (rest.reverse ++ bit :: accumulated) =
          (store.set source []).set scratch ((bit :: rest).reverse ++ accumulated) := by
        apply Store.ext
        intro index
        by_cases hs : index = source <;> by_cases hx : index = scratch <;>
          simp_all [moved, List.reverse_cons, List.append_assoc]
      exact congrArg (fun final => (⟨.running 7, final⟩ : Configuration count)) hStore

theorem restore_step {count : Nat} (destination source scratch : Fin count)
    (ds : destination ≠ source) (dx : destination ≠ scratch) (sx : source ≠ scratch)
    (store : Store count) (bit : Bool) (rest : BitString)
    (head : store.get scratch = bit :: rest) :
    BitRegister.run (body destination source scratch) 4 ⟨.running 7, store⟩ =
      ⟨.running 7,
        ((store.set scratch rest).set source (bit :: store.get source)).set destination
          (bit :: store.get destination)⟩ := by
  cases bit <;>
    simp [BitRegister.run, step, body, lookup, Instruction.execute, Instruction.nextControl,
      Instruction.update, head, ds, dx, sx]

theorem restore_loop {count : Nat} (destination source scratch : Fin count)
    (ds : destination ≠ source) (dx : destination ≠ scratch) (sx : source ≠ scratch)
    (store : Store count) (bits sourceAccum destinationAccum : BitString)
    (scratchValue : store.get scratch = bits)
    (sourceValue : store.get source = sourceAccum)
    (destinationValue : store.get destination = destinationAccum) :
    BitRegister.run (body destination source scratch) (4 * bits.length + 1)
      ⟨.running 7, store⟩ =
    ⟨.running 14,
      ((store.set scratch []).set source (bits.reverse ++ sourceAccum)).set destination
        (bits.reverse ++ destinationAccum)⟩ := by
  have sd := Ne.symm ds
  have xd := Ne.symm dx
  have xs := Ne.symm sx
  induction bits generalizing store sourceAccum destinationAccum with
  | nil =>
      have hx : store.set scratch [] = store := by
        rw [← scratchValue]; exact Store.set_get store scratch
      have hs : store.set source sourceAccum = store := by
        rw [← sourceValue]; exact Store.set_get store source
      have hd : store.set destination destinationAccum = store := by
        rw [← destinationValue]; exact Store.set_get store destination
      simp [BitRegister.run, step, body, lookup, Instruction.execute, Instruction.nextControl,
        Instruction.update, scratchValue, hx, hs, hd]
  | cons bit rest ih =>
      let moved := ((store.set scratch rest).set source (bit :: sourceAccum)).set destination
        (bit :: destinationAccum)
      have hFirst := restore_step destination source scratch ds dx sx store bit rest scratchValue
      rw [sourceValue, destinationValue] at hFirst
      have hx : moved.get scratch = rest := by simp [moved, xd, xs]
      have hs : moved.get source = bit :: sourceAccum := by simp [moved, sd]
      have hd : moved.get destination = bit :: destinationAccum := by simp [moved]
      have hTail := ih moved (bit :: sourceAccum) (bit :: destinationAccum) hx hs hd
      have hSteps : 4 * (bit :: rest).length + 1 = 4 + (4 * rest.length + 1) := by
        simp only [List.length_cons]; omega
      rw [hSteps, BitRegister.run_add, hFirst, hTail]
      have hStore :
          ((moved.set scratch []).set source (rest.reverse ++ bit :: sourceAccum)).set destination
            (rest.reverse ++ bit :: destinationAccum) =
          ((store.set scratch []).set source ((bit :: rest).reverse ++ sourceAccum)).set destination
            ((bit :: rest).reverse ++ destinationAccum) := by
        apply Store.ext
        intro index
        by_cases hi : index = source <;> by_cases hj : index = destination <;>
          by_cases hk : index = scratch <;>
          simp_all [moved, List.reverse_cons, List.append_assoc]
      exact congrArg (fun final => (⟨.running 14, final⟩ : Configuration count)) hStore

/-- All other registers, including the restored source, retain their exact value. -/
theorem body_run {count : Nat} (destination source scratch : Fin count)
    (ds : destination ≠ source) (dx : destination ≠ scratch) (sx : source ≠ scratch)
    (store : Store count) :
    BitRegister.run (body destination source scratch) (7 * (store.get source).length + 5)
      ⟨.running 0, store⟩ =
    ⟨.accepted, (store.set destination (store.get source)).set scratch []⟩ := by
  have sd := Ne.symm ds
  have xd := Ne.symm dx
  have xs := Ne.symm sx
  let bits := store.get source
  let initialized := (store.set destination []).set scratch []
  let reversed := (initialized.set source []).set scratch bits.reverse
  have hSource : initialized.get source = bits := by simp [initialized, bits, sd, sx]
  have hScratch : initialized.get scratch = [] := by simp [initialized]
  have hFirst := reverse_loop destination source scratch sx initialized bits [] hSource hScratch
  simp only [List.append_nil] at hFirst
  have hx : reversed.get scratch = bits.reverse := by simp [reversed]
  have hs : reversed.get source = [] := by simp [reversed, sx]
  have hd : reversed.get destination = [] := by simp [reversed, initialized, ds, dx]
  have hSecond := restore_loop destination source scratch ds dx sx reversed bits.reverse [] []
    hx hs hd
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hSecond
  have hSteps : 7 * bits.length + 5 = ((2 + (3 * bits.length + 1)) + (4 * bits.length + 1)) + 1 := by omega
  change BitRegister.run _ (7 * bits.length + 5) _ = _
  rw [hSteps,
    BitRegister.run_add _ ((2 + (3 * bits.length + 1)) + (4 * bits.length + 1)) 1,
    BitRegister.run_add _ (2 + (3 * bits.length + 1)) (4 * bits.length + 1),
    BitRegister.run_add _ 2 (3 * bits.length + 1),
    initialize_run, hFirst, hSecond]
  have hStore :
      ((reversed.set scratch []).set source bits).set destination bits =
      (store.set destination bits).set scratch [] := by
    apply Store.ext
    intro index
    by_cases hi : index = source <;> by_cases hj : index = destination <;>
      by_cases hk : index = scratch <;> simp_all [reversed, initialized, bits]
  have hFinish (final : Store count) :
      BitRegister.run (body destination source scratch) 1 ⟨.running 14, final⟩ =
        ⟨.accepted, final⟩ := by rfl
  rw [hFinish, hStore]

/-- The scratch register is reserved by construction, not selected by the caller. -/
def program {count : Nat} (destination source : Fin count) : Program (count + 1) :=
  if destination = source then
    { code := [.accept], entry := 0, input := source.succ, output := destination.succ }
  else body destination.succ source.succ 0

def instructionSteps {count : Nat} (destination source : Fin count) (store : Store count) : Nat :=
  if destination = source then 1 else 7 * (store.get source).length + 5

/-- Exact finite-instruction semantics for every source store and both alias cases. -/
theorem run {count : Nat} (destination source : Fin count) (store : Store count) :
    BitRegister.run (program destination source) (instructionSteps destination source store)
      ⟨.running 0, Store.cons [] store⟩ =
    ⟨.accepted, Store.cons [] (store.set destination (store.get source))⟩ := by
  by_cases same : destination = source
  · subst destination
    simp [program, instructionSteps, BitRegister.run, step, lookup, Instruction.execute,
      Instruction.nextControl, Instruction.update]
  · have separate : destination.succ ≠ source.succ := by
      intro equality; exact same (Fin.succ_inj.mp equality)
    have hd : destination.succ ≠ (0 : Fin (count + 1)) := Fin.succ_ne_zero destination
    have hs : source.succ ≠ (0 : Fin (count + 1)) := Fin.succ_ne_zero source
    have h := body_run destination.succ source.succ 0 separate hd hs (Store.cons [] store)
    simpa only [program, instructionSteps, if_neg same, Store.get_cons_succ, Store.set_cons_succ,
      Store.set_cons_zero] using h

def CopyFree {count : Nat} : Instruction count → Prop
  | .copy _ _ _ => False
  | _ => True

theorem program_copyFree {count : Nat} (destination source : Fin count) :
    ∀ instruction, instruction ∈ (program destination source).code → CopyFree instruction := by
  by_cases same : destination = source <;>
    simp [program, same, body, CopyFree]

theorem instructionSteps_le {count bound : Nat} (destination source : Fin count)
    (store : Store count) (bounded : store.Bounded bound) :
    instructionSteps destination source store ≤ 7 * bound + 5 := by
  have lengthBound := Store.get_length_le store source bounded
  unfold instructionSteps
  split <;> omega

end CopyProgram
end PNP.Concrete.BitRegister
