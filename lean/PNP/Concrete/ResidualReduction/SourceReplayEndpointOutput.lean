import PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute
import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

/-! Canonical optional-witness output for replay. Success is controlled by
the cumulative validity word, never by instruction termination. The actual
closed endpoint derives the final-width invariant before using the codec lemma. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState

def codec : Codec (Option BitString) := MatrixSolutionEncoding.optionCodec (listCodec bitCodec)
theorem bit_sequence (bits : BitString) : encodeSeq bitCodec.encode bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    change [bit] ++ encodeSeq bitCodec.encode rest = bit :: rest
    rw [ih]
    rfl
theorem some_bytes (point : BitString) :
    codec.encode (some point) = true :: (List.replicate point.length true ++ false :: point) := by
  simp only [codec,MatrixSolutionEncoding.optionCodec,listCodec,bit_sequence,natural,
    List.append_assoc,List.cons_append,List.nil_append]
theorem none_bytes : codec.encode none = [false] := rfl

def unaryBody : Block 9 := .seq (.action (.pop 0)) (.action (.push 8 true))
def unaryLoop : Block 9 := .loop 0 unaryBody
theorem unary_exec (count : Nat) (r : Registers) :
    Exec unaryLoop ({r with input := List.replicate count true}).store (3 * count + 1)
      ({r with input := [],output := List.replicate count true ++ r.output}).store := by
  induction count generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    let first := {r with input := List.replicate (count + 1) true}
    let middle := {r with input := List.replicate count true}
    let next := {middle with output := true :: r.output}
    have pop : Exec (.action (.pop (0 : Fin 9))) first.store 1 middle.store := by
      simp only [first,List.replicate_succ]
      exact .action _ _
    have push : Exec (.action (.push (8 : Fin 9) true)) middle.store 1 next.store := .action _ _
    have read : first.store.get 0 = true :: List.replicate count true := by
      change List.replicate (count + 1) true = _
      rw [List.replicate_succ]
    have checked := Exec.loopStep (source := (0 : Fin 9)) read (Exec.seq pop push)
      (ih {r with output := true :: r.output})
    have cost : 3 * (count + 1) + 1 = 1 + (2 + (3 * count + 1)) := by omega
    simpa only [unaryLoop,unaryBody,cost,first,MatrixStrictHeader.replicate_push] using checked

theorem push_output_exec (r : Registers) (point : BitString) (p : Parameters) (loopGood good bit : Bool) :
    Exec (.action (.push (8 : Fin 40) bit)) (full r 0 point [] p loopGood good) 1
      (full {r with output := bit :: r.output} 0 point [] p loopGood good) :=
  core9_exec (b := .action (.push (8 : Fin 9) bit)) (used := 1)
    (before := r) (after := {r with output := bit :: r.output})
    (show Exec (.action (.push (8 : Fin 9) bit)) r.store 1
      ({r with output := bit :: r.output}).store from .action _ _) 0 point [] p loopGood good

def width (p : Parameters) : Nat := SourceReplayEndpointCheck.width true p
def selectWidth : Block 40 := .branch 35 (.action (.copy 0 39)) (.action (.copy 0 39)) (.action (.copy 0 36))
theorem selectWidth_exec (cursor point : BitString) (p : Parameters) (loopGood good : Bool) :
    Exec selectWidth (work 0 cursor point p loopGood good) 2
      (full (SourceReplayState.blank (List.replicate (width p) true) []) 0 point [] p loopGood good) := by
  let r := SourceReplayState.blank cursor []
  let low := Frame.join (framed r 0 point p loopGood) (middle [])
  have original : Exec (.action (.copy (0 : Fin 40) 36)) (full r 0 point [] p loopGood good) 1
      (full (SourceReplayState.blank (List.replicate p.original true) []) 0 point [] p loopGood good) :=
    SourceReplayEndpointState.copy_core_exec low (saved p good) 0 1 (List.replicate p.original true)
      (Frame.join (framed (SourceReplayState.blank (List.replicate p.original true) []) 0 point p loopGood) (middle [])) rfl rfl
  have terminal : Exec (.action (.copy (0 : Fin 40) 39)) (full r 0 point [] p loopGood good) 1
      (full (SourceReplayState.blank (List.replicate p.terminal true) []) 0 point [] p loopGood good) :=
    SourceReplayEndpointState.copy_core_exec low (saved p good) 0 4 (List.replicate p.terminal true)
      (Frame.join (framed (SourceReplayState.blank (List.replicate p.terminal true) []) 0 point p loopGood) (middle [])) rfl rfl
  have read := read_mode r 0 point [] p loopGood good
  cases direction : p.recover with
  | false =>
    rw [direction] at read
    simpa only [selectWidth,width,SourceReplayEndpointCheck.width,direction,Bool.false_eq_true,↓reduceIte] using
      (show Exec selectWidth (work 0 cursor point p loopGood good) 2
        (full (SourceReplayState.blank (List.replicate p.terminal true) []) 0 point [] p loopGood good) from Exec.zero read terminal)
  | true =>
    rw [direction] at read
    simpa only [selectWidth,width,SourceReplayEndpointCheck.width,direction,↓reduceIte] using
      (show Exec selectWidth (work 0 cursor point p loopGood good) 2
        (full (SourceReplayState.blank (List.replicate p.original true) []) 0 point [] p loopGood good) from Exec.one read original)

def bytes (p : Parameters) (point : BitString) (good : Bool) : BitString :=
  if good then true :: (List.replicate (width p) true ++ false :: point) else [false]
def result (cursor point : BitString) (p : Parameters) (loopGood good : Bool) : Store 40 :=
  full (SourceReplayState.blank (if good then [] else cursor) (bytes p point good)) 0 point [] p loopGood good
def success : Block 40 := .seq selectWidth <| .seq (.action (.copy 8 26)) <|
  .seq (.action (.push 8 false)) (.seq (core9 unaryLoop) (.action (.push 8 true)))
theorem success_exec (cursor point : BitString) (p : Parameters) (loopGood good : Bool) :
    Exec success (work 0 cursor point p loopGood good) (3 * width p + 6)
      (full (SourceReplayState.blank [] (bytes p point true)) 0 point [] p loopGood good) := by
  let counted := SourceReplayState.blank (List.replicate (width p) true) []
  let copied := {counted with output := point}
  let started := {counted with output := false :: point}
  let ended := SourceReplayState.blank [] (List.replicate (width p) true ++ false :: point)
  have select := selectWidth_exec cursor point p loopGood good
  have copy : Exec (.action (.copy (8 : Fin 40) 26)) (full counted 0 point [] p loopGood good) 1
      (full copied 0 point [] p loopGood good) :=
    SourceReplayEndpointReadyState.copy_exec _ _ 8 26 point (read_point counted 0 point [] p loopGood good) rfl
  have mark : Exec (.action (.push (8 : Fin 40) false)) (full copied 0 point [] p loopGood good) 1
      (full started 0 point [] p loopGood good) := push_output_exec copied point p loopGood good false
  have prefixLoop : Exec (core9 unaryLoop) (full started 0 point [] p loopGood good)
      (3 * width p + 1) (full ended 0 point [] p loopGood good) :=
    core9_exec (before := started) (after := ended)
      (unary_exec (width p) (SourceReplayState.blank [] (false :: point))) 0 point [] p loopGood good
  have last : Exec (.action (.push (8 : Fin 40) true)) (full ended 0 point [] p loopGood good) 1
      (full (SourceReplayState.blank [] (bytes p point true)) 0 point [] p loopGood good) :=
    push_output_exec ended point p loopGood good true
  have cost : 3 * width p + 6 = 2 + (1 + (1 + ((3 * width p + 1) + 1))) := by omega
  simpa only [success,cost] using Exec.seq select (Exec.seq copy (Exec.seq mark (Exec.seq prefixLoop last)))

def failure : Block 40 := .seq (.action (.clear 8)) (.action (.push 8 false))
def block : Block 40 := .branch 38 failure failure success
def fuel (p : Parameters) (good : Bool) : Nat := if good then 3 * width p + 7 else 3
theorem block_exec (cursor point : BitString) (p : Parameters) (loopGood good : Bool) :
    Exec block (work 0 cursor point p loopGood good) (fuel p good) (result cursor point p loopGood good) := by
  have read := read_valid (SourceReplayState.blank cursor []) 0 point [] p loopGood good
  cases good with
  | false =>
    have failed : Exec failure (work 0 cursor point p loopGood false) 2
        (full (SourceReplayState.blank cursor [false]) 0 point [] p loopGood false) :=
      core9_exec (before := SourceReplayState.blank cursor []) (after := SourceReplayState.blank cursor [false])
        (show Exec (.seq (.action (.clear (8 : Fin 9))) (.action (.push 8 false)))
          (SourceReplayState.blank cursor []).store 2 (SourceReplayState.blank cursor [false]).store from
            Exec.seq (.action _ _) (.action _ _)) 0 point [] p loopGood false
    exact Exec.empty read failed
  | true =>
    have checked : Exec block (work 0 cursor point p loopGood true) (1 + (3 * width p + 6))
        (result cursor point p loopGood true) := Exec.one read (success_exec cursor point p loopGood true)
    have cost : fuel p true = 1 + (3 * width p + 6) := by
      simp only [fuel,↓reduceIte]
      omega
    rw [cost]
    exact checked

theorem read_output (r : Registers) (point : BitString) (p : Parameters) (loopGood good : Bool) :
    (full r 0 point [] p loopGood good).get 8 = r.output := rfl
theorem result_output (cursor point : BitString) (p : Parameters) (loopGood good : Bool) :
    (result cursor point p loopGood good).get 8 = bytes p point good :=
  read_output _ point p loopGood good

theorem bytes_codec (p : Parameters) (point : BitString) (good : Bool)
    (exactWidth : good = true → point.length = width p) :
    bytes p point good = codec.encode (if good then some point else none) := by
  cases good with
  | false => rfl
  | true => simp only [bytes,↓reduceIte,some_bytes,exactWidth rfl]

theorem width_bound (p : Parameters) (limit : Nat) (original : p.original ≤ limit) (terminal : p.terminal ≤ limit) :
    width p ≤ limit := by
  cases direction : p.recover <;>
    simp only [width,SourceReplayEndpointCheck.width,direction,Bool.false_eq_true,↓reduceIte] <;> assumption
theorem fuel_bound (p : Parameters) (good : Bool) (limit : Nat)
    (original : p.original ≤ limit) (terminal : p.terminal ≤ limit) : fuel p good ≤ 3 * limit + 7 := by
  have bound := width_bound p limit original terminal
  cases good <;> simp only [fuel,Bool.false_eq_true,↓reduceIte] <;> omega

end PNP.Concrete.ResidualReduction.SourceReplayEndpointOutput
