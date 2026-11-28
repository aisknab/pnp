import PNP.ThreeUse.Witness
import Lean.Elab.Command

/-! End-to-end and malformed-input controls for the typed reduction, strict decoder and word verifier. -/

namespace PNP.ThreeUse
open PNP.Concrete
namespace Regression

def good : CNFFormula := ⟨3, [[⟨true, 0⟩, ⟨true, 1⟩, ⟨false, 2⟩], [⟨false, 0⟩], [⟨true, 2⟩], [⟨false, 7⟩, ⟨true, 1⟩]]⟩

def bad : CNFFormula := ⟨0, [[⟨true, 0⟩, ⟨false, 0⟩]]⟩

def original : BitString := [false, true, true]

theorem good_word : good.Satisfied original := (checkCNF_eq_true_iff _ _).mp rfl

theorem strict_model : finiteFeasible (targetRows (encodeCNF good)) := (strict_finite _).mp
  ⟨good, decodeEncodedCNF_canonical _, original, good_word⟩

theorem impossible_oob : ¬feasible (targetRows (encodeCNF bad)) := by
  rintro ⟨v, h⟩; obtain ⟨f, par, w⟩ := original_replay _ _ h
  rw [decodeEncodedCNF_canonical] at par; cases par
  have len := w.1
  change (sourceWord (encodeCNF bad) v).length = 0 at len
  cases eq : sourceWord (encodeCNF bad) v with
  | nil => rw [eq] at w; obtain ⟨a|b|z, _⟩ := w.2 <;> contradiction
  | cons b w' => rw [eq] at len; contradiction

theorem impossible_bad_bytes : ¬finiteFeasible (targetRows []) := by
  intro h; obtain ⟨_, falseDecode, _⟩ := (strict_finite []).mpr h; contradiction

def evalBank {α : Type} (rows : List (Row α)) (v : α → G) : Bool :=
  rows.all fun r => decide (eval v r.w = r.out)
end Regression
end PNP.ThreeUse

namespace PNP.ThreeUse.Encoding
open PNP.Concrete
namespace Regression

def paired : CNFFormula := ⟨2, [[⟨true, 0⟩, ⟨true, 1⟩], [⟨false, 1⟩]]⟩

def outsidePacket : Packet := ⟨1, [⟨[(1, false)], one⟩]⟩

def emptyPacket : Packet := ⟨0, []⟩

theorem reject_oob : decode (encode outsidePacket) = none := rfl

theorem reject_partial : decode [true, true] = none := rfl

theorem empty_canonical : decode [false, false] = some emptyPacket := rfl

theorem impossible_source : ¬∃ w, verify (compile []) w = true := by
  intro h; obtain ⟨_, bad, _⟩ := (source_witness []).mpr h; contradiction

theorem malformed_cost : (compile []).length = 216 := by
  have h := emitted_exact []
  change 2*(compile []).length = 3*(8*8)+27*8+10*2+4 at h; omega
end Regression
end PNP.ThreeUse.Encoding

namespace PNP.ThreeUse.Encoding.Regression
open PNP.Concrete

-- This code is written independently of the encoder: width 1, one identity-target
-- word, and one positive token at numeric label 0. The word is valid syntax but
-- is not a three-use instance. Changing the index to 1 fails the range check.
private def examplePacket : Packet := ⟨1, [⟨[(0, false)], one⟩]⟩

example : decode [true,false,true,false,false,false,false,true,false,false,false] =
    some examplePacket := rfl
example : decode [true,false,true,false,false,false,false,true,false,false,true,false] =
    none := rfl
example : verify [true,false,true,false,false,false,false,true,false,false,false]
    [false,false,false] = false := rfl

end PNP.ThreeUse.Encoding.Regression

open Lean Elab Command PNP.ThreeUse PNP.ThreeUse.Regression PNP.Concrete
run_cmd do
  let bits:=encodeCNF good
  let rs:=targetRows bits
  let ext:=lift (send (fun i=>decide (i=1 ∨ i=2)))
  unless evalBank rs ext && sourceWord bits ext==original do throwError "original-signal replay failed"
  let ports:=unique (labels rs)
  let some first:=ports.head? | throwError "fixture lost all ports"
  let badPort:=fun p=>if p=first then gmul mark (ext p) else ext p
  unless !(evalBank rs badPort) && ports.all (fun p=>hits p (labels rs)==3) &&
      rs.all (fun r=>decide (r.w.map Prod.fst).Nodup && r.w.length≤12) do
    throwError "hostile changed physical port or degree/word shape failure"
  logInfo "THREE_USE_TYPED_REGRESSION_OK"

open PNP.ThreeUse.Encoding PNP.ThreeUse.Encoding.Regression
run_cmd do
  let raw:=encodeCNF paired
  let bs:=compile raw
  let some p:=decode bs | throwError "emission rejected during independent decode"
  let phys:=lift (send (fun i=>decide (i=0)))
  let slots0:=labels (tagged (macroRows (normalized raw)))
  let w:=witness p.width (fun i=>bySlot phys i slots0)
  unless p.width==36 && p.rows.length==42 && slots p.rows==108 && bs.length==2462 && raw.length==33 &&
      w.length==108 && verify bs w && shapeB p &&
      sourceWord raw (fun t=>loadVal t.2 w)==[true,false] do
    throwError "real bytes, cost, physical donor, or original word mismatch"
  unless (decode (bs++[true])).isNone && (decode bs.dropLast).isNone &&
      (decode (encode outsidePacket)).isNone && !(verify bs w.dropLast) &&
      !(verify bs (w++[true])) && !(verify (encode emptyPacket) []) &&
      (compile []).length==216 do throwError "hostile token/terminator or witness mutation accepted"
  logInfo "THREE_USE_ENCODING_REGRESSION_OK"
