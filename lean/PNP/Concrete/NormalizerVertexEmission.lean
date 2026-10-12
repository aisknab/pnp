/-
Copyright (c) 2026 PNP Labs.

Finite tagged-vertex emission for the complete source-order search range.
The tag reuses literal polarity only as an encoding: true denotes a clause
vertex and false a variable vertex. Each index is a finite unary word, copied
and consumed by the already checked loop, not a semantic machine instruction.
-/

import PNP.Concrete.NormalizerCandidateOrder

namespace PNP.Concrete.NormalizerBlocks.SearchVertices

open BitRegister Occurrence

def entryBits (tag : Bool) (index : Nat) : BitString :=
  [false, true] ++ NANDFrontend.literalBits tag index ++ [true, false]

theorem entryBits_exact (tag : Bool) (index : Nat) :
    entryBits tag index = encodeTokenPairs (encodeClauseTokens [⟨tag, index⟩]) := by
  simp only [entryBits, NANDFrontend.literalBits_exact, encodeClauseTokens,
    encodeLiteralListTokens, NANDFrontend.encodeTokenPairs_append,
    encodeTokenPairs, CNFToken.bits, List.append_nil, List.cons_append, List.nil_append]

theorem entryBits_reverse (tag : Bool) (index : Nat) :
    (entryBits tag index).reverse =
      [false, true, false, false] ++ List.replicate (2 * index) true ++ [tag, tag, true, false] := by
  simp only [entryBits, List.reverse_append, NANDFrontend.literalBits_reverse,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.append_assoc]

def emitEntry (tag : Bool) : Block 9 :=
  .seq (.action (.copy 4 1)) <| .seq (ClauseQuery.emit false true) <|
  .seq (ClauseQuery.emit tag tag) <| .seq TableWrite.valueLoop <|
  .seq (ClauseQuery.emit false false) (ClauseQuery.emit true false)

def emitted (tag : Bool) (r : Registers) : Registers :=
  {r with sign := [], excess := (entryBits tag r.target.length).reverse ++ r.excess}

theorem emitEntry_exec (tag : Bool) (r : Registers) :
    Exec (emitEntry tag) r.store (4 * r.target.length + 10) (emitted tag r).store := by
  have checked := Exec.seq (Exec.action (.copy 4 1) r.store)
    (Exec.seq (ClauseQuery.emit_exec false true {r with sign := r.target})
      (Exec.seq (ClauseQuery.emit_exec tag tag (ClauseQuery.emitted false true {r with sign := r.target}))
        (Exec.seq (TableWrite.value_exec r.target
          (ClauseQuery.emitted tag tag (ClauseQuery.emitted false true {r with sign := r.target})))
          (Exec.seq (ClauseQuery.emit_exec false false _) (ClauseQuery.emit_exec true false _)))))
  have cost : 4 * r.target.length + 10 =
      1 + (2 + (2 + ((4 * r.target.length + 1) + (2 + 2)))) := by omega
  rw [cost]
  simpa only [emitEntry, emitted, ClauseQuery.emitted, TableWrite.valueResult,
    entryBits_reverse, List.append_assoc,
    List.cons_append, List.nil_append] using checked

def step (tag : Bool) : Block 9 :=
  .seq (emitEntry tag) (.seq (.action (.pop 2)) (.action (.push 1 true)))
def advanced (tag : Bool) (r : Registers) : Registers :=
  {emitted tag r with remaining := r.remaining.tail, target := true :: r.target}

theorem step_exec (tag : Bool) (r : Registers) :
    Exec (step tag) r.store (4 * r.target.length + 12) (advanced tag r).store := by
  have cost : 4 * r.target.length + 12 = (4 * r.target.length + 10) + (1 + 1) := by omega
  rw [cost]
  exact Exec.seq (emitEntry_exec tag r) (Exec.seq (.action _ _) (.action _ _))

def rangeBits (tag : Bool) : Nat → Nat → BitString
  | 0, _ => []
  | count + 1, index => entryBits tag index ++ rangeBits tag count (index + 1)

def rangeData (tag : Bool) : Nat → Nat → List CNFLiteral
  | 0, _ => []
  | count + 1, index => ⟨tag, index⟩ :: rangeData tag count (index + 1)

theorem rangeBits_exact (tag : Bool) (count index : Nat) :
    rangeBits tag count index =
      encodeTokenPairs (encodeClauseListTokens ((rangeData tag count index).map (fun v => [v]))) := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      simp only [rangeBits, rangeData, List.map_cons, encodeClauseListTokens,
        NANDFrontend.encodeTokenPairs_append, entryBits_exact, ih]

end PNP.Concrete.NormalizerBlocks.SearchVertices
