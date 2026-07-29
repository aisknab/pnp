/-
Copyright (c) 2026 PNP Labs.

Constructive layout witnesses for one cursor-marked retained source.

The literal source-capture controller replaces exactly one packed source cell
by the contextual cursor.  Marked appenders need that cursor split for all
four source kinds.  The reload machine additionally needs a packed prefix and
an input/gate unary field.  These two facts are deliberately proved
separately: Boolean constants have the former shape and not the latter.
-/

import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgram

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimeLayout

open PNP.Concrete

abbrev SourceKind := TargetEmitterSourceCapture.SourceKind
abbrev NatKind := TargetEmitterMarkedSourceReload.NatKind

def packedCellOfSymbol : WorkSymbol →
    TargetEmitterMarkedSourceReload.PackedCell
  | ⟨.zero, .zero⟩ =>
      .cell00
  | ⟨.zero, .one⟩ =>
      .cell01
  | ⟨.one, .zero⟩ =>
      .cell10
  | ⟨.one, .one⟩ =>
      .cell11
  | _ =>
      .cell00

def packedCells (word : List WorkSymbol) :
    List TargetEmitterMarkedSourceReload.PackedCell :=
  word.map packedCellOfSymbol

theorem packedWord_packedCells_eq
    (word : List WorkSymbol)
    (packed :
      ∀ symbol, symbol ∈ word →
        TargetEmitter.PackedSymbol symbol) :
    TargetEmitterMarkedSourceReload.packedWord
        (packedCells word) =
      word := by
  induction word with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      have headPacked := packed head (List.Mem.head tail)
      have tailPacked :
          ∀ symbol, symbol ∈ tail →
            TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        exact packed symbol (List.Mem.tail head member)
      change
        TargetEmitterMarkedSourceReload.PackedCell.symbol
              (packedCellOfSymbol head) ::
            TargetEmitterMarkedSourceReload.packedWord
              (packedCells tail) =
          head :: tail
      rw [inductionHypothesis tailPacked]
      cases headPacked <;> rfl

def localCursorBefore (kind : SourceKind) (value : Nat) :
    List WorkSymbol :=
  match kind with
  | .input =>
      [TargetEmitterSourceCapture.cell00,
        TargetEmitterSourceCapture.cell11] ++
        TargetEmitterSourceCapture.unitPrefix value ++
        [TargetEmitterSourceCapture.cell00]
  | .constantFalse | .constantTrue =>
      [TargetEmitterSourceCapture.cell01]
  | .gate =>
      [TargetEmitterSourceCapture.cell01,
        TargetEmitterSourceCapture.cell10] ++
        TargetEmitterSourceCapture.unitPrefix value ++
        [TargetEmitterSourceCapture.cell00]

def cursorOriginal (kind : SourceKind) : WorkSymbol :=
  match kind with
  | .input | .gate =>
      TargetEmitterSourceCapture.cell10
  | .constantFalse =>
      TargetEmitterSourceCapture.cell00
  | .constantTrue =>
      TargetEmitterSourceCapture.cell01

theorem markedSourceCells_eq_cursor
    (kind : SourceKind) (value : Nat) :
    TargetEmitterSourceCapture.markedSourceCells kind value =
      localCursorBefore kind value ++
        [TargetEmitterCursorAppender.cursorMarker] := by
  cases kind <;>
    simp [TargetEmitterSourceCapture.markedSourceCells,
      localCursorBefore, TargetEmitterSourceCapture.cursorMarker,
      TargetEmitterCursorAppender.cursorMarker,
      List.append_assoc]

theorem sourceCells_eq_original
    (kind : SourceKind) (value : Nat) :
    TargetEmitterSourceCapture.sourceCells kind value =
      localCursorBefore kind value ++
        [cursorOriginal kind] := by
  cases kind <;>
    simp [TargetEmitterSourceCapture.sourceCells,
      TargetEmitterSourceCapture.natCells_eq_unitPrefix,
      localCursorBefore, cursorOriginal, List.append_assoc]

def cursorLayout
    (kind : SourceKind) (value : Nat)
    (before after : List WorkSymbol)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            before ++
              TargetEmitterSourceCapture.sourceCells kind value ++
              after →
          TargetEmitter.PackedSymbol symbol) :
    TargetEmitterRuntimeProgram.CursorLayout
      (before ++
        TargetEmitterSourceCapture.markedSourceCells kind value ++
        after) := by
  let cursorBefore := before ++ localCursorBefore kind value
  refine
    { cursorBefore := cursorBefore
      cursorOriginal := cursorOriginal kind
      cursorAfter := after
      cursorSource := ?_
      originalPacked := ?_
      beforePacked := ?_
      afterPacked := ?_ }
  · simp [TargetEmitterCursorAppender.sourceWithCursor,
      cursorBefore, markedSourceCells_eq_cursor,
      List.append_assoc]
  · intro symbol member
    apply originalPacked symbol
    simpa [TargetEmitterCursorAppender.originalSource,
      cursorBefore, sourceCells_eq_original,
      List.append_assoc] using member
  · intro symbol member
    apply originalPacked symbol
    rcases List.mem_append.mp member with
      beforeMember | localMember
    · exact List.mem_append.mpr <|
        Or.inl <| List.mem_append.mpr (Or.inl beforeMember)
    · have sourceMember :
          symbol ∈
            TargetEmitterSourceCapture.sourceCells kind value := by
        rw [sourceCells_eq_original]
        exact List.mem_append.mpr (Or.inl localMember)
      exact List.mem_append.mpr <|
        Or.inl <| List.mem_append.mpr (Or.inr sourceMember)
  · intro symbol member
    apply originalPacked symbol
    exact List.mem_append.mpr (Or.inr member)

def reloadLayout
    (kind : NatKind) (value : Nat)
    (before after : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    TargetEmitterRuntimeProgram.ReloadLayout
      (before ++
        TargetEmitterMarkedSourceReload.markedSourceCells kind value ++
        after) := by
  refine
    { kind := kind
      value := value
      reloadBefore := packedCells before
      reloadAfter := after
      reloadSource := ?_ }
  rw [packedWord_packedCells_eq before beforePacked]

def sourceContext_of_packed_head
    (head : WorkSymbol) (tail : List WorkSymbol)
    (packed : TargetEmitter.PackedSymbol head) :
    TargetEmitterRuntimeProgram.SourceContext (head :: tail) :=
  { head := head
    tail := tail
    source_eq := rfl
    allowed := Or.inl packed }

def sourceContext_of_cursor
    (tail : List WorkSymbol) :
    TargetEmitterRuntimeProgram.SourceContext
      (TargetEmitterCursorAppender.cursorMarker :: tail) :=
  { head := TargetEmitterCursorAppender.cursorMarker
    tail := tail
    source_eq := rfl
    allowed := Or.inr rfl }

def sourceContext_of_nonempty_packed_prefix
    (head : WorkSymbol) (prefixTail marked after : List WorkSymbol)
    (packed : TargetEmitter.PackedSymbol head) :
    TargetEmitterRuntimeProgram.SourceContext
      ((head :: prefixTail) ++ marked ++ after) := by
  simpa [List.append_assoc] using
    sourceContext_of_packed_head head
      (prefixTail ++ marked ++ after) packed

end PNP.Concrete.LockedNAND.TargetEmitterRuntimeLayout
