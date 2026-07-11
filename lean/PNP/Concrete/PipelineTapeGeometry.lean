/-
Copyright (c) 2026 PNP Labs.

Boundary-marked two-track geometry for future raw-pipeline composition.

The first track stores one simulated raw tape symbol.  The second track is a
tag: blank denotes data, zero denotes the left boundary, and one denotes the
right boundary.  Cells strictly outside the first markers are intentionally
unconstrained so that moving a boundary inward need not erase stale tape.

This module proves only pure tape identities.  It defines no transition rules,
work machine, state namespace, simulation, compiler, or runtime theorem.
-/

import PNP.Concrete.TapeHandoff
import PNP.Concrete.WorkMachine

namespace PNP.Concrete

namespace PipelineTape

/-- Encode one simulated raw cell on the first track.  A blank second track
marks this as data rather than a boundary. -/
def dataSymbol (symbol : TapeSymbol) : WorkSymbol :=
  ⟨symbol, .blank⟩

/-- Boundary immediately beyond the materialized logical cells to the left. -/
def leftMarker : WorkSymbol :=
  ⟨.blank, .zero⟩

/-- Boundary immediately beyond the materialized logical cells to the right. -/
def rightMarker : WorkSymbol :=
  ⟨.blank, .one⟩

theorem dataSymbol_injective {left right : TapeSymbol}
    (h : dataSymbol left = dataSymbol right) : left = right := by
  exact congrArg WorkSymbol.first h

theorem dataSymbol_ne_leftMarker (symbol : TapeSymbol) :
    dataSymbol symbol ≠ leftMarker := by
  intro h
  have hSecond := congrArg WorkSymbol.second h
  contradiction

theorem dataSymbol_ne_rightMarker (symbol : TapeSymbol) :
    dataSymbol symbol ≠ rightMarker := by
  intro h
  have hSecond := congrArg WorkSymbol.second h
  contradiction

theorem leftMarker_ne_rightMarker : leftMarker ≠ rightMarker := by
  intro h
  have hSecond := congrArg WorkSymbol.second h
  contradiction

/-- Two-track image of one raw tape.  Cells beyond each first boundary marker
are arbitrary garbage and are outside the represented logical tape. -/
def frameWithGarbage (raw : Tape)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  { left := raw.left.map dataSymbol ++ (leftMarker :: outsideLeft)
    head := dataSymbol raw.head
    right := raw.right.map dataSymbol ++ (rightMarker :: outsideRight) }

/-- A work tape represents a raw tape when the logical data is bracketed by
the two markers.  No restriction is imposed on cells outside the markers. -/
def Represents (raw : Tape) (work : WorkTape) : Prop :=
  ∃ outsideLeft outsideRight,
    work = frameWithGarbage raw outsideLeft outsideRight

/-- Canonical frame with no materialized exterior garbage. -/
def frame (raw : Tape) : WorkTape :=
  frameWithGarbage raw [] []

theorem frameWithGarbage_represents (raw : Tape)
    (outsideLeft outsideRight : List WorkSymbol) :
    Represents raw (frameWithGarbage raw outsideLeft outsideRight) := by
  exact ⟨outsideLeft, outsideRight, rfl⟩

theorem frame_represents (raw : Tape) :
    Represents raw (frame raw) := by
  exact frameWithGarbage_represents raw [] []

/-- Writing a raw symbol changes only the data head and preserves both
boundaries and all exterior garbage. -/
theorem represents_write {raw : Tape} {work : WorkTape}
    (h : Represents raw work) (symbol : TapeSymbol) :
    Represents (raw.write symbol) (work.write (dataSymbol symbol)) := by
  rcases h with ⟨outsideLeft, outsideRight, hWork⟩
  subst work
  exact ⟨outsideLeft, outsideRight, rfl⟩

/-- An interior raw left move is one ordinary work-tape left move. -/
theorem represents_moveLeft_of_cons {raw : Tape} {work : WorkTape}
    (h : Represents raw work) {symbol : TapeSymbol} {rest : List TapeSymbol}
    (hLeft : raw.left = symbol :: rest) :
    Represents raw.moveLeft work.moveLeft := by
  rcases h with ⟨outsideLeft, outsideRight, hWork⟩
  subst work
  cases raw with
  | mk left head right =>
      cases hLeft
      exact ⟨outsideLeft, outsideRight, rfl⟩

/-- Pure geometry for extending an empty logical left side by one blank data
cell while moving the left marker one cell outward. -/
def expandLeftBoundary (work : WorkTape) : WorkTape :=
  (((work.moveLeft).write (dataSymbol .blank)).moveLeft.write leftMarker).moveRight

/-- Left-boundary expansion consumes the first exterior garbage cell when it
exists, or materializes an implicit blank when it does not. -/
theorem represents_expandLeft_of_nil {raw : Tape} {work : WorkTape}
    (h : Represents raw work) (hLeft : raw.left = []) :
    Represents raw.moveLeft (expandLeftBoundary work) := by
  rcases h with ⟨outsideLeft, outsideRight, hWork⟩
  subst work
  cases raw with
  | mk left head right =>
      cases hLeft
      cases outsideLeft with
      | nil => exact ⟨[], outsideRight, rfl⟩
      | cons first rest => exact ⟨rest, outsideRight, rfl⟩

/-- An interior raw right move is one ordinary work-tape right move. -/
theorem represents_moveRight_of_cons {raw : Tape} {work : WorkTape}
    (h : Represents raw work) {symbol : TapeSymbol} {rest : List TapeSymbol}
    (hRight : raw.right = symbol :: rest) :
    Represents raw.moveRight work.moveRight := by
  rcases h with ⟨outsideLeft, outsideRight, hWork⟩
  subst work
  cases raw with
  | mk left head right =>
      cases hRight
      exact ⟨outsideLeft, outsideRight, rfl⟩

/-- Pure geometry for extending an empty logical right side by one blank data
cell while moving the right marker one cell outward. -/
def expandRightBoundary (work : WorkTape) : WorkTape :=
  (((work.moveRight).write (dataSymbol .blank)).moveRight.write rightMarker).moveLeft

/-- Right-boundary expansion consumes the first exterior garbage cell when it
exists, or materializes an implicit blank when it does not. -/
theorem represents_expandRight_of_nil {raw : Tape} {work : WorkTape}
    (h : Represents raw work) (hRight : raw.right = []) :
    Represents raw.moveRight (expandRightBoundary work) := by
  rcases h with ⟨outsideLeft, outsideRight, hWork⟩
  subst work
  cases raw with
  | mk left head right =>
      cases hRight
      cases outsideRight with
      | nil => exact ⟨outsideLeft, [], rfl⟩
      | cons first rest => exact ⟨outsideLeft, rest, rfl⟩

/-- Every pure canonical handoff target has a valid boundary frame even when
arbitrary stale cells remain outside both markers.  This theorem constructs
no transition rules and gives no runtime bound. -/
theorem handoffTarget_withGarbage_represents (raw : Tape)
    (outsideLeft outsideRight : List WorkSymbol) :
    Represents raw.handoffTarget
      (frameWithGarbage raw.handoffTarget outsideLeft outsideRight) := by
  exact frameWithGarbage_represents raw.handoffTarget outsideLeft outsideRight

end PipelineTape

end PNP.Concrete
