/-
Copyright (c) 2026 PNP Labs.

Finite decoding of a selected matching value. A positive literal consists of
a positive tag and unary units, each encoded as a true/true pair. Counting
those pairs directly produces the presence bit followed by the unary value.
The loop stops on any other pair; malformed input is handled totally.
-/

import PNP.Concrete.NormalizerVertexCanonical

namespace PNP.Concrete.NormalizerBlocks.MatchingValue

open BitRegister Occurrence

def pair : Block 9 :=
  .branch 0 Occurrence.stop Occurrence.stop
    (.seq (.action (.pop 0))
      (.branch 0 Occurrence.stop Occurrence.stop
        (.seq (.action (.pop 0)) (.action (.push 8 true)))))

theorem pair_empty_exec (r : Registers) :
    Exec pair ({r with input := []}).store 2 ({r with input := [], active := []}).store :=
  Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)

theorem pair_false_exec (r : Registers) (rest : BitString) :
    Exec pair ({r with input := false :: rest}).store 2
      ({r with input := false :: rest, active := []}).store :=
  Exec.zero (source := (0 : Fin 9)) rfl (.action _ _)

theorem pair_true_empty_exec (r : Registers) :
    Exec pair ({r with input := [true]}).store 4
      ({r with input := [], active := []}).store :=
  Exec.one (source := (0 : Fin 9)) rfl
    (Exec.seq (.action _ _) (Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)))

theorem pair_true_false_exec (r : Registers) (rest : BitString) :
    Exec pair ({r with input := true :: false :: rest}).store 4
      ({r with input := false :: rest, active := []}).store :=
  Exec.one (source := (0 : Fin 9)) rfl
    (Exec.seq (.action _ _) (Exec.zero (source := (0 : Fin 9)) rfl (.action _ _)))

theorem pair_true_true_exec (r : Registers) (rest : BitString) :
    Exec pair ({r with input := true :: true :: rest}).store 5
      ({r with input := rest, output := true :: r.output}).store :=
  Exec.one (source := (0 : Fin 9)) rfl
    (Exec.seq (.action _ _) (Exec.one (source := (0 : Fin 9)) rfl
      (Exec.seq (.action _ _) (.action _ _))))

end PNP.Concrete.NormalizerBlocks.MatchingValue
