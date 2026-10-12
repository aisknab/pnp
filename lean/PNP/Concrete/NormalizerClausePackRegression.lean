import PNP.Concrete.NormalizerClausePack

namespace PNP.Concrete.NormalizerBlocks

open Occurrence

example (r : Registers) (word : BitString) :
    Exec ClauseQuery.reverseLoop ({r with excess := word}).store (4 * word.length + 1)
      ({r with excess := [], output := word.reverse ++ r.output}).store := ClauseQuery.reverse_exec r word
example (r : Registers) : Exec ClauseQuery.pack r.store (ClauseQuery.packFuel r) (ClauseQuery.packed r).store :=
  ClauseQuery.pack_exec r
example : (ClauseQuery.packed ⟨[], [], [], [], [], [], [], [], [false]⟩).output = [true, false] := rfl
example : (ClauseQuery.packed ⟨[], [], [], [false, true], [], [], [], [], [false]⟩).output =
    [true, false, true, false] := rfl
example : ClauseQuery.packFuel ⟨[], [], [], [false, true], [], [], [], [], []⟩ = 20 := rfl

#print axioms ClauseQuery.reverse_step
#print axioms ClauseQuery.reverse_exec
#print axioms ClauseQuery.pack_exec

end PNP.Concrete.NormalizerBlocks
