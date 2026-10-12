import PNP.Concrete.NormalizerTableEmission

namespace PNP.Concrete.NormalizerBlocks

example (word : BitString) (r : Occurrence.Registers) :
    Exec TableWrite.valueLoop ({r with sign := word}).store (4 * word.length + 1)
      (TableWrite.valueResult word r).store := TableWrite.value_exec word r
example (r : Occurrence.Registers) :
    Exec TableWrite.replacement r.store (TableWrite.replacementFuel r)
      (TableWrite.replaced r).store := TableWrite.replacement_exec r
example (r : Occurrence.Registers) : (TableWrite.replaced r).input = r.input := rfl
example (r : Occurrence.Registers) : (TableWrite.replaced r).target = r.target := rfl

#print axioms TableWrite.value_exec
#print axioms TableWrite.replacement_exec
#print axioms TableWrite.replacement_input
#print axioms TableWrite.replacement_target
#print axioms TableWrite.replacement_sign

end PNP.Concrete.NormalizerBlocks
