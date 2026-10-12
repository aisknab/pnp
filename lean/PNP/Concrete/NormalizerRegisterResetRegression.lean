import PNP.Concrete.NormalizerRegisterReset
namespace PNP.Concrete.NormalizerBlocks
open BitRegister
example {count : Nat} (store : Store count) :
    Exec (RegisterReset.all count) store (count + 1) (Store.empty count) := RegisterReset.all_exec store
example {count : Nat} (store : Store (count + 1)) :
    Exec (RegisterReset.keepFirst count) store (count + 1) (.cons (store.get 0) (Store.empty count)) :=
  RegisterReset.keepFirst_exec store
#print axioms RegisterReset.action_update
#print axioms RegisterReset.get_succ
#print axioms RegisterReset.execution
#print axioms RegisterReset.all_exec
#print axioms RegisterReset.keepFirst_exec
end PNP.Concrete.NormalizerBlocks
