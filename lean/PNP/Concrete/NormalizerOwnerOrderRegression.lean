import PNP.Concrete.NormalizerOwnerOrder

namespace PNP.Concrete.NormalizerBlocks

example (f : Fin count → Option Nat) (offset target : Nat) :
    TableOwner.ownerFrom offset (List.ofFn f) target =
      ((List.finRange count).find? (fun i => f i == some target)).map (fun i => offset + i.val) :=
  TableOwner.ownerFrom_ofFn f offset target
example (f : Fin count → Option Nat) (target : Nat) :
    TableOwner.owner (List.ofFn f) target =
      ((List.finRange count).find? (fun i => f i == some target)).map Fin.val :=
  TableOwner.owner_ofFn f target
example (f : Fin count → Option Nat) (target : Nat) :
    TableOwner.polynomial.output (TableOwner.encodeQuery target (List.ofFn f)) =
      TableOwner.answer (((List.finRange count).find? (fun i => f i == some target)).map Fin.val) := by
  rw [TableOwner.polynomial_canonical, TableOwner.owner_ofFn]

#print axioms TableOwner.ownerFrom_ofFn
#print axioms TableOwner.owner_ofFn

end PNP.Concrete.NormalizerBlocks
