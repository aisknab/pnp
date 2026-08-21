import PNP.ResidualTerminalHResolveHDisjointFamily

namespace PNP
namespace DirectWire
namespace HResolveHDisjointFamilyRegression

abbrev FixtureFootprint :=
  TerminalHereditaryFootprint Nat Nat Nat Nat Nat Nat Nat Nat

def footprint (support frontier origin kernel obligation prefixTail charge
    interface : List Nat) : FixtureFootprint :=
  {
    support := support
    frontier := frontier
    origin := origin
    kernel := kernel
    obligation := obligation
    prefixTail := prefixTail
    charge := charge
    interface := interface
  }

def supportRoute : FixtureFootprint :=
  footprint [0] [] [] [] [] [] [] []

def frontierRoute : FixtureFootprint :=
  footprint [] [1] [] [] [] [] [] []

def originRoute : FixtureFootprint :=
  footprint [] [] [2] [] [] [] [] []

def kernelRoute : FixtureFootprint :=
  footprint [] [] [] [3] [] [] [] []

def obligationRoute : FixtureFootprint :=
  footprint [] [] [] [] [4] [] [] []

def prefixTailRoute : FixtureFootprint :=
  footprint [] [] [] [] [] [5] [] []

def chargeRoute : FixtureFootprint :=
  footprint [] [] [] [] [] [] [6] []

def interfaceRoute : FixtureFootprint :=
  footprint [] [] [] [] [] [] [] [7]

example : supportRoute.firstInterference? supportRoute = some .support := rfl
example : frontierRoute.firstInterference? frontierRoute = some .frontier := rfl
example : originRoute.firstInterference? originRoute = some .origin := rfl
example : kernelRoute.firstInterference? kernelRoute = some .kernel := rfl
example : obligationRoute.firstInterference? obligationRoute =
    some .obligation := rfl
example : prefixTailRoute.firstInterference? prefixTailRoute =
    some .prefixTail := rfl
example : chargeRoute.firstInterference? chargeRoute = some .charge := rfl
example : interfaceRoute.firstInterference? interfaceRoute =
    some .interface := rfl

def selectedLeft : FixtureFootprint :=
  footprint [10] [20] [30] [40] [50] [60] [70] [80]

def selectedRight : FixtureFootprint :=
  footprint [11] [21] [31] [41] [51] [61] [71] [81]

example : selectedLeft.checkHDisjoint selectedRight = true := rfl
example : selectedLeft.firstInterference? selectedRight = none := rfl
example : selectedLeft.HDisjoint selectedRight :=
  (selectedLeft.checkHDisjoint_eq_true_iff selectedRight).mp rfl

def rejectedCandidate : FixtureFootprint :=
  footprint [99] [100] [] [] [] [] [] []

def selectedBlocker : FixtureFootprint :=
  footprint [99] [101] [] [] [] [] [] []

def governedFamily : List FixtureFootprint :=
  [rejectedCandidate, selectedBlocker, selectedRight]

example : terminalHResolveGreedyHDisjointFamily governedFamily =
    [selectedBlocker, selectedRight] := rfl

example : rejectedCandidate.firstInterference? selectedBlocker =
    some .support := rfl

example : governedFamily.Nodup := by decide

example :
    let selected := terminalHResolveGreedyHDisjointFamily governedFamily
    selected.Nodup ∧
      (∀ candidate, candidate ∈ selected → candidate ∈ governedFamily) ∧
      selected.Pairwise TerminalHereditaryFootprint.HDisjoint ∧
      (∀ candidate, candidate ∈ governedFamily →
        candidate ∈ selected ∨
          ∃ blocker, blocker ∈ selected ∧
            ∃ route, candidate.firstInterference? blocker = some route) :=
  terminal_hresolve_maximal_hdisjoint_family_complete governedFamily (by decide)

end HResolveHDisjointFamilyRegression
end DirectWire
end PNP
