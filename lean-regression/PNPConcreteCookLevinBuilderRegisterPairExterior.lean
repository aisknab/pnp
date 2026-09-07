import PNP.Concrete.CookLevinBuilderRegisterPairExterior

open PNP.Concrete
open PNP.Concrete.CookLevin
open WorkMachineLeftBoundary
open BuilderRegisterPairExterior

example (boundary : WorkSymbol) (machine : WorkMachine) (hSafe : Safe boundary machine)
    (steps : Nat) (initial final : WorkConfiguration) (outside : List WorkSymbol)
    (hProtected : Protected boundary initial.tape)
    (hRun : workRunExact? machine steps initial = some final) :
    workRunExact? machine steps (appendConfiguration initial outside) =
      some (appendConfiguration final outside) :=
  workRunExact_transport boundary machine hSafe steps initial final outside hProtected hRun

example (boundary : WorkSymbol) (machine : WorkMachine) (hSafe : Safe boundary machine)
    (config next : WorkConfiguration) (outside : List WorkSymbol)
    (hProtected : Protected boundary config.tape) (hStep : workStep? machine config = some next) :
    Protected boundary next.tape ∧
      workStep? machine (appendConfiguration config outside) =
        some (appendConfiguration next outside) :=
  step_transport boundary machine hSafe config next outside hProtected hStep

example (boundary : WorkSymbol) (inside : List WorkSymbol) :
    Protected boundary {left := [], head := boundary, right := inside} := Or.inr ⟨rfl, rfl⟩

example : ¬ RuleSafe WorkSymbol.oneOne
    {sourceState := 0, readSymbol := .oneOne, targetState := 1,
     writeSymbol := .oneOne, move := .left} := by
  unfold RuleSafe
  decide

example : ¬ RuleSafe WorkSymbol.oneOne
    {sourceState := 0, readSymbol := .oneOne, targetState := 1,
     writeSymbol := .blank, move := .stay} := by
  unfold RuleSafe
  decide

example (tape : WorkTape) (outside : List WorkSymbol) :
    (appendTape tape outside).left = tape.left ++ outside := rfl

example (tape : WorkTape) (outside : List WorkSymbol) :
    (appendTape tape outside).right = tape.right := rfl

example : Safe BuilderUnaryPolynomial.scratchEndSymbol BuilderRegionPairComparison.machine := boundary_safe

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? BuilderRegionPairComparison.machine (BuilderRegionPairComparison.workSteps c b)
      (initialConfiguration c b older inside outside) =
      some (finalConfiguration c b older inside outside) := workRunExact c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine BuilderRegionPairComparison.machine)
      (6 * BuilderRegionPairComparison.workSteps c b)
      (encodeWorkConfiguration (initialConfiguration c b older inside outside)) =
      encodeWorkConfiguration (finalConfiguration c b older inside outside) :=
  run_compile_exact c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).tape =
      BuilderRegionResidualRegisters.inputTape
        (BuilderRegionResidualRegisters.ofComparison
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 c b))
        ((BuilderUnaryPolynomial.registerWord older).reverse ++ inside) outside :=
  final_tape c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).state =
      BuilderRegionPairComparison.machine.acceptState ↔ c < b :=
  final_accept_iff c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).state =
      BuilderRegionPairComparison.machine.rejectState ↔ b ≤ c :=
  final_reject_iff c b older inside outside

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration n n older inside outside).state =
      BuilderRegionPairComparison.machine.rejectState :=
  (final_reject_iff n n older inside outside).2 (Nat.le_refl n)

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration n (n + 1) older inside outside).state =
      BuilderRegionPairComparison.machine.acceptState :=
  (final_accept_iff n (n + 1) older inside outside).2 (by omega)

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (n + 1) n older inside outside).state =
      BuilderRegionPairComparison.machine.rejectState :=
  (final_reject_iff (n + 1) n older inside outside).2 (by omega)

example : workRunExact? BuilderRegionPairComparison.machine
    (BuilderRegionPairComparison.workSteps 0 1)
    (initialConfiguration 0 1 [4, 2] [.oneZero] [.oneOne, .zeroOne]) =
    some (finalConfiguration 0 1 [4, 2] [.oneZero] [.oneOne, .zeroOne]) :=
  workRunExact 0 1 [4, 2] [.oneZero] [.oneOne, .zeroOne]

example : workRunExact? BuilderRegionPairComparison.machine
    (BuilderRegionPairComparison.workSteps 2 2)
    (initialConfiguration 2 2 [4] [.oneZero] [.zeroZero, .oneOne]) =
    some (finalConfiguration 2 2 [4] [.oneZero] [.zeroZero, .oneOne]) :=
  workRunExact 2 2 [4] [.oneZero] [.zeroZero, .oneOne]

example : workRunExact? BuilderRegionPairComparison.machine
    (BuilderRegionPairComparison.workSteps 3 1)
    (initialConfiguration 3 1 [] [.oneZero] [.oneOne]) =
    some (finalConfiguration 3 1 [] [.oneZero] [.oneOne]) :=
  workRunExact 3 1 [] [.oneZero] [.oneOne]

example (c b bound : Nat) (hc : c ≤ bound) (hb : b ≤ bound) :
    6 * BuilderRegionPairComparison.workSteps c b ≤ BuilderRegionPairComparison.rawTimeBound bound :=
  BuilderRegionPairComparison.rawTimeBound_le c b bound hc hb
