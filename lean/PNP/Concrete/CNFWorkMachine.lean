/-
Copyright (c) 2026 PNP Labs.

A literal finite work-machine verifier for the canonical CNF codec.  The
machine validates both packed frames, checks the declared assignment width,
and evaluates every unary-indexed literal against the shared assignment.
Malformed paths have explicit reject transitions; no Lean function is stored
in the executable machine syntax.
-/

import PNP.Concrete.CNFWorkInput

namespace PNP.Concrete

/-! ### Readable aliases for the nine work symbols -/

def cnfBlank : WorkSymbol := WorkSymbol.blank
def cnfMarkFalse : WorkSymbol := WorkSymbol.blankZero
def cnfMarkTrue : WorkSymbol := WorkSymbol.blankOne
def cnfRootGuard : WorkSymbol := WorkSymbol.zeroBlank
def cnfF : WorkSymbol := WorkSymbol.zeroZero
def cnfSep : WorkSymbol := WorkSymbol.zeroOne
def cnfBoundaryGuard : WorkSymbol := WorkSymbol.oneBlank
def cnfFinish : WorkSymbol := WorkSymbol.oneZero
def cnfT : WorkSymbol := WorkSymbol.oneOne

/-- Fixed complete work alphabet, in compiler code order. -/
def cnfWorkAlphabet : List WorkSymbol :=
  [cnfBlank, cnfMarkFalse, cnfMarkTrue, cnfRootGuard, cnfF,
    cnfSep, cnfBoundaryGuard, cnfFinish, cnfT]

namespace CNFWorkState

def accept : Nat := 0
def reject : Nat := 1
def boot : Nat := 2
def bootLeft : Nat := 3

def frameOneFindCounter : Nat := 4
def frameOneToHeader : Nat := 5
def frameOneFindPayload : Nat := 6
def frameOneBackPayload : Nat := 7
def frameOneBackHeader : Nat := 8
def frameOneCheckPayload : Nat := 9
def frameOneRestorePayload : Nat := 10
def frameOneGoBoundary : Nat := 11

def frameTwoFindCounter : Nat := 12
def frameTwoToHeader : Nat := 13
def frameTwoFindPayload : Nat := 14
def frameTwoBackPayload : Nat := 15
def frameTwoBackHeader : Nat := 16
def frameTwoCheckPayload : Nat := 17
def frameTwoEnsureBlank : Nat := 18
def frameTwoAtRightGuard : Nat := 19
def frameTwoRestorePayload : Nat := 20

def seekLeftRoot : Nat := 21
def seekFormulaStart : Nat := 22

def widthFindFormula : Nat := 23
def widthToBoundary : Nat := 24
def widthPastCertificateCounter : Nat := 25
def widthFindAssignment : Nat := 26
def widthBackAssignment : Nat := 27
def widthBackCertificateCounter : Nat := 28
def widthBackFormula : Nat := 29
def widthDoneToBoundary : Nat := 30
def widthDonePastCertificateCounter : Nat := 31
def widthDoneCheckAssignment : Nat := 32
def widthRestoreAssignment : Nat := 33
def widthRestoreCertificateCounter : Nat := 34
def widthRestoreBackFormula : Nat := 35
def widthRestoreSeekFormula : Nat := 36
def widthRestoreFormula : Nat := 37

def clauseStart : Nat := 38
def clauseNeedLiteral : Nat := 39

private def boolCode : Bool → Nat
  | false => 0
  | true => 1

private def modeCode (alreadySatisfied positive : Bool) : Nat :=
  2 * boolCode alreadySatisfied + boolCode positive

def clauseContinue (alreadySatisfied : Bool) : Nat :=
  40 + boolCode alreadySatisfied

def literalIndex (alreadySatisfied positive : Bool) : Nat :=
  42 + modeCode alreadySatisfied positive

def literalIndexToBoundary (alreadySatisfied positive : Bool) : Nat :=
  46 + modeCode alreadySatisfied positive

def literalIndexPastCertificateCounter
    (alreadySatisfied positive : Bool) : Nat :=
  50 + modeCode alreadySatisfied positive

def literalMarkAssignment (alreadySatisfied positive : Bool) : Nat :=
  54 + modeCode alreadySatisfied positive

def literalReturnAssignment (alreadySatisfied positive : Bool) : Nat :=
  58 + modeCode alreadySatisfied positive

def literalReturnCertificateCounter
    (alreadySatisfied positive : Bool) : Nat :=
  62 + modeCode alreadySatisfied positive

def literalReturnSeekSign (alreadySatisfied positive : Bool) : Nat :=
  66 + modeCode alreadySatisfied positive

def literalReturnSeekIndex (alreadySatisfied positive : Bool) : Nat :=
  70 + modeCode alreadySatisfied positive

def literalLookupToBoundary (alreadySatisfied positive : Bool) : Nat :=
  74 + modeCode alreadySatisfied positive

def literalLookupPastCertificateCounter
    (alreadySatisfied positive : Bool) : Nat :=
  78 + modeCode alreadySatisfied positive

def literalLookupAssignment (alreadySatisfied positive : Bool) : Nat :=
  82 + modeCode alreadySatisfied positive

def literalRestoreAssignment (result positive : Bool) : Nat :=
  86 + modeCode result positive

def literalRestoreCertificateCounter (result positive : Bool) : Nat :=
  90 + modeCode result positive

def literalRestoreSeekSign (result positive : Bool) : Nat :=
  94 + modeCode result positive

def literalRestoreIndex (result positive : Bool) : Nat :=
  98 + modeCode result positive

def finalCheck : Nat := 102

end CNFWorkState

/-! ### Finite rule-list construction -/

def cnfWorkRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (movement : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := movement }

def cnfKeepRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (movement : HeadMove) : WorkRule :=
  cnfWorkRule source read target read movement

def cnfRejectRule (source : Nat) (read : WorkSymbol) : WorkRule :=
  cnfWorkRule source read CNFWorkState.reject read .stay

/-- One explicit reject rule for every alphabet symbol.  Specific rules are
placed before this suffix, so first-match semantics selects them and every
other symbol rejects. -/
def cnfRejectSuffix (source : Nat) : List WorkRule :=
  cnfWorkAlphabet.map (cnfRejectRule source)

def cnfCompleteRules (source : Nat) (specific : List WorkRule) :
    List WorkRule :=
  specific ++ cnfRejectSuffix source

private def keepMany (source target : Nat) (movement : HeadMove)
    (symbols : List WorkSymbol) : List WorkRule :=
  symbols.map (fun symbol => cnfKeepRule source symbol target movement)

private def completeKeepMany (source target : Nat) (movement : HeadMove)
    (symbols : List WorkSymbol) : List WorkRule :=
  cnfCompleteRules source (keepMany source target movement symbols)

/-! ### Frame validation -/

private def cnfBootRules : List WorkRule :=
  cnfCompleteRules CNFWorkState.boot
    [cnfKeepRule CNFWorkState.boot cnfT CNFWorkState.bootLeft .left] ++
  cnfCompleteRules CNFWorkState.bootLeft
    [cnfWorkRule CNFWorkState.bootLeft cnfBlank
      CNFWorkState.frameOneFindCounter cnfRootGuard .right]

private def frameOneRules : List WorkRule :=
  cnfCompleteRules CNFWorkState.frameOneFindCounter
    [ cnfKeepRule CNFWorkState.frameOneFindCounter cnfMarkFalse
        CNFWorkState.frameOneFindCounter .right
    , cnfWorkRule CNFWorkState.frameOneFindCounter cnfT
        CNFWorkState.frameOneToHeader cnfMarkFalse .right
    , cnfKeepRule CNFWorkState.frameOneFindCounter cnfFinish
        CNFWorkState.frameOneCheckPayload .right ] ++
  cnfCompleteRules CNFWorkState.frameOneToHeader
    (keepMany CNFWorkState.frameOneToHeader CNFWorkState.frameOneToHeader
        .right [cnfT, cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.frameOneToHeader cnfFinish
        CNFWorkState.frameOneFindPayload .right]) ++
  cnfCompleteRules CNFWorkState.frameOneFindPayload
    (keepMany CNFWorkState.frameOneFindPayload CNFWorkState.frameOneFindPayload
        .right [cnfMarkFalse, cnfMarkTrue, cnfRootGuard, cnfBoundaryGuard] ++
      [ cnfWorkRule CNFWorkState.frameOneFindPayload cnfF
          CNFWorkState.frameOneBackPayload cnfMarkFalse .left
      , cnfWorkRule CNFWorkState.frameOneFindPayload cnfT
          CNFWorkState.frameOneBackPayload cnfMarkTrue .left
      , cnfWorkRule CNFWorkState.frameOneFindPayload cnfSep
          CNFWorkState.frameOneBackPayload cnfRootGuard .left
      , cnfWorkRule CNFWorkState.frameOneFindPayload cnfFinish
          CNFWorkState.frameOneBackPayload cnfBoundaryGuard .left ]) ++
  cnfCompleteRules CNFWorkState.frameOneBackPayload
    (keepMany CNFWorkState.frameOneBackPayload CNFWorkState.frameOneBackPayload
        .left [cnfMarkFalse, cnfMarkTrue, cnfRootGuard, cnfBoundaryGuard] ++
      [cnfKeepRule CNFWorkState.frameOneBackPayload cnfFinish
        CNFWorkState.frameOneBackHeader .left]) ++
  cnfCompleteRules CNFWorkState.frameOneBackHeader
    (keepMany CNFWorkState.frameOneBackHeader CNFWorkState.frameOneBackHeader
        .left [cnfT, cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.frameOneBackHeader cnfRootGuard
        CNFWorkState.frameOneFindCounter .right]) ++
  cnfCompleteRules CNFWorkState.frameOneCheckPayload
    (keepMany CNFWorkState.frameOneCheckPayload
        CNFWorkState.frameOneCheckPayload .right
        [cnfMarkFalse, cnfMarkTrue, cnfRootGuard, cnfBoundaryGuard] ++
      [cnfWorkRule CNFWorkState.frameOneCheckPayload cnfSep
        CNFWorkState.frameOneRestorePayload cnfBoundaryGuard .left]) ++
  cnfCompleteRules CNFWorkState.frameOneRestorePayload
    [ cnfWorkRule CNFWorkState.frameOneRestorePayload cnfMarkFalse
        CNFWorkState.frameOneRestorePayload cnfF .left
    , cnfWorkRule CNFWorkState.frameOneRestorePayload cnfMarkTrue
        CNFWorkState.frameOneRestorePayload cnfT .left
    , cnfWorkRule CNFWorkState.frameOneRestorePayload cnfRootGuard
        CNFWorkState.frameOneRestorePayload cnfSep .left
    , cnfWorkRule CNFWorkState.frameOneRestorePayload cnfBoundaryGuard
        CNFWorkState.frameOneRestorePayload cnfFinish .left
    , cnfKeepRule CNFWorkState.frameOneRestorePayload cnfFinish
        CNFWorkState.frameOneGoBoundary .right ] ++
  cnfCompleteRules CNFWorkState.frameOneGoBoundary
    (keepMany CNFWorkState.frameOneGoBoundary CNFWorkState.frameOneGoBoundary
        .right [cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule CNFWorkState.frameOneGoBoundary cnfBoundaryGuard
        CNFWorkState.frameTwoFindCounter .right])

private def frameTwoRules : List WorkRule :=
  cnfCompleteRules CNFWorkState.frameTwoFindCounter
    [ cnfKeepRule CNFWorkState.frameTwoFindCounter cnfMarkFalse
        CNFWorkState.frameTwoFindCounter .right
    , cnfWorkRule CNFWorkState.frameTwoFindCounter cnfT
        CNFWorkState.frameTwoToHeader cnfMarkFalse .right
    , cnfKeepRule CNFWorkState.frameTwoFindCounter cnfFinish
        CNFWorkState.frameTwoCheckPayload .right ] ++
  cnfCompleteRules CNFWorkState.frameTwoToHeader
    (keepMany CNFWorkState.frameTwoToHeader CNFWorkState.frameTwoToHeader
        .right [cnfT, cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.frameTwoToHeader cnfFinish
        CNFWorkState.frameTwoFindPayload .right]) ++
  cnfCompleteRules CNFWorkState.frameTwoFindPayload
    (keepMany CNFWorkState.frameTwoFindPayload CNFWorkState.frameTwoFindPayload
        .right [cnfMarkFalse, cnfMarkTrue] ++
      [ cnfWorkRule CNFWorkState.frameTwoFindPayload cnfF
          CNFWorkState.frameTwoBackPayload cnfMarkFalse .left
      , cnfWorkRule CNFWorkState.frameTwoFindPayload cnfT
          CNFWorkState.frameTwoBackPayload cnfMarkTrue .left ]) ++
  cnfCompleteRules CNFWorkState.frameTwoBackPayload
    (keepMany CNFWorkState.frameTwoBackPayload CNFWorkState.frameTwoBackPayload
        .left [cnfMarkFalse, cnfMarkTrue] ++
      [cnfKeepRule CNFWorkState.frameTwoBackPayload cnfFinish
        CNFWorkState.frameTwoBackHeader .left]) ++
  cnfCompleteRules CNFWorkState.frameTwoBackHeader
    (keepMany CNFWorkState.frameTwoBackHeader CNFWorkState.frameTwoBackHeader
        .left [cnfT, cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.frameTwoBackHeader cnfBoundaryGuard
        CNFWorkState.frameTwoFindCounter .right]) ++
  cnfCompleteRules CNFWorkState.frameTwoCheckPayload
    (keepMany CNFWorkState.frameTwoCheckPayload
        CNFWorkState.frameTwoCheckPayload .right [cnfMarkFalse, cnfMarkTrue] ++
      [cnfWorkRule CNFWorkState.frameTwoCheckPayload cnfFinish
        CNFWorkState.frameTwoEnsureBlank cnfRootGuard .right]) ++
  cnfCompleteRules CNFWorkState.frameTwoEnsureBlank
    [cnfKeepRule CNFWorkState.frameTwoEnsureBlank cnfBlank
      CNFWorkState.frameTwoAtRightGuard .left] ++
  cnfCompleteRules CNFWorkState.frameTwoAtRightGuard
    [cnfKeepRule CNFWorkState.frameTwoAtRightGuard cnfRootGuard
      CNFWorkState.frameTwoRestorePayload .left] ++
  cnfCompleteRules CNFWorkState.frameTwoRestorePayload
    [ cnfWorkRule CNFWorkState.frameTwoRestorePayload cnfMarkFalse
        CNFWorkState.frameTwoRestorePayload cnfF .left
    , cnfWorkRule CNFWorkState.frameTwoRestorePayload cnfMarkTrue
        CNFWorkState.frameTwoRestorePayload cnfT .left
    , cnfKeepRule CNFWorkState.frameTwoRestorePayload cnfFinish
        CNFWorkState.seekLeftRoot .left ]

/-! ### Width comparison -/

private def seekAndWidthRules : List WorkRule :=
  cnfCompleteRules CNFWorkState.seekLeftRoot
    (keepMany CNFWorkState.seekLeftRoot CNFWorkState.seekLeftRoot .left
        [cnfMarkFalse, cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish,
          cnfBoundaryGuard] ++
      [cnfKeepRule CNFWorkState.seekLeftRoot cnfRootGuard
        CNFWorkState.seekFormulaStart .right]) ++
  cnfCompleteRules CNFWorkState.seekFormulaStart
    (keepMany CNFWorkState.seekFormulaStart CNFWorkState.seekFormulaStart
        .right [cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.seekFormulaStart cnfFinish
        CNFWorkState.widthFindFormula .right]) ++
  cnfCompleteRules CNFWorkState.widthFindFormula
    [ cnfKeepRule CNFWorkState.widthFindFormula cnfMarkTrue
        CNFWorkState.widthFindFormula .right
    , cnfWorkRule CNFWorkState.widthFindFormula cnfT
        CNFWorkState.widthToBoundary cnfMarkTrue .right
    , cnfKeepRule CNFWorkState.widthFindFormula cnfF
        CNFWorkState.widthDoneToBoundary .right ] ++
  cnfCompleteRules CNFWorkState.widthToBoundary
    (keepMany CNFWorkState.widthToBoundary CNFWorkState.widthToBoundary .right
        [cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule CNFWorkState.widthToBoundary cnfBoundaryGuard
        CNFWorkState.widthPastCertificateCounter .right]) ++
  cnfCompleteRules CNFWorkState.widthPastCertificateCounter
    (keepMany CNFWorkState.widthPastCertificateCounter
        CNFWorkState.widthPastCertificateCounter .right [cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.widthPastCertificateCounter cnfFinish
        CNFWorkState.widthFindAssignment .right]) ++
  cnfCompleteRules CNFWorkState.widthFindAssignment
    (keepMany CNFWorkState.widthFindAssignment CNFWorkState.widthFindAssignment
        .right [cnfMarkFalse, cnfMarkTrue] ++
      [ cnfWorkRule CNFWorkState.widthFindAssignment cnfF
          CNFWorkState.widthBackAssignment cnfMarkFalse .left
      , cnfWorkRule CNFWorkState.widthFindAssignment cnfT
          CNFWorkState.widthBackAssignment cnfMarkTrue .left ]) ++
  cnfCompleteRules CNFWorkState.widthBackAssignment
    (keepMany CNFWorkState.widthBackAssignment CNFWorkState.widthBackAssignment
        .left [cnfMarkFalse, cnfMarkTrue] ++
      [cnfKeepRule CNFWorkState.widthBackAssignment cnfFinish
        CNFWorkState.widthBackCertificateCounter .left]) ++
  cnfCompleteRules CNFWorkState.widthBackCertificateCounter
    (keepMany CNFWorkState.widthBackCertificateCounter
        CNFWorkState.widthBackCertificateCounter .left [cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.widthBackCertificateCounter cnfBoundaryGuard
        CNFWorkState.widthBackFormula .left]) ++
  cnfCompleteRules CNFWorkState.widthBackFormula
    (keepMany CNFWorkState.widthBackFormula CNFWorkState.widthBackFormula .left
        [cnfMarkFalse, cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule CNFWorkState.widthBackFormula cnfRootGuard
        CNFWorkState.seekFormulaStart .right]) ++
  cnfCompleteRules CNFWorkState.widthDoneToBoundary
    (keepMany CNFWorkState.widthDoneToBoundary CNFWorkState.widthDoneToBoundary
        .right [cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule CNFWorkState.widthDoneToBoundary cnfBoundaryGuard
        CNFWorkState.widthDonePastCertificateCounter .right]) ++
  cnfCompleteRules CNFWorkState.widthDonePastCertificateCounter
    (keepMany CNFWorkState.widthDonePastCertificateCounter
        CNFWorkState.widthDonePastCertificateCounter .right [cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.widthDonePastCertificateCounter cnfFinish
        CNFWorkState.widthDoneCheckAssignment .right]) ++
  cnfCompleteRules CNFWorkState.widthDoneCheckAssignment
    (keepMany CNFWorkState.widthDoneCheckAssignment
        CNFWorkState.widthDoneCheckAssignment .right
        [cnfMarkFalse, cnfMarkTrue] ++
      [cnfKeepRule CNFWorkState.widthDoneCheckAssignment cnfRootGuard
        CNFWorkState.widthRestoreAssignment .left]) ++
  cnfCompleteRules CNFWorkState.widthRestoreAssignment
    [ cnfWorkRule CNFWorkState.widthRestoreAssignment cnfMarkFalse
        CNFWorkState.widthRestoreAssignment cnfF .left
    , cnfWorkRule CNFWorkState.widthRestoreAssignment cnfMarkTrue
        CNFWorkState.widthRestoreAssignment cnfT .left
    , cnfKeepRule CNFWorkState.widthRestoreAssignment cnfFinish
        CNFWorkState.widthRestoreCertificateCounter .left ] ++
  cnfCompleteRules CNFWorkState.widthRestoreCertificateCounter
    (keepMany CNFWorkState.widthRestoreCertificateCounter
        CNFWorkState.widthRestoreCertificateCounter .left [cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.widthRestoreCertificateCounter cnfBoundaryGuard
        CNFWorkState.widthRestoreBackFormula .left]) ++
  cnfCompleteRules CNFWorkState.widthRestoreBackFormula
    (keepMany CNFWorkState.widthRestoreBackFormula
        CNFWorkState.widthRestoreBackFormula .left
        [cnfMarkFalse, cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule CNFWorkState.widthRestoreBackFormula cnfRootGuard
        CNFWorkState.widthRestoreSeekFormula .right]) ++
  cnfCompleteRules CNFWorkState.widthRestoreSeekFormula
    (keepMany CNFWorkState.widthRestoreSeekFormula
        CNFWorkState.widthRestoreSeekFormula .right [cnfMarkFalse] ++
      [cnfKeepRule CNFWorkState.widthRestoreSeekFormula cnfFinish
        CNFWorkState.widthRestoreFormula .right]) ++
  cnfCompleteRules CNFWorkState.widthRestoreFormula
    [ cnfWorkRule CNFWorkState.widthRestoreFormula cnfMarkTrue
        CNFWorkState.widthRestoreFormula cnfT .right
    , cnfKeepRule CNFWorkState.widthRestoreFormula cnfF
        CNFWorkState.clauseStart .right ]

/-! ### Clause and literal evaluation -/

private def clauseRules : List WorkRule :=
  cnfCompleteRules CNFWorkState.clauseStart
    [ cnfKeepRule CNFWorkState.clauseStart cnfSep
        CNFWorkState.clauseNeedLiteral .right
    , cnfKeepRule CNFWorkState.clauseStart cnfFinish
        CNFWorkState.finalCheck .right ] ++
  cnfCompleteRules CNFWorkState.clauseNeedLiteral
    [ cnfWorkRule CNFWorkState.clauseNeedLiteral cnfF
        (CNFWorkState.literalIndex false false) cnfBoundaryGuard .right
    , cnfWorkRule CNFWorkState.clauseNeedLiteral cnfT
        (CNFWorkState.literalIndex false true) cnfBoundaryGuard .right ] ++
  cnfCompleteRules (CNFWorkState.clauseContinue false)
    [ cnfWorkRule (CNFWorkState.clauseContinue false) cnfF
        (CNFWorkState.literalIndex false false) cnfBoundaryGuard .right
    , cnfWorkRule (CNFWorkState.clauseContinue false) cnfT
        (CNFWorkState.literalIndex false true) cnfBoundaryGuard .right ] ++
  cnfCompleteRules (CNFWorkState.clauseContinue true)
    [ cnfWorkRule (CNFWorkState.clauseContinue true) cnfF
        (CNFWorkState.literalIndex true false) cnfBoundaryGuard .right
    , cnfWorkRule (CNFWorkState.clauseContinue true) cnfT
        (CNFWorkState.literalIndex true true) cnfBoundaryGuard .right
    , cnfKeepRule (CNFWorkState.clauseContinue true) cnfFinish
        CNFWorkState.clauseStart .right ] ++
  cnfCompleteRules CNFWorkState.finalCheck
    [cnfKeepRule CNFWorkState.finalCheck cnfBoundaryGuard
      CNFWorkState.accept .stay]

private def literalModeRules (alreadySatisfied positive : Bool) :
    List WorkRule :=
  let index := CNFWorkState.literalIndex alreadySatisfied positive
  let toBoundary :=
    CNFWorkState.literalIndexToBoundary alreadySatisfied positive
  let pastCounter :=
    CNFWorkState.literalIndexPastCertificateCounter alreadySatisfied positive
  let markAssignment :=
    CNFWorkState.literalMarkAssignment alreadySatisfied positive
  let returnAssignment :=
    CNFWorkState.literalReturnAssignment alreadySatisfied positive
  let returnCounter :=
    CNFWorkState.literalReturnCertificateCounter alreadySatisfied positive
  let returnSign :=
    CNFWorkState.literalReturnSeekSign alreadySatisfied positive
  let returnIndex :=
    CNFWorkState.literalReturnSeekIndex alreadySatisfied positive
  let lookupBoundary :=
    CNFWorkState.literalLookupToBoundary alreadySatisfied positive
  let lookupPastCounter :=
    CNFWorkState.literalLookupPastCertificateCounter alreadySatisfied positive
  let lookupAssignment :=
    CNFWorkState.literalLookupAssignment alreadySatisfied positive
  cnfCompleteRules index
    [ cnfWorkRule index cnfT toBoundary cnfMarkTrue .right
    , cnfKeepRule index cnfF lookupBoundary .right ] ++
  cnfCompleteRules toBoundary
    (keepMany toBoundary toBoundary .right
        [cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule toBoundary cnfBoundaryGuard pastCounter .right]) ++
  cnfCompleteRules pastCounter
    (keepMany pastCounter pastCounter .right [cnfMarkFalse] ++
      [cnfKeepRule pastCounter cnfFinish markAssignment .right]) ++
  cnfCompleteRules markAssignment
    (keepMany markAssignment markAssignment .right [cnfMarkFalse, cnfMarkTrue] ++
      [ cnfWorkRule markAssignment cnfF returnAssignment cnfMarkFalse .left
      , cnfWorkRule markAssignment cnfT returnAssignment cnfMarkTrue .left
      , cnfKeepRule markAssignment cnfRootGuard
          (CNFWorkState.literalRestoreAssignment alreadySatisfied positive)
          .left ]) ++
  cnfCompleteRules returnAssignment
    (keepMany returnAssignment returnAssignment .left [cnfMarkFalse, cnfMarkTrue] ++
      [cnfKeepRule returnAssignment cnfFinish returnCounter .left]) ++
  cnfCompleteRules returnCounter
    (keepMany returnCounter returnCounter .left [cnfMarkFalse] ++
      [cnfKeepRule returnCounter cnfBoundaryGuard returnSign .left]) ++
  cnfCompleteRules returnSign
    (keepMany returnSign returnSign .left
        [cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule returnSign cnfBoundaryGuard returnIndex .right]) ++
  cnfCompleteRules returnIndex
    (keepMany returnIndex returnIndex .right [cnfMarkTrue] ++
      [ cnfKeepRule returnIndex cnfT index .stay
      , cnfKeepRule returnIndex cnfF index .stay ]) ++
  cnfCompleteRules lookupBoundary
    (keepMany lookupBoundary lookupBoundary .right
        [cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfKeepRule lookupBoundary cnfBoundaryGuard lookupPastCounter .right]) ++
  cnfCompleteRules lookupPastCounter
    (keepMany lookupPastCounter lookupPastCounter .right [cnfMarkFalse] ++
      [cnfKeepRule lookupPastCounter cnfFinish lookupAssignment .right]) ++
  cnfCompleteRules lookupAssignment
    (keepMany lookupAssignment lookupAssignment .right
        [cnfMarkFalse, cnfMarkTrue] ++
      [ cnfKeepRule lookupAssignment cnfF
          (CNFWorkState.literalRestoreAssignment
            (alreadySatisfied || !positive) positive) .left
      , cnfKeepRule lookupAssignment cnfT
          (CNFWorkState.literalRestoreAssignment
            (alreadySatisfied || positive) positive) .left
      , cnfKeepRule lookupAssignment cnfRootGuard
          (CNFWorkState.literalRestoreAssignment alreadySatisfied positive)
          .left ])

private def literalRestoreRules (result positive : Bool) : List WorkRule :=
  let restoreAssignment :=
    CNFWorkState.literalRestoreAssignment result positive
  let restoreCounter :=
    CNFWorkState.literalRestoreCertificateCounter result positive
  let restoreSign := CNFWorkState.literalRestoreSeekSign result positive
  let restoreIndex := CNFWorkState.literalRestoreIndex result positive
  cnfCompleteRules restoreAssignment
    [ cnfWorkRule restoreAssignment cnfMarkFalse restoreAssignment cnfF .left
    , cnfWorkRule restoreAssignment cnfMarkTrue restoreAssignment cnfT .left
    , cnfKeepRule restoreAssignment cnfFinish restoreCounter .left ] ++
  cnfCompleteRules restoreCounter
    (keepMany restoreCounter restoreCounter .left [cnfMarkFalse] ++
      [cnfKeepRule restoreCounter cnfBoundaryGuard restoreSign .left]) ++
  cnfCompleteRules restoreSign
    (keepMany restoreSign restoreSign .left
        [cnfMarkTrue, cnfF, cnfT, cnfSep, cnfFinish] ++
      [cnfWorkRule restoreSign cnfBoundaryGuard restoreIndex
        (if positive then cnfT else cnfF) .right]) ++
  cnfCompleteRules restoreIndex
    [ cnfWorkRule restoreIndex cnfMarkTrue restoreIndex cnfT .right
    , cnfKeepRule restoreIndex cnfF
        (CNFWorkState.clauseContinue result) .right ]

private def allLiteralRules : List WorkRule :=
  literalModeRules false false ++
  literalModeRules false true ++
  literalModeRules true false ++
  literalModeRules true true ++
  literalRestoreRules false false ++
  literalRestoreRules false true ++
  literalRestoreRules true false ++
  literalRestoreRules true true

/-- The complete finite rule table.  Specific rules precede their total reject
suffix, and state ranges are disjoint across phases. -/
def cnfWorkRules : List WorkRule :=
  cnfBootRules ++ frameOneRules ++ frameTwoRules ++ seekAndWidthRules ++
    clauseRules ++ allLiteralRules

/-- Direct finite work-machine CNF verifier. -/
def cnfWorkMachine : WorkMachine :=
  { rules := cnfWorkRules
    startState := CNFWorkState.boot
    acceptState := CNFWorkState.accept
    rejectState := CNFWorkState.reject }

/-- Literal raw machine obtained from the generic six-step compiler. -/
def cnfCompiledMachine : Machine := compileWorkMachine cnfWorkMachine

/-! ### Explicit polynomial budgets -/

/-- `8 + 64 * (n + 2)^3`, a deliberately loose work-transition bound. -/
def cnfWorkStepPolynomial : NatPolynomial :=
  let shifted : NatPolynomial := .add .variable (.constant 2)
  .add (.constant 8)
    (.mul (.constant 64) (.mul (.mul shifted shifted) shifted))

/-- Six raw transitions implement one work transition. -/
def cnfCompiledStepPolynomial : NatPolynomial :=
  .mul (.constant 6) cnfWorkStepPolynomial

/-- A paired input whose two components are each bounded by `n` has raw size
at most `6*n+6`; substitution makes that transport syntactic and auditable. -/
def cnfInputStepPolynomial : NatPolynomial :=
  NatPolynomial.substitute cnfCompiledStepPolynomial
    (NatPolynomial.linear 6 6)

theorem cnfWorkStepPolynomial_eval (n : Nat) :
    cnfWorkStepPolynomial.eval n =
      8 + 64 * ((n + 2) * (n + 2) * (n + 2)) := rfl

theorem cnfCompiledStepPolynomial_eval (n : Nat) :
    cnfCompiledStepPolynomial.eval n =
      6 * (8 + 64 * ((n + 2) * (n + 2) * (n + 2))) := rfl

theorem cnfInputStepPolynomial_eval (n : Nat) :
    cnfInputStepPolynomial.eval n =
      6 * (8 + 64 * (((6 * n + 6) + 2) * ((6 * n + 6) + 2) *
        ((6 * n + 6) + 2))) := rfl

def cnfWorkFuel (input certificate : BitString) : Nat :=
  cnfWorkStepPolynomial.eval (BitString.size (BitString.pair input certificate))

def cnfCompiledFuel (input certificate : BitString) : Nat :=
  cnfCompiledStepPolynomial.eval
    (BitString.size (BitString.pair input certificate))

def cnfWorkDecide (input certificate : BitString) : WorkVerdict :=
  workBoundedDecide cnfWorkMachine (cnfWorkFuel input certificate)
    (pairedWorkTape input certificate)

def cnfCompiledDecide (input certificate : BitString) : Verdict :=
  boundedDecide cnfCompiledMachine (cnfCompiledFuel input certificate)
    (BitString.pair input certificate)

/-! Executable sanity checks.  These are anonymous so they do not enlarge the
public proof transcript. -/

example :
    cnfCompiledMachine.acceptState =
      (compileWorkMachine cnfWorkMachine).acceptState := rfl

end PNP.Concrete
