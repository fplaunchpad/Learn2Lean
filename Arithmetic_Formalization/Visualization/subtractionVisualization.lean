import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.Subtraction
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

def computeBorrows (a b : MultiDigit) : List Bool :=
  let rec go : MultiDigit → MultiDigit → Bool → List Bool
    | [], [], _ => []
    | [], b :: bs, borrow =>
        let (_, borrow') := subDigits ⟨0, by omega⟩ b borrow
        borrow' :: go [] bs borrow'
    | a :: as, [], borrow =>
        let (_, borrow') := subDigits a ⟨0, by omega⟩ borrow
        borrow' :: go as [] borrow'
    | a :: as, b :: bs, borrow =>
        let (_, borrow') := subDigits a b borrow
        borrow' :: go as bs borrow'
    termination_by a b _ => a.length + b.length
  let borrows := go a b false
  match borrows with
  | [] => []
  | _ :: _ => false :: borrows.dropLast

def getBorrowAt (a b : MultiDigit) (k : Nat) : Bool :=
  let borrows := computeBorrows a b
  borrows.getD k false

-- 214 - 91: borrow in tens column
#eval computeBorrows (fromNat 214) (fromNat 91)
-- expect [false, false, true] --

-- 123 - 91: borrow needed
#eval computeBorrows (fromNat 123) (fromNat 91)
-- expect [false, false, true]

-- 100 - 1: borrow cascades through tens and hundreds
#eval computeBorrows (fromNat 100) (fromNat 1)
-- units: 0 - 1, borrow out
-- tens: 0 - 0 - 1(borrow), borrow out again
-- hundreds: 1 - 0 - 1(borrow) = 0
-- borrow INTO: [false, true, true]

-- Borrow indicator box -- red instead of yellow to distinguish from carry
def borrowBox (b : Bool) : Html :=
  if b then
    Html.element "div"
      #[("style", json% {
        display: "inline-block",
        width: "40px",
        height: "20px",
        textAlign: "center",
        fontSize: "14px",
        color: "red",
        margin: "3px"
      })]
      #[Html.text "1"]
  else
    Html.element "div"
      #[("style", json% {
        display: "inline-block",
        width: "40px",
        height: "20px",
        textAlign: "center",
        fontSize: "14px",
        color: "transparent",
        margin: "3px"
      })]
      #[Html.text " "]

-- Borrow row
def borrowRow (borrows : List Bool) : Html :=
  let boxes := (borrows.reverse.map borrowBox).toArray
  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "row",
      justifyContent: "flex-end"
    })]
    boxes

-- Digit box with strikethrough showing original value being crossed out
def digitBoxStrikethrough (original : Nat) (newVal : Nat) : Html :=
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      border: "2px solid red",
      width: "40px",
      height: "40px",
      textAlign: "center",
      margin: "3px",
      position: "relative",
      backgroundColor: "black"
    })]
    #[
      -- original value with strikethrough
      Html.element "span"
        #[("style", json% {
          textDecoration: "line-through",
          color: "red",
          fontSize: "20px"
        })]
        #[Html.text s!"{original}"],
      -- new reduced value superscript
      Html.element "span"
        #[("style", json% {
          position: "absolute",
          top: "2px",
          right: "4px",
          fontSize: "12px",
          color: "yellow"
        })]
        #[Html.text s!"{newVal}"]
    ]

-- Digit that received a borrow -- shows +10 superscript
def digitBoxBorrowTaker (d : Nat) : Html :=
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      border: "2px solid yellow",
      width: "40px",
      height: "40px",
      textAlign: "center",
      margin: "3px",
      position: "relative",
      backgroundColor: "black"
    })]
    #[
      -- main digit value
      Html.element "div"
        #[("style", json% {
          color: "yellow",
          fontSize: "18px",
          lineHeight: "40px"
        })]
        #[Html.text s!"{d}"],
      -- +10 superscript top left
      Html.element "div"
        #[("style", json% {
          position: "absolute",
          top: "1px",
          left: "2px",
          fontSize: "10px",
          color: "cyan"
        })]
        #[Html.text "+10"]
    ]

-- For each position in a, compute whether it was borrowed from
-- and what its effective value is at display time
structure DigitDisplay where
  original : Nat
  effective : Nat
  wasBorrowed : Bool    -- this digit gave a borrow (reduced by 1)
  receivesBorrow : Bool -- this digit takes a borrow (gets +10)

def computeDigitDisplays (a : MultiDigit) (borrows : List Bool) : List DigitDisplay :=
  a.mapIdx (fun i d =>
    -- digit at position i was borrowed FROM if position i+1 had a borrow in
    let gave := borrows.getD (i + 1) false
    -- digit at position i receives a borrow if position i had a borrow in
    let receives := borrows.getD i false
    { original := d.val,
      effective := if gave then (if d.val = 0 then 9 else d.val - 1) else d.val,
      wasBorrowed := gave,
      receivesBorrow := receives }
  )

-- Normal digit box
def digitBoxNormal (d : Nat) : Html :=
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      border: "2px solid gray",
      width: "40px",
      height: "40px",
      textAlign: "center",
      lineHeight: "40px",
      fontSize: "20px",
      color: "gray",
      margin: "3px",
      backgroundColor: "black"
    })]
    #[Html.text s!"{d}"]

-- Active digit box (currently being processed)
def digitBoxCurrent (d : Nat) : Html :=
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      border: "2px solid yellow",
      width: "40px",
      height: "40px",
      textAlign: "center",
      lineHeight: "40px",
      fontSize: "20px",
      color: "yellow",
      margin: "3px",
      backgroundColor: "black"
    })]
    #[Html.text s!"{d}"]

-- Borrowed digit box showing strikethrough and reduced value
-- Borrowed digit box with orange strikethrough
def digitBoxBorrowed (original : Nat) (reduced : Nat) : Html :=
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      border: "2px solid orange",
      width: "40px",
      height: "40px",
      textAlign: "center",
      margin: "3px",
      position: "relative",
      backgroundColor: "black"
    })]
    #[
      Html.element "div"
        #[("style", json% {
          textDecoration: "line-through",
          color: "orange",
          fontSize: "18px",
          lineHeight: "40px"
        })]
        #[Html.text s!"{original}"],
      Html.element "div"
        #[("style", json% {
          position: "absolute",
          top: "1px",
          right: "3px",
          fontSize: "11px",
          color: "yellow"
        })]
        #[Html.text s!"{reduced}"]
    ]

-- Borrow OUT of each column (before shift)
def computeBorrowsOut (a b : MultiDigit) : List Bool :=
  let rec go : MultiDigit → MultiDigit → Bool → List Bool
    | [], [], _ => []
    | [], b :: bs, borrow =>
        let (_, borrow') := subDigits ⟨0, by omega⟩ b borrow
        borrow' :: go [] bs borrow'
    | a :: as, [], borrow =>
        let (_, borrow') := subDigits a ⟨0, by omega⟩ borrow
        borrow' :: go as [] borrow'
    | a :: as, b :: bs, borrow =>
        let (_, borrow') := subDigits a b borrow
        borrow' :: go as bs borrow'
    termination_by a b _ => a.length + b.length
  go a b false
-- No shift -- raw borrow OUT of each column

-- Render the top number in subtraction with full visual state
def subNumberRow (a : MultiDigit) (borrowsOut : List Bool) (step : Nat) : Html :=
  let maxIdx := a.length - 1
  let boxes := (a.reverse.mapIdx (fun i d =>
    let listIdx := maxIdx - i
    let tookBorrow := borrowsOut.getD listIdx false
    -- this column gave a borrow if the column to its right took one
    let gaveBorrow := if listIdx > 0
                      then borrowsOut.getD (listIdx - 1) false
                      else false
    let reduced := if d.val = 0 then 9 else d.val - 1
    if listIdx > step + 1 then
      -- not yet reached
      digitBoxNormal d.val
    else if listIdx = step + 1 then
      -- one ahead: show strikethrough if giving borrow right now
      if gaveBorrow then
        digitBoxBorrowed d.val reduced
      else
        digitBoxNormal d.val
    else if listIdx = step then
      -- currently active
      if tookBorrow then
        digitBoxBorrowTaker d.val
      else if gaveBorrow then
        -- active AND gave a borrow (cascading case)
        digitBoxBorrowed d.val reduced
      else
        digitBoxCurrent d.val
    else
      -- already processed -- keep strikethrough if it ever gave a borrow
      if gaveBorrow then
        digitBoxBorrowed d.val reduced
      else
        digitBoxActive d.val
  )).toArray
  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "row",
      justifyContent: "flex-end"
    })]
    boxes

-- Invariant: a[0..k-1] + borrow × 10^k = result[0..k-1] + b[0..k-1]
def subInvariantPanel (a b : MultiDigit) (step : Nat) : Html :=
  let result := verticalSub a b false
  let maxLen := max (max a.length b.length) result.length
  let pad (x : MultiDigit) : MultiDigit :=
    List.append x (List.replicate (maxLen - x.length) ⟨0, by omega⟩)
  let paddedA := pad a
  let paddedB := pad b
  let paddedResult := pad result
  let k := step + 1
  let prefixA := toNatPrefix paddedA k
  let prefixB := toNatPrefix paddedB k
  let prefixResult := toNatPrefix paddedResult k
  let borrow := getBorrowAt a b (step + 1)
  let borrowNum := if borrow then 1 else 0
  let placeValue := Nat.pow 10 k
  -- correct invariant: a[0..k-1] + borrow × 10^k = result[0..k-1] + b[0..k-1]
  let lhs := prefixA + borrowNum * placeValue
  let rhs := prefixResult + prefixB
  let holds := lhs == rhs
  Html.element "div"
    #[("style", json% {
      marginTop: "15px",
      padding: "10px",
      border: "1px solid gray",
      color: "white",
      fontSize: "13px",
      fontFamily: "monospace",
      maxWidth: "300px"
    })]
    #[
      Html.element "div"
        #[("style", json% {
          color: "cyan",
          marginBottom: "8px",
          fontSize: "14px"
        })]
        #[Html.text s!"Invariant after step {step}:"],
      Html.element "div"
        #[("style", json% { marginBottom: "5px" })]
        #[Html.text s!"a[0..{k-1}] + borrow × 10^{k} = result[0..{k-1}] + b[0..{k-1}]"],
      Html.element "div"
        #[("style", json% { color: "yellow", marginBottom: "3px" })]
        #[Html.text s!"{prefixA} + {borrowNum} × {placeValue} = {prefixResult} + {prefixB}"],
      Html.element "div"
        #[("style", json% { color: "yellow", marginBottom: "8px" })]
        #[Html.text s!"{lhs} = {rhs}"],
      if holds then
        Html.element "div"
          #[("style", json% { color: "green", fontSize: "14px" })]
          #[Html.text "✓ Invariant holds"]
      else
        Html.element "div"
          #[("style", json% { color: "red", fontSize: "14px" })]
          #[Html.text "✗ Invariant violated"]
    ]

-- Full step by step subtraction display
def subtractionStepDisplay (a b : MultiDigit) (step : Nat) : Html :=
  let result := verticalSub a b false
  let borrowsOut := computeBorrowsOut a b
  let borrows := computeBorrows a b  -- still needed for borrowRow and invariant
  let maxLen := max (max a.length b.length) result.length
  let pad (x : MultiDigit) : MultiDigit :=
    List.append x (List.replicate (maxLen - x.length) ⟨0, by omega⟩)
  let paddedA := pad a
  let paddedB := pad b
  let paddedResult := pad result
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      padding: "15px",
      paddingLeft: "40px",
      backgroundColor: "black",
      color: "white",
      fontFamily: "monospace"
    })]
    #[
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center"
        })]
        #[subNumberRow paddedA borrowsOut step],
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center",
          position: "relative"
        })]
        #[
          Html.element "span"
            #[("style", json% {
              position: "absolute",
              left: "0px",
              top: "8px",
              color: "white",
              fontSize: "20px"
            })]
            #[Html.text "-"],
          numberRowStepped paddedB step
        ],
      Html.element "hr"
        #[("style", json% {
          border: "1px solid white",
          margin: "5px 0",
          width: "100%"
        })]
        #[],
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center"
        })]
        #[resultRowStepped paddedResult step],
      subInvariantPanel a b step
    ]
-- 214 - 91 = 123, borrow in tens column
#html subtractionStepDisplay (fromNat 714) (fromNat 93) 0
#html subtractionStepDisplay (fromNat 714) (fromNat 93) 1
#html subtractionStepDisplay (fromNat 714) (fromNat 93) 2

-- 100 - 1 = 99, cascading borrows
#html subtractionStepDisplay (fromNat 100) (fromNat 1) 0
#html subtractionStepDisplay (fromNat 100) (fromNat 1) 1
#html subtractionStepDisplay (fromNat 100) (fromNat 1) 2
