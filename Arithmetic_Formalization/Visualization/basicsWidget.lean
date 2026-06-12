import ProofWidgets
import Arithmetic_Formalization.Foundations

open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

def digitBox (d : Nat) : Html :=
  <div style={json% {
    display: "inline-block",
    border: "2px solid white",
    width: "40px",
    height: "40px",
    textAlign: "center",
    lineHeight: "40px",
    fontSize: "20px",
    color: "white",
    margin: "3px",
    backgroundColor: "black"
  }}>
    {.text s!"{d}"}
  </div>

#html digitBox 7

def numberRow (a : MultiDigit) : Html :=
  let digits := (a.reverse.map (fun d => digitBox d.val)).toArray
  Html.element "div" #[("style", json% {
    display: "flex",
    flexDirection: "row",
    justifyContent: "flex-end"
  })] digits




#html numberRow [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

def fromNat : Nat → MultiDigit
  | 0 => []
  | n + 1 => ⟨(n + 1) % 10, by omega⟩ :: fromNat ((n + 1) / 10)
termination_by n => n

def digitBoxActive (d : Nat) : Html :=
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

-- Grayed out digit box for inactive columns
def digitBoxInactive (d : Nat) : Html :=
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

def numberRowStepped (a : MultiDigit) (step : Nat) : Html :=
  let maxIdx := a.length - 1
  let boxes := (a.reverse.mapIdx (fun i d =>
    -- convert display index to list index
    let listIdx := maxIdx - i
    if listIdx = step
    then digitBoxActive d.val
    else digitBoxInactive d.val)).toArray
  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "row",
      justifyContent: "flex-end"
    })]
    boxes

-- Result box showing computed digit
def resultBoxComputed (d : Nat) : Html :=
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

-- Result box showing unknown digit
def resultBoxUnknown : Html :=
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
    #[Html.text "?"]

-- Result row: computed digits show actual value, future digits show ?
def resultRowStepped (result : MultiDigit) (step : Nat) : Html :=
  let maxIdx := result.length - 1
  let boxes := (result.reverse.mapIdx (fun i d =>
    let listIdx := maxIdx - i
    if listIdx ≤ step
    then resultBoxComputed d.val
    else resultBoxUnknown)).toArray
  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "row",
      justifyContent: "flex-end"
    })]
    boxes
