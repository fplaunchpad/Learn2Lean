import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.Division
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

def divDigitBox (d : String) (borderColor : String) (textColor : String) : Html :=
  let borderValue := s!"2px solid {borderColor}"

  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      border: $(borderValue),
      width: "40px",
      height: "40px",
      textAlign: "center",
      lineHeight: "40px",
      fontSize: "20px",
      color: $(textColor),
      margin: "3px",
      backgroundColor: "transparent",
      borderRadius: "4px"
    })]
    #[Html.text d]

def calcStepLine (stepIdx : Nat) (currentStep : Nat) (currentDiv : Nat) (divisor : Nat) (q : Nat) (rem : Nat) : Html :=
  let isActive := stepIdx == currentStep
  let isPast := stepIdx < currentStep
  let baseColor := if isActive then "yellow" else (if isPast then "#00aaff" else "#555555")
  let bgColor := if isActive then "#2a2a00" else "transparent"
  let remColor := if isActive then "cyan" else (if isPast then "cyan" else "#555555")

  Html.element "div"
    #[("style", json% {
      padding: "5px 10px",
      color: $(baseColor),
      backgroundColor: $(bgColor),
      fontFamily: "monospace",
      margin: "4px 0",
      borderRadius: "6px",
      width: "max-content",
      fontSize: "14px"
    })]
    #[
      Html.text s!"↓ {currentDiv} ÷ {divisor} = {q} ({divisor}×{q}={divisor * q})  rem ",
      Html.element "span" #[("style", json% { color: $(remColor) })] #[Html.text s!"{rem}"]
    ]

def divInvariantPanel (step : Nat) (prefixVal : Nat) (qVal : Nat) (divisor : Nat) (rem : Nat) : Html :=
  Html.element "div"
    #[("style", json% {
      marginLeft: "20px", padding: "15px", border: "1px solid gray",
      color: "white", fontSize: "14px", fontFamily: "monospace",
      backgroundColor: "#161616", borderRadius: "6px", minWidth: "300px"
    })]
    #[
      Html.element "div" #[("style", json% { color: "cyan", marginBottom: "12px", fontWeight: "bold" })] #[Html.text s!"Invariant after step {step + 1}:"],
      Html.element "div" #[("style", json% { marginBottom: "8px", color: "#aaa" })] #[Html.text s!"prefix(a, {step + 1}) = quotient[0..{step}] × {divisor} + rem"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "8px" })] #[Html.text s!"{prefixVal} = {qVal} × {divisor} + {rem}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "12px" })] #[Html.text s!"{prefixVal} = {qVal * divisor + rem}"],
      Html.element "div" #[("style", json% { color: "#4caf50", fontWeight: "bold" })] #[Html.text "✓ Invariant holds"]
    ]

def computeDivStates (dividend : Array Nat) (divisor : Nat) : Array (Nat × Nat × Nat) :=
  let initAcc : Array (Nat × Nat × Nat) × Nat := (#[], 0)
  (dividend.foldl (fun acc d =>
    let (accArray, prevRem) := acc
    let currentDiv := prevRem * 10 + d
    let q := currentDiv / divisor
    let newRem := currentDiv % divisor
    (accArray.push (q, currentDiv, newRem), newRem)
  ) initAcc).1

-- FIX 1: Signature updated to MultiDigit
def divisionStateVisualizer (dividend : MultiDigit) (divisor : Nat) (step : Nat) : Html :=
  -- FIX 2: Convert LSB-first MultiDigit into MSB-first Array for the algorithm loop
  let dividendArray := (dividend.reverse.map (fun d => d.val)).toArray

  let states := computeDivStates dividendArray divisor

  let (curQ, curDiv, curRem) := if h : step < states.size then states[step]! else (0, 0, 0)

  -- FIX 3: Calculate invariant values dynamically
  -- prefixVal: Take the MSB prefix up to the current step and compute base-10
  let prefixVal := (dividendArray.toList.take (step + 1)).foldl (fun acc d => acc * 10 + d) 0
  -- qVal: Accumulate the quotient digits computed up to the current step
  let qVal := (states.toList.take (step + 1)).foldl (fun acc s => acc * 10 + s.1) 0

  let qBoxes := (dividendArray.mapIdx (fun i _ =>
    if i < step then
      divDigitBox s!"{states[i]!.1}" "gray" "yellow"
    else if i == step then
      divDigitBox s!"{states[i]!.1}" "yellow" "yellow"
    else
      divDigitBox "?" "#333" "#555"
  ))

  let dBoxes := (dividendArray.mapIdx (fun i d =>
    if i < step then divDigitBox s!"{d}" "white" "white"
    else if i == step then divDigitBox s!"{d}" "yellow" "yellow"
    else divDigitBox s!"{d}" "#444" "#444"
  ))

  let calcLogs := (states.mapIdx (fun i state =>
    if i <= step then
      calcStepLine i step state.2.1 divisor state.1 state.2.2
    else
      Html.element "span" #[] #[]
  ))

  Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", padding: "20px", backgroundColor: "#0d0d0d" })] #[
    Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] #[

      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", marginLeft: "45px", marginBottom: "5px" })] qBoxes,
      Html.element "div" #[("style", json% { borderBottom: "1px solid white", width: "100%", marginBottom: "10px" })] #[],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", alignItems: "center", marginBottom: "20px" })] #[
        Html.element "div" #[("style", json% { color: "#ff8c00", fontSize: "22px", marginRight: "10px", fontFamily: "monospace" })] #[Html.text s!"{divisor}"],
        Html.element "div" #[("style", json% { borderLeft: "2px solid #ff8c00", height: "35px", marginRight: "10px", opacity: "0.7" })] #[],
        Html.element "div" #[("style", json% { display: "flex", flexDirection: "row" })] dBoxes
      ],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] calcLogs
    ],

    -- FIX 4: Feed the dynamic variables here
    divInvariantPanel step prefixVal qVal divisor curRem
  ]

-- Because we swapped to MultiDigit (LSB-first), your tests will look like this!
-- This simulates 1234 ÷ 5
#html divisionStateVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 5 0
#html divisionStateVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 5 1
#html divisionStateVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 5 2
#html divisionStateVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 5 3
