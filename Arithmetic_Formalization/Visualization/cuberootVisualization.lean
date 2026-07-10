import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.CuberootTrick
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

/-
  ## The cube root trick (perfect cubes, roots 1–99)

  Unlike the other visualisations this one shows the *execution* of the
  algorithm rather than a loop invariant. The trick has two independent parts,
  shown as steps:

    step 0 — units digit of the root, from the cube's units digit
             (the map d ↦ (d³ mod 10) is a bijection, so it inverts).
    step 1 — tens digit of the root: divide the cube by 1000 and take the
             largest d with d³ ≤ that quotient.
    step 2 — combine:  root = 10·tens + units.

  All values come from the real `cubeRootTrick` / `cubeUnitsDigit` /
  `findCubeTensHelper` definitions.
-/

-- A digit box with configurable border / text colour.
def crDigitBox (d : String) (borderColor : String) (textColor : String) : Html :=
  let borderValue := s!"2px solid {borderColor}"
  Html.element "div"
    #[("style", json% {
      display: "inline-block", border: $(borderValue), width: "40px", height: "40px",
      textAlign: "center", lineHeight: "40px", fontSize: "20px", color: $(textColor),
      margin: "3px", backgroundColor: "transparent", borderRadius: "4px"
    })]
    #[Html.text d]

-- One line of explanatory text in the side panel.
def crLine (color : String) (txt : String) : Html :=
  Html.element "div"
    #[("style", json% { color: $(color), marginBottom: "6px", fontFamily: "monospace", fontSize: "14px" })]
    #[Html.text txt]

-- step 0 = units digit, step 1 = tens digit, step 2 = combined result.
def cubeRootVisualizer (n : MultiDigit) (step : Nat) : Html :=
  let cubeVal   := toNat n
  let c         := cubeVal % 10               -- units digit of the cube
  let (u, t)    := cubeRootTrick n            -- the actual algorithm
  let rootUnits := u.val
  let rootTens  := t.val
  let upper     := cubeVal / 1000
  let root      := 10 * rootTens + rootUnits
  let digitsMSB := n.reverse.map (fun d => d.val)
  let maxIdx    := n.length - 1

  -- The cube's digits. step 0 highlights the units digit; step 1 highlights
  -- the thousands-and-above part (everything except the last three digits).
  let cubeBoxes := (digitsMSB.mapIdx (fun i d =>
      let listIdx := maxIdx - i
      let active : Bool :=
        if step == 0 then listIdx == 0
        else if step == 1 then decide (3 ≤ listIdx)
        else false
      if active then crDigitBox s!"{d}" "yellow" "yellow"
      else crDigitBox s!"{d}" "#555" "#888")).toArray

  -- The root being assembled: [tens][units]. Units is known from step 0,
  -- tens from step 1.
  let tensBox :=
    if 1 ≤ step then crDigitBox s!"{rootTens}" "#4caf50" "#4caf50"
    else crDigitBox "?" "#444" "#666"
  let unitsBox := crDigitBox s!"{rootUnits}" "#4caf50" "#4caf50"

  -- The side panel: explanatory text for the current step.
  let panel : Html :=
    if step == 0 then
      Html.element "div" #[] #[
        crLine "#ff8c00" "Step 1 — units digit of the root",
        crLine "#aaa"    s!"The cube {cubeVal} ends in {c}.",
        crLine "yellow"  s!"{rootUnits}³ = {rootUnits ^ 3}, which ends in {(rootUnits ^ 3) % 10}.",
        crLine "#4caf50" s!"→ the root ends in {rootUnits}."
      ]
    else if step == 1 then
      Html.element "div" #[] #[
        crLine "#ff8c00" "Step 2 — tens digit of the root",
        crLine "#aaa"    s!"Drop the last three digits:  {cubeVal} / 1000 = {upper}.",
        crLine "#aaa"    s!"Find the largest d with d³ ≤ {upper}:",
        crLine "yellow"  s!"{rootTens}³ = {rootTens ^ 3} ≤ {upper} < {(rootTens + 1) ^ 3} = {rootTens + 1}³",
        crLine "#4caf50" s!"→ the tens digit is {rootTens}."
      ]
    else
      Html.element "div" #[] #[
        crLine "#ff8c00" "Result",
        crLine "yellow"  s!"root = 10 × {rootTens} + {rootUnits} = {root}",
        (if root ^ 3 == cubeVal then
          crLine "#4caf50" s!"check: {root}³ = {root ^ 3} = {cubeVal} ✓"
         else
          crLine "#f44336" s!"check: {root}³ = {root ^ 3} ≠ {cubeVal} (not a perfect cube)")
      ]

  Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", padding: "20px", backgroundColor: "#0d0d0d" })] #[
    Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] #[
      Html.element "div" #[("style", json% { color: "#ff8c00", fontFamily: "monospace", fontSize: "16px", marginBottom: "8px" })]
        #[Html.text "Cube root trick"],
      -- the perfect cube
      Html.element "div" #[("style", json% { color: "#888", fontFamily: "monospace", fontSize: "12px", marginBottom: "2px" })]
        #[Html.text "perfect cube"],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", marginBottom: "14px" })] cubeBoxes,
      -- the root being assembled
      Html.element "div" #[("style", json% { color: "#888", fontFamily: "monospace", fontSize: "12px", marginBottom: "2px" })]
        #[Html.text "root  (tens · units)"],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row" })] #[tensBox, unitsBox]
    ],
    Html.element "div" #[("style", json% {
      marginLeft: "24px", padding: "15px", border: "1px solid gray", color: "white",
      backgroundColor: "#161616", borderRadius: "6px", minWidth: "320px", height: "max-content"
    })] #[panel]
  ]

-- 54³ = 157464  (units 4 → root units 4; 157464/1000 = 157, 5³=125 ≤ 157 < 216 → tens 5)
#html cubeRootVisualizer (fromNat (54 ^ 3)) 0
#html cubeRootVisualizer (fromNat (54 ^ 3)) 1
#html cubeRootVisualizer (fromNat (54 ^ 3)) 2

-- 12³ = 1728  (units 8 → root units 2; 1728/1000 = 1, 1³=1 ≤ 1 < 8 → tens 1)
#html cubeRootVisualizer (fromNat (12 ^ 3)) 0
#html cubeRootVisualizer (fromNat (12 ^ 3)) 1
#html cubeRootVisualizer (fromNat (12 ^ 3)) 2

-- 99³ = 970299
#html cubeRootVisualizer (fromNat (99 ^ 3)) 0
#html cubeRootVisualizer (fromNat (99 ^ 3)) 1
#html cubeRootVisualizer (fromNat (99 ^ 3)) 2
