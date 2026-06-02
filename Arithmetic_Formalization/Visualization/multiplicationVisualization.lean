import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.Multiplication
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

-- Renders the active partial product row in yellow, and completed rows normally
def carryBox (c : Nat) : Html :=
  if c > 0 then
    Html.element "div"
      #[("style", json% {
        display: "inline-block",
        width: "40px",
        height: "20px",
        textAlign: "center",
        fontSize: "14px",
        margin: "3px",
        color: "yellow"
      })]
      #[Html.text s!"{c}"]
  else
    Html.element "div"
      #[("style", json% {
        display: "inline-block",
        width: "40px",
        height: "20px",
        textAlign: "center",
        fontSize: "14px",
        margin: "3px",
        color: "transparent"
      })]
      #[Html.text " "]

-- 2. Calculates the specific carries for the top number (a) times a single digit
def carryRow (a : MultiDigit) (multiplier : Nat) : Html :=
  -- FIX: Removed .reverse. We fold naturally over the little-endian list (ones, tens, hundreds)
  let (_, htmlBoxes) := a.foldl (init := (0, [])) fun (carry, accList) d =>
    let prod := d.val * multiplier + carry
    let nextCarry := prod / 10
    (nextCarry, carryBox carry :: accList)

  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "row",
      justifyContent: "flex-end",
      marginBottom: "2px"
    })]
    htmlBoxes.toArray

-- 3. Renders the active partial product row in yellow, and completed rows normally
def partialProductRow (pp : MultiDigit) (isActive : Bool) : Html :=
  if isActive then
    -- UI mapping still uses .reverse to draw left-to-right visually
    let digits := (pp.reverse.map (fun d => digitBoxActive d.val)).toArray
    Html.element "div"
      #[("style", json% {
        display: "flex",
        flexDirection: "row",
        justifyContent: "flex-end"
      })]
      digits
  else
    numberRow pp


-- Helper to format a list of numbers into an explicit addition string (e.g., "615 + 4920")
def formatPPSum (list : List Nat) : String :=
  match list with
  | [] => "0"
  | n :: ns => ns.foldl (fun acc x => acc ++ s!" + {x}") s!"{n}"
-- Invariant panel for partial products
-- Invariant: Sum(PartialProducts[0..k]) = a × b[0..k]
def mulInvariantPanel (a b : MultiDigit) (visiblePPs : List MultiDigit) (step : Nat) (isFinalPhase : Bool) : Html :=
  let k := if isFinalPhase then b.length else step + 1
  let ppValues := visiblePPs.map toNat
  let actualSum := toNat (sumAll visiblePPs)
  let valA := toNat a
  let valBPrefix := toNatPrefix b k
  let targetValue := valA * valBPrefix
  let holds := actualSum == targetValue

  -- 1. Pre-compute the green/red verification boxes
  let finalVerificationBox : Html :=
    if holds then
      Html.element "div"
        #[("style", json% { color: "#4caf50", fontSize: "14px", fontWeight: "bold", marginTop: "8px" })]
        #[Html.text "✓ Multiplication rigorously verified"]
    else
      Html.element "div"
        #[("style", json% { color: "#f44336", fontSize: "14px", fontWeight: "bold", marginTop: "8px" })]
        #[Html.text "✗ Verification failed"]

  let intermediateVerificationBox : Html :=
    if holds then
      Html.element "div"
        #[("style", json% { color: "#4caf50", fontSize: "14px", fontWeight: "bold" })]
        #[Html.text "✓ Invariant holds"]
    else
      Html.element "div"
        #[("style", json% { color: "#f44336", fontSize: "14px", fontWeight: "bold" })]
        #[Html.text "✗ Invariant violated"]

  -- 2. Pre-compute the content structures
  let finalContent : Html :=
    Html.element "div" #[] #[
      Html.element "div" #[("style", json% { color: "#4caf50", marginBottom: "8px", fontSize: "14px", fontWeight: "bold" })] #[Html.text "★ Final Correctness Theorem:"],
      Html.element "div" #[("style", json% { marginBottom: "5px", color: "#aaa" })] #[Html.text "Final Result = a × b"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "3px" })] #[Html.text s!"{actualSum} = {valA} × {toNat b}"],
      finalVerificationBox
    ]
  let intermediateContent : Html :=
    Html.element "div" #[] #[
      Html.element "div" #[("style", json% { color: "cyan", marginBottom: "8px", fontSize: "14px" })] #[Html.text s!"Invariant after step {step + 1}:"],
      Html.element "div" #[("style", json% { marginBottom: "5px", color: "#aaa" })] #[Html.text s!"Sum(PPs[0..{k-1}]) = a × b[0..{k-1}]"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "3px" })] #[Html.text s!"{formatPPSum ppValues} = {actualSum}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "8px" })] #[Html.text s!"{valA} × {valBPrefix} = {targetValue}"],
      intermediateVerificationBox
    ]
  -- 3. Select the active content
  let activeContent : Html := if isFinalPhase then finalContent else intermediateContent
  -- 4. FIX: Evaluate the entire json% style block conditionally so the macro gets raw strings
  let panelStyle := if isFinalPhase then
    json% {
      marginTop: "15px", padding: "10px", border: "2px solid #4caf50",
      color: "white", fontSize: "13px", fontFamily: "monospace",
      maxWidth: "380px", backgroundColor: "#161616"
    }
  else
    json% {
      marginTop: "15px", padding: "10px", border: "1px solid gray",
      color: "white", fontSize: "13px", fontFamily: "monospace",
      maxWidth: "380px", backgroundColor: "#161616"
    }
  -- 5. Final render using the pre-computed style variable
  Html.element "div"
    #[("style", panelStyle)]
    #[activeContent]


-- The main component, now supporting Final Addition and Proof Invariants
def mulVisualization (a b : MultiDigit) (step : Nat) : Html :=
  let allPPs := partialProducts a b 0
  let isFinalPhase := step >= b.length

  -- Grab only the rows calculated up to this point
  let visiblePPs := if isFinalPhase then allPPs else allPPs.take (step + 1)

  let ppHtml : Array Html := (visiblePPs.mapIdx (fun i pp =>
    partialProductRow pp (i == step && !isFinalPhase)
  )).toArray

  let activeMultiplierDigit :=
    match b.drop step with
    | d :: _ => d.val
    | [] => 0

  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "column",
      alignItems: "flex-end",
      width: "max-content",
      padding: "20px",
      backgroundColor: "#1e1e1e"
    })]
    #[
      if !isFinalPhase then
        carryRow a activeMultiplierDigit
      else
        Html.element "div" #[("style", json% { height: "26px" })] #[],

      numberRow a,

      Html.element "div"
        #[("style", json% { display: "flex", flexDirection: "row", alignItems: "center" })]
        #[
          Html.element "span"
            #[("style", json% { color: "white", fontSize: "24px", marginRight: "10px", fontFamily: "monospace" })]
            #[Html.text "×"],
          if !isFinalPhase then numberRowStepped b step else numberRow b
        ],

      Html.element "div"
        #[("style", json% { borderBottom: "2px solid white", width: "100%", margin: "10px 0" })]
        #[],

      Html.element "div"
        #[("style", json% { display: "flex", flexDirection: "column", alignItems: "flex-end" })]
        ppHtml,

      -- Final Addition Block
      if isFinalPhase then
        let finalSum := sumAll allPPs
        Html.element "div"
          #[("style", json% { display: "flex", flexDirection: "column", alignItems: "flex-end", width: "100%" })]
          #[
            Html.element "div"
              #[("style", json% { borderBottom: "2px solid white", width: "100%", margin: "10px 0" })]
              #[],

            Html.element "div"
              #[("style", json% { display: "flex", flexDirection: "row", alignItems: "center" })]
              #[
                Html.element "span"
                  #[("style", json% { color: "#00ff00", fontSize: "24px", marginRight: "10px", fontFamily: "monospace" })]
                  #[Html.text "+"],
                Html.element "div"
                  #[("style", json% { display: "flex", flexDirection: "row", justifyContent: "flex-end" })]
                  (finalSum.reverse.map (fun d =>
                    Html.element "div"
                      #[("style", json% {
                        display: "inline-block", border: "2px solid #00ff00", width: "40px", height: "40px",
                        textAlign: "center", lineHeight: "40px", fontSize: "20px", color: "#00ff00", margin: "3px", backgroundColor: "black"
                      })]
                      #[Html.text s!"{d.val}"]
                  )).toArray
              ]
          ]
      else
        Html.element "span" #[] #[],

      -- NEW: The Invariant Panel attached at the bottom
      mulInvariantPanel a b visiblePPs step isFinalPhase
    ]

-- Test Case: 123 × 45
#html mulVisualization [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] [⟨5, by omega⟩, ⟨4, by omega⟩,⟨3,by omega⟩] 0
#html mulVisualization [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] [⟨5, by omega⟩, ⟨4, by omega⟩,⟨3,by omega⟩] 1
#html mulVisualization [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] [⟨5, by omega⟩, ⟨4, by omega⟩,⟨3,by omega⟩] 2
#html mulVisualization [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] [⟨5, by omega⟩, ⟨4, by omega⟩,⟨3,by omega⟩] 3
