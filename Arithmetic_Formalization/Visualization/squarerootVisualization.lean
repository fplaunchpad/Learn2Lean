import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.Squareroot
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

def sqrtDigitBox (d : String) (borderColor : String) (textColor : String) : Html :=
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

-- Everything the UI needs to render one step of the pen-and-paper algorithm.
-- All values are plain Nats; the root digit itself is computed by the REAL
-- findSqrtDigit from Squareroot.lean, so the picture is driven by the algorithm.
structure SqrtStepState where
  x : Nat   -- root digit found this step
  pairVal      : Nat   -- the two-digit pair brought down
  currentRem   : Nat   -- remainder after bringing the pair down (rem·100 + pair)
  trialDivisor : Nat   -- 2q·10 + x
  trialProduct : Nat   -- (2q·10 + x)·x, the amount subtracted
  newRem       : Nat   -- remainder after subtraction
  qAfter       : Nat   -- partial root after appending x
deriving Inhabited

-- Group an MSB-first digit list into pairs from the LEFT.
-- Mirrors chunkPairs: an odd-length number gets a singleton LEADING group
-- (chunkPairs pads it with a zero; for display we just show one digit).
def pairsOfMSB : List Nat → List (List Nat)
  | []              => []
  | [d]             => [[d]]
  | d1 :: d2 :: ds  => [d1, d2] :: pairsOfMSB ds
termination_by ds => ds.length

def groupPairsMSB (ds : List Nat) : List (List Nat) :=
  if ds.length % 2 == 1 then
    match ds with
    | []        => []
    | d :: rest => [d] :: pairsOfMSB rest
  else
    pairsOfMSB ds

-- Replay sqrtHelper over the MSB-first pair values, recording every step.
-- The digit search delegates to the actual findSqrtDigit from the formalization.
def computeSqrtStates (pairVals : List Nat) : Array SqrtStepState :=
  let init : Array SqrtStepState × Nat × Nat := (#[], 0, 0)
  (pairVals.foldl (fun acc p =>
    let (arr, rem, q) := acc
    let currentRem := rem * 100 + p
    let x := (findSqrtDigit currentRem (fromNat q)).val
    let trialDivisor := 20 * q + x
    let trialProduct := trialDivisor * x
    let newRem := currentRem - trialProduct
    let qAfter := q * 10 + x
    (arr.push {
        x := x, pairVal := p, currentRem := currentRem,
        trialDivisor := trialDivisor, trialProduct := trialProduct,
        newRem := newRem, qAfter := qAfter },
     newRem, qAfter)
  ) init).1

def sqrtCalcStepLine (stepIdx : Nat) (currentStep : Nat) (st : SqrtStepState) : Html :=
  let isActive := stepIdx == currentStep
  let isPast := stepIdx < currentStep
  let baseColor := if isActive then "yellow" else (if isPast then "#00aaff" else "#555555")
  let bgColor := if isActive then "#2a2a00" else "transparent"
  let remColor := if isActive then "cyan" else (if isPast then "cyan" else "#555555")
  let qBefore := st.qAfter / 10
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
      Html.text s!"↓ bring down {st.pairVal} → {st.currentRem}   (20×{qBefore}+{st.x})×{st.x} = {st.trialDivisor}×{st.x} = {st.trialProduct}  rem ",
      Html.element "span" #[("style", json% { color: $(remColor) })] #[Html.text s!"{st.newRem}"]
    ]

-- Invariant after step k (the sqrt analog of division's prefix invariant):
--   value of the first k+1 pairs = (partial root)² + rem
def sqrtInvariantPanel (step : Nat) (prefixVal : Nat) (qVal : Nat) (rem : Nat) : Html :=
  let holds := prefixVal == qVal * qVal + rem
  let verdictBox : Html :=
    if holds then
      Html.element "div" #[("style", json% { color: "#4caf50", fontWeight: "bold" })] #[Html.text "✓ Invariant holds"]
    else
      Html.element "div" #[("style", json% { color: "#f44336", fontWeight: "bold" })] #[Html.text "✗ Invariant violated"]
  Html.element "div"
    #[("style", json% {
      marginLeft: "20px", padding: "15px", border: "1px solid gray",
      color: "white", fontSize: "14px", fontFamily: "monospace",
      backgroundColor: "#161616", borderRadius: "6px", minWidth: "300px",
      height: "max-content"
    })]
    #[
      Html.element "div" #[("style", json% { color: "cyan", marginBottom: "12px", fontWeight: "bold" })] #[Html.text s!"Invariant after step {step + 1}:"],
      Html.element "div" #[("style", json% { marginBottom: "8px", color: "#aaa" })] #[Html.text s!"pairs(a, {step + 1}) = root[0..{step}]² + rem"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "8px" })] #[Html.text s!"{prefixVal} = {qVal}² + {rem}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "12px" })] #[Html.text s!"{prefixVal} = {qVal * qVal + rem}"],
      verdictBox
    ]

-- Main component. a is LSB-first (like the algorithm); step indexes the
-- pair being processed, MSB-first — exactly the order sqrtHelper consumes them.
def sqrtStateVisualizer (a : MultiDigit) (step : Nat) : Html :=
  let digitsMSB := a.reverse.map (fun d => d.val)
  let groups := groupPairsMSB digitsMSB
  let pairVals := groups.map (fun g => g.foldl (fun acc d => acc * 10 + d) 0)
  let states := computeSqrtStates pairVals
  let cur : SqrtStepState := states.getD step default
  -- Invariant values: the number formed by the pairs consumed so far,
  -- and the partial root / remainder after the current step.
  let prefixVal := (pairVals.take (step + 1)).foldl (fun acc p => acc * 100 + p) 0
  -- One root digit sits centered above each pair group.
  -- A digit box occupies 50px (40 width + 4 border + 6 margin).
  let rootBoxes := (groups.mapIdx (fun i g =>
    let w := s!"{50 * g.length}px"
    let inner :=
      if i < step then
        sqrtDigitBox s!"{(states.getD i default).x}" "gray" "yellow"
      else if i == step then
        sqrtDigitBox s!"{(states.getD i default).x}" "yellow" "yellow"
      else
        sqrtDigitBox "?" "#333" "#555"
    Html.element "div"
      #[("style", json% { width: $(w), display: "flex", justifyContent: "center", marginRight: "12px" })]
      #[inner]
  )).toArray
  -- The radicand, grouped into its pen-and-paper pairs.
  let pairBoxes := (groups.mapIdx (fun i g =>
    let (borderC, textC) :=
      if i < step then ("white", "white")
      else if i == step then ("yellow", "yellow")
      else ("#444", "#444")
    Html.element "div"
      #[("style", json% { display: "flex", flexDirection: "row", marginRight: "12px" })]
      ((g.map (fun d => sqrtDigitBox s!"{d}" borderC textC)).toArray)
  )).toArray
  let calcLogs := (states.mapIdx (fun i st =>
    if i <= step then
      sqrtCalcStepLine i step st
    else
      Html.element "span" #[] #[]
  ))
  Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", padding: "20px", backgroundColor: "#0d0d0d" })] #[
    Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] #[
      -- Root digits, aligned over their pairs (40px = width of the √ sign area)
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", marginLeft: "40px", marginBottom: "5px" })] rootBoxes,
      -- √ sign + overline + the radicand grouped in pairs
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", alignItems: "flex-end", marginBottom: "20px" })] #[
        Html.element "div" #[("style", json% { color: "#ff8c00", fontSize: "34px", fontFamily: "monospace", width: "30px", textAlign: "right", marginRight: "10px" })] #[Html.text "√"],
        Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", borderTop: "2px solid #ff8c00", paddingTop: "4px" })] pairBoxes
      ],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] calcLogs
    ],
    sqrtInvariantPanel step prefixVal cur.qAfter cur.newRem
  ]

-- √1234 = 35 rem 9: pairs 12 | 34
-- step 0: bring down 12, x=3 (3²=9 ≤ 12), rem 3
-- step 1: bring down 34 → 334, x=5 ((60+5)·5=325 ≤ 334), rem 9
#html sqrtStateVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 0
#html sqrtStateVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 1

-- √12345 = 111 rem 24: odd length, pairs 1 | 23 | 45 (leading singleton)
#html sqrtStateVisualizer [⟨5, by omega⟩, ⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 0
#html sqrtStateVisualizer [⟨5, by omega⟩, ⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 1
#html sqrtStateVisualizer [⟨5, by omega⟩, ⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 2

-- √9999 = 99 rem 198: pairs 99 | 99
#html sqrtStateVisualizer [⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩] 0
#html sqrtStateVisualizer [⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩] 1

#html sqrtStateVisualizer [⟨6, by omega⟩, ⟨9, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 0
#html sqrtStateVisualizer [⟨6, by omega⟩, ⟨9, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 1
