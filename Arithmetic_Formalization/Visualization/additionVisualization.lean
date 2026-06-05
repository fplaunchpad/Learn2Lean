import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.Addition
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

def computeCarries (a b : MultiDigit) : List Bool :=
  let rec go : MultiDigit → MultiDigit → Bool → List Bool
    | [], [], c =>
        -- include final carry if it exists
        if c then [true] else []
    | [], b :: bs, c =>
        let (_, c') := addDigits ⟨0, by omega⟩ b c
        c' :: go [] bs c'
    | a :: as, [], c =>
        let (_, c') := addDigits a ⟨0, by omega⟩ c
        c' :: go as [] c'
    | a :: as, b :: bs, c =>
        let (_, c') := addDigits a b c
        c' :: go as bs c'
    termination_by a b _ => a.length + b.length
  let carries := go a b false
  match carries with
  | [] => []
  | _ :: _ => false :: carries.dropLast

-- 123 + 91: carries should be [false, true, false] from right to left
#eval computeCarries
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [⟨1, by omega⟩, ⟨9, by omega⟩]
-- expect [false, true, false]

-- Render a single carry indicator above a column
def carryBox (c : Bool) : Html :=
  if c then
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
      #[Html.text "1"]
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


#html carryBox true
#html carryBox false
-- Render the full carry row
def carryRow (carries : List Bool) : Html :=
  let boxes := (carries.reverse.map carryBox).toArray
  Html.element "div"
    #[("style", json% {
      display: "flex",
      flexDirection: "row",
      justifyContent: "flex-end"
    })]
    boxes
#html carryRow [true, false, true]

def additionDisplay (a b : MultiDigit) : Html :=
  let result := verticalAdd a b false
  let carries := computeCarries a b
  let maxLen := max (max a.length b.length) result.length
  let pad (x : MultiDigit) : MultiDigit :=
    List.append x (List.replicate (maxLen - x.length) ⟨0, by omega⟩)
  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      padding: "15px",
      backgroundColor: "black",
      color: "white",
      fontFamily: "monospace"
    })]
    #[
      -- Carry row at top
      carryRow carries,
      -- First number
      numberRow (pad a),
      -- Plus sign and second number
      Html.element "div"
        #[("style", json% {
          display: "flex",
          flexDirection: "row",
          alignItems: "center"
        })]
        #[
          Html.element "span"
            #[("style", json% {
              color: "white",
              fontSize: "20px",
              marginRight: "5px",
              lineHeight: "46px"
            })]
            #[.text "+"],
          numberRow (pad b)
        ],
      Html.element "hr"
        #[("style", json% {
          border: "1px solid white",
          margin: "5px 0"
        })]
        #[],
      -- Result
      numberRow (pad result)
    ]

-- Test 1: Single carry in middle column
-- 123 + 091 = 214
#html additionDisplay
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [⟨1, by omega⟩, ⟨9, by omega⟩, ⟨0, by omega⟩]

-- Test 2: Cascading carries
-- 999 + 001 = 1000
#html additionDisplay
  [⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩]
  [⟨1, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩]

-- Test 3: No carries
-- 123 + 234 = 357
#html additionDisplay
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩]

-- Test 4: Carry only from units cascading
-- 195 + 005 = 200
#html additionDisplay
  [⟨5, by omega⟩, ⟨9, by omega⟩, ⟨1, by omega⟩]
  [⟨5, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩]

-- Test 5: Different length numbers
-- 99 + 1 = 100
#html additionDisplay
  [⟨9, by omega⟩, ⟨9, by omega⟩]
  [⟨1, by omega⟩]


-- Get carry value going into column k
def getCarryAt (a b : MultiDigit) (k : Nat) : Bool :=
  let carries := computeCarries a b
  carries.getD k false

-- carry into column 0 = false (no initial carry)
#eval getCarryAt (fromNat 123) (fromNat 91) 0  -- expect false

-- carry into column 1 = false (3+1=4, no carry)
#eval getCarryAt (fromNat 123) (fromNat 91) 1  -- expect false

-- carry into column 2 = true (2+9=11, carry out)
#eval getCarryAt (fromNat 123) (fromNat 91) 2  -- expect true

-- Invariant panel showing the key relationship at each step
-- Invariant: a[0..k-1] + b[0..k-1] = result[0..k-1] + carry × 10^k
def invariantPanel (a b : MultiDigit) (step : Nat) : Html :=
  let result := verticalAdd a b false
  let maxLen := max (max a.length b.length) result.length
  let pad (x : MultiDigit) : MultiDigit :=
    List.append x (List.replicate (maxLen - x.length) ⟨0, by omega⟩)
  let paddedA := pad a
  let paddedB := pad b
  let paddedResult := pad result
  -- components of the invariant at this step
  let k := step + 1
  let prefixA := toNatPrefix paddedA k
  let prefixB := toNatPrefix paddedB k
  let prefixResult := toNatPrefix paddedResult k
  let carry := getCarryAt a b (step + 1)
  let carryNum := if carry then 1 else 0
  let placeValue := Nat.pow 10 k
  -- left side: sum of input prefixes
  let lhs := prefixA + prefixB
  -- right side: result prefix + carry shifted to next place value
  let rhs := prefixResult + carryNum * placeValue
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
      -- Title
      Html.element "div"
        #[("style", json% {
          color: "cyan",
          marginBottom: "8px",
          fontSize: "14px"
        })]
        #[Html.text s!"Invariant after step {step}:"],
      -- The invariant equation in general form
      Html.element "div"
        #[("style", json% { marginBottom: "5px" })]
        #[Html.text s!"a[0..{k-1}] + b[0..{k-1}] = result[0..{k-1}] + carry × 10^{k}"],
      -- Left side with concrete values
      Html.element "div"
        #[("style", json% { color: "yellow", marginBottom: "3px" })]
        #[Html.text s!"{prefixA} + {prefixB} = {lhs}"],
      -- Right side with concrete values
      Html.element "div"
        #[("style", json% { color: "yellow", marginBottom: "8px" })]
        #[Html.text s!"{prefixResult} + {carryNum} × {placeValue} = {rhs}"],
      -- Verification check -- two separate elements to avoid dynamic json%
      if holds then
        Html.element "div"
          #[("style", json% {
            color: "green",
            fontSize: "14px"
          })]
          #[Html.text "✓ Invariant holds"]
      else
        Html.element "div"
          #[("style", json% {
            color: "red",
            fontSize: "14px"
          })]
          #[Html.text "✗ Invariant violated"]
    ]

-- Full step by step addition display with invariant panel
def additionStepDisplay (a b : MultiDigit) (step : Nat) : Html :=
  let result := verticalAdd a b false
  let carries := computeCarries a b
  let maxLen := max (max a.length b.length) result.length
  let pad (x : MultiDigit) : MultiDigit :=
    List.append x (List.replicate (maxLen - x.length) ⟨0, by omega⟩)

  let paddedA := pad a
  let paddedB := pad b
  let paddedResult := pad result

  -- Helper to maintain left-column alignment
  let opBox (op : String) : Html :=
    Html.element "div"
      #[("style", json% {
        width: "30px", -- Fixed width ensures identical offset for all rows
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        color: "white",
        fontSize: "20px",
        fontWeight: "bold"
      })]
      #[Html.text op]

  Html.element "div"
    #[("style", json% {
      display: "inline-block",
      padding: "15px",
      backgroundColor: "black",
      color: "white",
      fontFamily: "monospace"
    })]
    #[
      -- carry row
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center"
        })]
        -- Add opBox "" here if you want the carry row aligned perfectly with digits too
        #[opBox "", carryRow (carries.mapIdx (fun i c => c && i ≤ step))],

      -- first number centered (with invisible spacer)
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center"
        })]
        #[opBox "", numberRowStepped paddedA step],

      -- + sign next to second number
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center"
        })]
        #[opBox "+", numberRowStepped paddedB step],

      Html.element "hr"
        #[("style", json% {
          border: "1px solid white",
          margin: "5px 0",
          width: "100%"
        })]
        #[],

      -- result row centered (with invisible spacer)
      Html.element "div"
        #[("style", json% {
          display: "flex",
          justifyContent: "center"
        })]
        #[opBox "", resultRowStepped paddedResult step],

      -- invariant panel
      invariantPanel a b step
    ]

#html additionStepDisplay (fromNat 123) (fromNat 91) 0
#html additionStepDisplay (fromNat 123) (fromNat 91) 1
#html additionStepDisplay (fromNat 123) (fromNat 91) 2
