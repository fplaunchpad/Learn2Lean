import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.Divisibility
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

-- A digit box with configurable border / text colour (same look as the others).
def divisDigitBox (d : String) (borderColor : String) (textColor : String) : Html :=
  let borderValue := s!"2px solid {borderColor}"
  Html.element "div"
    #[("style", json% {
      display: "inline-block", border: $(borderValue), width: "40px", height: "40px",
      textAlign: "center", lineHeight: "40px", fontSize: "20px", color: $(textColor),
      margin: "3px", backgroundColor: "transparent", borderRadius: "4px"
    })]
    #[Html.text d]

/-
  ## Divisibility by 3 and 9

  We visualise the invariant behind `toNat_mod3_eq_digitSum_mod3` /
  `toNat_mod9_eq_digitSum_mod9`: for every suffix of the number (its rightmost
  digits, stepping in from the units), the value of that suffix and its digit
  sum leave the same remainder mod 3 (resp. 9). The equation never breaks —
  that is exactly the inductive proof, made visible.
-/

-- For each suffix length j+1 (the rightmost j+1 digits = `a.take (j+1)` since
-- the list is LSB-first), record (value, digitSum).
def digitSumStates (a : MultiDigit) : List (Nat × Nat) :=
  (List.range a.length).map (fun j =>
    let s := a.take (j + 1)
    (toNat s, digitSum s))

def digitSumCalcLine (idx step m val dsum : Nat) : Html :=
  let isActive := idx == step
  let isPast := idx < step
  let color := if isActive then "yellow" else (if isPast then "#00aaff" else "#555555")
  let bg := if isActive then "#2a2a00" else "transparent"
  Html.element "div"
    #[("style", json% {
      padding: "5px 10px", color: $(color), backgroundColor: $(bg),
      fontFamily: "monospace", margin: "4px 0", borderRadius: "6px",
      width: "max-content", fontSize: "14px"
    })]
    #[Html.text s!"{idx + 1}-digit suffix:  value {val} % {m} = {val % m}   ·   digitSum {dsum} % {m} = {dsum % m}"]

def digitSumInvariantPanel (step m val dsum : Nat) : Html :=
  let lhs := val % m
  let rhs := dsum % m
  let holds := lhs == rhs
  let verdict : Html :=
    if holds then
      Html.element "div" #[("style", json% { color: "#4caf50", fontWeight: "bold" })]
        #[Html.text s!"✓ congruent (mod {m})"]
    else
      Html.element "div" #[("style", json% { color: "#f44336", fontWeight: "bold" })]
        #[Html.text "✗ not congruent"]
  Html.element "div"
    #[("style", json% {
      marginLeft: "20px", padding: "15px", border: "1px solid gray", color: "white",
      fontSize: "14px", fontFamily: "monospace", backgroundColor: "#161616",
      borderRadius: "6px", minWidth: "320px", height: "max-content"
    })]
    #[
      Html.element "div" #[("style", json% { color: "cyan", marginBottom: "12px", fontWeight: "bold" })]
        #[Html.text s!"Invariant after {step + 1}-digit suffix:"],
      Html.element "div" #[("style", json% { marginBottom: "8px", color: "#aaa" })]
        #[Html.text s!"value % {m} = digitSum % {m}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "8px" })]
        #[Html.text s!"{val} % {m} = {lhs}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "12px" })]
        #[Html.text s!"{dsum} % {m} = {rhs}"],
      verdict
    ]

-- m is the modulus (use 3 or 9). step indexes the suffix (0 = just the units digit).
def digitSumDivisVisualizer (a : MultiDigit) (m : Nat) (step : Nat) : Html :=
  let digitsMSB := a.reverse.map (fun d => d.val)
  let maxIdx := a.length - 1
  let states := digitSumStates a
  let cur := states.getD step (0, 0)
  let boxes := (digitsMSB.mapIdx (fun i d =>
      let listIdx := maxIdx - i          -- LSB-first index of this displayed digit
      if listIdx ≤ step then divisDigitBox s!"{d}" "yellow" "yellow"
      else divisDigitBox s!"{d}" "#444" "#444")).toArray
  let calcLogs := ((List.range a.length).map (fun j =>
      if j ≤ step then
        let st := states.getD j (0, 0)
        digitSumCalcLine j step m st.1 st.2
      else Html.element "span" #[] #[])).toArray
  Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", padding: "20px", backgroundColor: "#0d0d0d" })] #[
    Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] #[
      Html.element "div" #[("style", json% { color: "#ff8c00", fontFamily: "monospace", fontSize: "16px", marginBottom: "8px" })]
        #[Html.text s!"Divisibility by {m} — digit-sum rule"],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", marginBottom: "12px" })] boxes,
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] calcLogs
    ],
    digitSumInvariantPanel step m cur.1 cur.2
  ]

/-
  ## Divisibility by 11

  The analogue of the digit-sum rule. For each suffix we split its digits by
  position parity (counting from the units digit) into the even-position sum E
  and the odd-position sum O. The invariant from `toNat_mod11_eq_altSum` is that
  the suffix value plus O is congruent to E mod 11 — equivalently,
  value ≡ E − O (mod 11). Even-position digits are green, odd-position orange.
-/

-- For each suffix length j+1, record (value, E, O) where (E, O) = altSums.
def altSumStates (a : MultiDigit) : List (Nat × Nat × Nat) :=
  (List.range a.length).map (fun j =>
    let s := a.take (j + 1)
    let p := altSums s
    (toNat s, p.1, p.2))

def altSumCalcLine (idx step val e o : Nat) : Html :=
  let isActive := idx == step
  let isPast := idx < step
  let color := if isActive then "yellow" else (if isPast then "#00aaff" else "#555555")
  let bg := if isActive then "#2a2a00" else "transparent"
  Html.element "div"
    #[("style", json% {
      padding: "5px 10px", color: $(color), backgroundColor: $(bg),
      fontFamily: "monospace", margin: "4px 0", borderRadius: "6px",
      width: "max-content", fontSize: "14px"
    })]
    #[Html.text s!"{idx + 1}-digit suffix:  ({val} + {o}) % 11 = {(val + o) % 11}   ·   E {e} % 11 = {e % 11}"]

def altSumInvariantPanel (step val e o : Nat) : Html :=
  let lhs := (val + o) % 11
  let rhs := e % 11
  let holds := lhs == rhs
  let verdict : Html :=
    if holds then
      Html.element "div" #[("style", json% { color: "#4caf50", fontWeight: "bold" })]
        #[Html.text "✓ congruent (mod 11)"]
    else
      Html.element "div" #[("style", json% { color: "#f44336", fontWeight: "bold" })]
        #[Html.text "✗ not congruent"]
  Html.element "div"
    #[("style", json% {
      marginLeft: "20px", padding: "15px", border: "1px solid gray", color: "white",
      fontSize: "14px", fontFamily: "monospace", backgroundColor: "#161616",
      borderRadius: "6px", minWidth: "340px", height: "max-content"
    })]
    #[
      Html.element "div" #[("style", json% { color: "cyan", marginBottom: "12px", fontWeight: "bold" })]
        #[Html.text s!"Invariant after {step + 1}-digit suffix:"],
      Html.element "div" #[("style", json% { marginBottom: "8px", color: "#aaa" })]
        #[Html.text "(value + O) % 11 = E % 11"],
      Html.element "div" #[("style", json% { color: "#4caf50", marginBottom: "4px" })]
        #[Html.text s!"E (even positions) = {e}"],
      Html.element "div" #[("style", json% { color: "#ff8c00", marginBottom: "8px" })]
        #[Html.text s!"O (odd positions)  = {o}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "4px" })]
        #[Html.text s!"({val} + {o}) % 11 = {lhs}"],
      Html.element "div" #[("style", json% { color: "yellow", marginBottom: "8px" })]
        #[Html.text s!"{e} % 11 = {rhs}        (value % 11 = {val % 11})"],
      verdict
    ]

-- step indexes the suffix (0 = just the units digit).
def altSumDivisVisualizer (a : MultiDigit) (step : Nat) : Html :=
  let digitsMSB := a.reverse.map (fun d => d.val)
  let maxIdx := a.length - 1
  let states := altSumStates a
  let cur := states.getD step (0, 0, 0)
  let boxes := (digitsMSB.mapIdx (fun i d =>
      let listIdx := maxIdx - i
      if listIdx ≤ step then
        if listIdx % 2 == 0 then divisDigitBox s!"{d}" "#4caf50" "#4caf50"   -- even position → E
        else divisDigitBox s!"{d}" "#ff8c00" "#ff8c00"                       -- odd position → O
      else divisDigitBox s!"{d}" "#444" "#444")).toArray
  let calcLogs := ((List.range a.length).map (fun j =>
      if j ≤ step then
        let st := states.getD j (0, 0, 0)
        altSumCalcLine j step st.1 st.2.1 st.2.2
      else Html.element "span" #[] #[])).toArray
  Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", padding: "20px", backgroundColor: "#0d0d0d" })] #[
    Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] #[
      Html.element "div" #[("style", json% { color: "#ff8c00", fontFamily: "monospace", fontSize: "16px", marginBottom: "8px" })]
        #[Html.text "Divisibility by 11 — alternating (even − odd) rule"],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", marginBottom: "6px" })] boxes,
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", fontFamily: "monospace", fontSize: "12px", marginBottom: "12px" })] #[
        Html.element "span" #[("style", json% { color: "#4caf50", marginRight: "16px" })] #[Html.text "■ even position (E)"],
        Html.element "span" #[("style", json% { color: "#ff8c00" })] #[Html.text "■ odd position (O)"]
      ],
      Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] calcLogs
    ],
    altSumInvariantPanel step cur.1 cur.2.1 cur.2.2
  ]

-- 1234, divisibility by 3 (digit sum 10, both ≡ 1 mod 3)
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 3 0
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 3 1
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 3 2
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 3 3

-- 1234, divisibility by 9

#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 9 0
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 9 1
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 9 2
#html digitSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 9 3

-- 1234, divisibility by 11 (E = 4+2 = 6, O = 3+1 = 4, value % 11 = 2 = 6 − 4)
#html altSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 0
#html altSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 1
#html altSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 2
#html altSumDivisVisualizer [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩] 3
