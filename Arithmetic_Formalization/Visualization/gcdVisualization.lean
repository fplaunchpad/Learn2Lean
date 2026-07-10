import ProofWidgets
import Arithmetic_Formalization.Visualization.basicsWidget
import Arithmetic_Formalization.EuclidGCDAlgo
open ProofWidgets
open scoped ProofWidgets.Jsx
open Lean Widget

/-
  ## Euclid's subtractive GCD as rectangle tiling

  An a × b rectangle is paved exactly by squares of side gcd(a, b), and by no
  larger square. Subtractive Euclid (`gcdSub`) carries this out geometrically:
  it repeatedly removes the largest square that fits along the shorter edge —
  i.e. subtracts the shorter side from the longer — until the leftover region
  is itself a square, whose side is the gcd.

  The visualisation keeps ONE fixed rectangle with a faint unit grid, and
  carves squares out of it in place:
    • cyan   — squares already removed in earlier steps
    • orange — the square being removed in the current step
    • faint  — the rectangle still left to process
  The final step re-tiles the whole rectangle with gcd × gcd squares.
-/

-- Trace of the (width, height) of the leftover rectangle at each step.
def gcdTrace : Nat → Nat → Nat → List (Nat × Nat)
  | 0,     a, b => [(a, b)]
  | f + 1, a, b =>
      if a == 0 || b == 0 || a == b then [(a, b)]
      else if b < a then (a, b) :: gcdTrace f (a - b) b
      else                (a, b) :: gcdTrace f a (b - a)

-- The squares carved out, as (x, y, side) in the original rectangle's grid.
def gcdSquares : Nat → Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | 0,     x, y, _, _ => [(x, y, 0)]
  | f + 1, x, y, w, h =>
      if w == 0 || h == 0 then []
      else if w == h then [(x, y, w)]                          -- final gcd square
      else if h < w then (x, y, h) :: gcdSquares f (x + h) y (w - h) h   -- remove from left
      else                (x, y, w) :: gcdSquares f x (y + w) w (h - w)   -- remove from top

-- An absolutely-positioned square inside the board (sizes/positions in pixels).
def posSquare (x y side scale : Nat) (bg border label : String) : Html :=
  Html.element "div"
    #[("style", json% {
        position: "absolute",
        left: $(s!"{x * scale}px"), top: $(s!"{y * scale}px"),
        width: $(s!"{side * scale}px"), height: $(s!"{side * scale}px"),
        backgroundColor: $(bg), border: $(s!"1px solid {border}"), boxSizing: "border-box",
        display: "flex", alignItems: "flex-end", justifyContent: "center", paddingBottom: "3px",
        color: "#ffd9a8", fontFamily: "monospace", fontSize: "11px"
      })]
    #[Html.text label]

-- The board: a fixed W × H rectangle with a faint unit grid, holding `children`.
def board (w h scale : Nat) (showGrid : Bool) (children : Array Html) : Html :=
  let bgImg := if showGrid then
      "linear-gradient(to right, rgba(255,255,255,0.08) 1px, transparent 1px), linear-gradient(to bottom, rgba(255,255,255,0.08) 1px, transparent 1px)"
    else "none"
  Html.element "div"
    #[("style", json% {
        position: "relative",
        width: $(s!"{w * scale}px"), height: $(s!"{h * scale}px"),
        backgroundColor: "#0a0a0a",
        backgroundImage: $(bgImg),
        backgroundSize: $(s!"{scale}px {scale}px")
      })]
    children

def gcdCalcLine (idx step ca cb : Nat) : Html :=
  let isActive := idx == step
  let isPast := idx < step
  let color := if isActive then "yellow" else (if isPast then "#00aaff" else "#555555")
  let bg := if isActive then "#2a2a00" else "transparent"
  let txt :=
    if ca == cb then s!"gcd({ca}, {cb}) = {ca}"
    else if cb < ca then s!"gcd({ca}, {cb}) = gcd({ca - cb}, {cb})"
    else                 s!"gcd({ca}, {cb}) = gcd({ca}, {cb - ca})"
  Html.element "div"
    #[("style", json% { padding: "4px 10px", color: $(color), backgroundColor: $(bg),
        fontFamily: "monospace", margin: "3px 0", borderRadius: "6px", width: "max-content", fontSize: "13px" })]
    #[Html.text txt]

-- step 0 .. N-1 = the subtractive carving; step N = the final gcd tiling.
def gcdVisualizer (a b : MultiDigit) (step : Nat) : Html :=
  let a0 := toNat a
  let b0 := toNat b
  let trace := gcdTrace (a0 + b0) a0 b0
  let squares := gcdSquares (a0 + b0) 0 0 a0 b0
  let n := squares.length                       -- number of carving steps
  let g := toNat (gcdSub a b)                    -- the gcd, from the proven algorithm
  let scale := Nat.max 1 (320 / Nat.max a0 b0)   -- pixels per unit (fixed across steps)
  let final := step ≥ n + 1                      -- after the intro + n carving steps

  -- the board contents
  let children : Array Html :=
    if step == 0 then
      -- intro: the bare rectangle (grid only), nothing carved yet
      #[]
    else if final then
      -- whole rectangle tiled by gcd × gcd squares
      let cols := a0 / g
      let rows := b0 / g
      let oneRow := Html.element "div" #[("style", json% { display: "flex", flexDirection: "row" })]
        ((List.replicate cols
          (Html.element "div" #[("style", json% {
              width: $(s!"{g * scale}px"), height: $(s!"{g * scale}px"),
              backgroundColor: "rgba(76,175,80,0.22)", border: "1px solid #4caf50", boxSizing: "border-box"
            })] #[])).toArray)
      (List.replicate rows oneRow).toArray
    else
      -- carving step k = step - 1: squares coloured by relation to k
      let k := step - 1
      (squares.mapIdx (fun j sq =>
        let (x, y, side) := sq
        if j < k then posSquare x y side scale "rgba(46,100,112,0.92)" "#3a7e8e" ""
        else if j == k then posSquare x y side scale "rgba(176,98,0,0.92)" "#ff8c00" s!"side {side}"
        else posSquare x y side scale "rgba(150,150,150,0.05)" "#333333" "")).toArray
  let opText :=
    if step == 0 then s!"An {a0} × {b0} rectangle. What is the largest square that tiles it exactly?"
    else if final then s!"The {g}×{g} square tiles the whole rectangle exactly — {a0 / g} across × {b0 / g} down."
    else
      let cur := trace.getD (step - 1) (a0, b0)
      let ca := cur.1; let cb := cur.2
      if ca == cb then s!"Leftover is a square of side {ca} — that side is the gcd."
      else if cb < ca then s!"Remove the largest square that fits: {cb}×{cb} (orange)."
      else s!"Remove the largest square that fits: {ca}×{ca} (orange)."
  let calcLogs := ((List.range n).map (fun j =>
      if j + 1 ≤ step then
        let st := trace.getD j (0, 0)
        gcdCalcLine j (step - 1) st.1 st.2
      else Html.element "span" #[] #[])).toArray
  Html.element "div" #[("style", json% { display: "flex", flexDirection: "row", padding: "20px", backgroundColor: "#0d0d0d", alignItems: "flex-start" })] #[
    Html.element "div" #[("style", json% { display: "flex", flexDirection: "column" })] #[
      Html.element "div" #[("style", json% { color: "#ff8c00", fontFamily: "monospace", fontSize: "16px", marginBottom: "10px" })]
        #[Html.text s!"Euclid's subtractive GCD — rectangle tiling   ({a0} × {b0})"],
      board a0 b0 scale (decide (step ≤ n)) children,
      Html.element "div" #[("style", json% { color: "#aaa", fontFamily: "monospace", fontSize: "13px", marginTop: "12px", maxWidth: "340px" })]
        #[Html.text opText]
    ],
    Html.element "div" #[("style", json% {
        marginLeft: "24px", padding: "15px", border: "1px solid gray", color: "white",
        backgroundColor: "#161616", borderRadius: "6px", minWidth: "300px", height: "max-content" })]
      #[
        Html.element "div" #[("style", json% { color: "cyan", fontWeight: "bold", marginBottom: "10px", fontFamily: "monospace" })]
          #[Html.text s!"Step {step + 1} of {n + 2}"],
        Html.element "div" #[("style", json% { color: "#aaa", marginBottom: "8px", fontFamily: "monospace", fontSize: "13px" })]
          #[Html.text "Subtracting the smaller side preserves the gcd:"],
        Html.element "div" #[("style", json% { display: "flex", flexDirection: "column", marginBottom: "12px" })] calcLogs,
        if final then
          Html.element "div" #[("style", json% { color: "#4caf50", fontWeight: "bold", fontFamily: "monospace" })]
            #[Html.text s!"✓ gcd = {g} tiles the whole {a0}×{b0} rectangle"]
        else if step == n then
          Html.element "div" #[("style", json% { color: "#4caf50", fontWeight: "bold", fontFamily: "monospace" })]
            #[Html.text s!"Leftover is a square — gcd discovered = {g}"]
        else
          Html.element "div" #[("style", json% { color: "#888888", fontWeight: "bold", fontFamily: "monospace" })]
            #[Html.text "gcd = ?   (keep removing the largest square)"]
      ]
  ]

-- gcd(48, 36) = 12   step 0 = problem; steps 1-4 = carving; step 5 = final tiling
#html gcdVisualizer [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩] 0   -- the rectangle
#html gcdVisualizer [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩] 1
#html gcdVisualizer [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩] 2
#html gcdVisualizer [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩] 3
#html gcdVisualizer [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩] 4
#html gcdVisualizer [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩] 5   -- final tiling

-- gcd(12, 8) = 4   step 0 = problem; steps 1-3 = carving; step 4 = final tiling
#html gcdVisualizer [⟨2,by omega⟩,⟨1,by omega⟩] [⟨8,by omega⟩] 0
#html gcdVisualizer [⟨2,by omega⟩,⟨1,by omega⟩] [⟨8,by omega⟩] 1
#html gcdVisualizer [⟨2,by omega⟩,⟨1,by omega⟩] [⟨8,by omega⟩] 2
#html gcdVisualizer [⟨2,by omega⟩,⟨1,by omega⟩] [⟨8,by omega⟩] 3
#html gcdVisualizer [⟨2,by omega⟩,⟨1,by omega⟩] [⟨8,by omega⟩] 4   -- final tiling
