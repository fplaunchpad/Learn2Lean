# Formal Verification of Elementary Arithmetic in Lean 4

A summer internship project at **FP Launchpad, IIT Madras** under **Prof. KC Sivaramakrishnan**.

## What is this?

This project formalises elementary pen-and-paper arithmetic algorithms in Lean 4 and proves their correctness using machine-checked theorem proving.

The goal is to bridge traditional arithmetic algorithms, formal verification, and interactive visualisation by developing verified implementations of the methods commonly taught in school mathematics.

## Features

- Machine-checked correctness proofs in Lean 4
- Interactive arithmetic visualisations using [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4)
- Step-by-step execution of grade-school arithmetic algorithms alongside invariant reasoning

## Visualisations

Each algorithm ships with an interactive widget that renders its execution step by step in the Lean infoview, complete with the loop invariant being maintained at each stage. A few highlights:

**Vertical addition** — column carries, with the invariant `a[0..k] + b[0..k] = result[0..k] + carry·10ᵏ`:

![Vertical addition visualisation](assets/addition_visualization.png)

**Long multiplication** — partial products summed, with the invariant `Sum(partial products) = a × b[0..k]`:

![Long multiplication visualisation](assets/multiplication_visualization.png)

**Long division** — bring-down steps, with the invariant `prefix = quotient × divisor + remainder`:

![Long division visualisation](assets/division_visualization.png)

**Integer square root** — the digit-by-digit radical method, with the invariant `pairs = root² + remainder`:

![Square root visualisation](assets/squareroot_visualization.png)

> These are screenshots of the live widgets in the Lean infoview — see [Viewing the visualisations](#viewing-the-visualisations) to step through them interactively.

## Current Status

| Algorithm | Correctness proof | Visualisation |
|---|---|---|
| Vertical Addition | ✅ proved | ✅ |
| Vertical Subtraction | ✅ proved | ✅ |
| Long Multiplication | ✅ proved | ✅ |
| Long Division (single- and multi-digit divisor) | ✅ proved | ✅ |
| Integer Square Root | ✅ proved — returns ⌊√n⌋ (`q² ≤ n < (q+1)²`) | ✅ |
| Divisibility Tests (digit-sum rules for 3, 9, 11) | 🚧 in progress | — |

## Building

This project depends on [Mathlib](https://github.com/leanprover-community/mathlib4). **Always fetch Mathlib's prebuilt binaries with `lake exe cache get` before building** — otherwise Lake compiles all of Mathlib from source, which takes 1–2+ hours and is unreliable on Windows.

```bash
# 1. Install elan (the Lean version manager) if you don't have it:
#    https://github.com/leanprover/elan
#    The correct Lean toolchain (pinned in `lean-toolchain`) installs automatically.

# 2. Clone the repository
git clone https://github.com/UnOrdinary19/Lean_formalization.git
cd Lean_formalization

# 3. Download prebuilt Mathlib oleans — minutes instead of hours
lake exe cache get

# 4. Build the project
lake build
```

**First build:** ~15–30 min (Mathlib cache download + ProofWidgets + this project's files). **Every build after that:** seconds.

The dependency revision is pinned in the committed `lake-manifest.json`, which is what lets `lake exe cache get` resolve the exact prebuilt oleans — please keep it tracked.

## Viewing the visualisations

Open any file under [`Arithmetic_Formalization/Visualization/`](Arithmetic_Formalization/Visualization) in **VS Code** with the **Lean 4 extension** installed. Place your cursor on a `#html …` command and the rendered widget appears in the Lean infoview on the right. Each file ends with several `#html` calls that step through an example (`step 0`, `step 1`, …).

## Project layout

```
Arithmetic_Formalization/
├── Foundations.lean        -- digit/number representation (LSB-first) + toNat
├── Addition.lean           -- vertical addition + correctness
├── Subtraction.lean        -- vertical subtraction + correctness
├── Multiplication.lean     -- long multiplication (partial products) + correctness
├── Division.lean           -- long division (single & multi-digit) + correctness
├── Squareroot.lean         -- integer square root (pen-and-paper method)
└── Visualization/          -- ProofWidgets visualisations for each algorithm
```

Each core file imports only the specific Mathlib tactics it uses (`FinCases`, `Ring`, `SplitIfs`) rather than the full `Mathlib.Tactic`, which keeps the build's dependency closure as small as possible.

## Acknowledgements

Developed as a summer internship project at **FP Launchpad, IIT Madras**, under the guidance of **Prof. KC Sivaramakrishnan**.
