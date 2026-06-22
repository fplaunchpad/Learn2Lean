# Formal Verification of Elementary Arithmetic in Lean 4

A summer internship project at **FP Launchpad, IIT Madras** under **Prof. KC Sivaramakrishnan**.

## What is this?
This project formalises elementary pen-and-paper arithmetic algorithms in Lean 4 and proves their correctness using machine-checked theorem proving.

The goal is to bridge traditional arithmetic algorithms, formal verification, and interactive visualisation by developing verified implementations of the methods commonly taught in school mathematics.

## Features
- Machine-checked correctness proofs in Lean 4
- Interactive arithmetic visualisations using [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4)
- Step-by-step execution of grade-school arithmetic algorithms along with invariant reasoning

## Current Status
- **Vertical Addition** — proved correct
- **Vertical Subtraction** — proved correct
- **Long Multiplication** — proved correct
- **Long Division** — proved correct
- **Integer Square Root** — proved correct 
- **Divisibility Tests** — proved correct

## Visualisations
Each algorithm ships with an interactive widget that renders its execution step by step in the Lean infoview, complete with the loop invariant maintained at each stage.

**Vertical addition** — column carries, with the invariant `a[0..k] + b[0..k] = result[0..k] + carry·10ᵏ`:

![Vertical addition visualisation](assets/addition_visualization.png)

**Long multiplication** — partial products summed, with the invariant `Sum(partial products) = a × b[0..k]`:

![Long multiplication visualisation](assets/multiplication_visualization.png)

**Long division** — bring-down steps, with the invariant `prefix = quotient × divisor + remainder`:

![Long division visualisation](assets/division_visualization.png)

**Integer square root** — the digit-by-digit radical method, with the invariant `pairs = root² + remainder`:

![Square root visualisation](assets/squareroot_visualization.png)

## Getting Started

### Prerequisites
* [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) via the `elan` version manager. The exact toolchain (pinned in `lean-toolchain`) installs automatically.

### Build
This project depends on [Mathlib](https://github.com/leanprover-community/mathlib4). **Run `lake exe cache get` before building** — otherwise Lake compiles all of Mathlib from source, which takes 1–2+ hours and is unreliable on Windows.

```bash
git clone https://github.com/UnOrdinary19/Lean_formalization.git
cd Lean_formalization
lake exe cache get   # download prebuilt Mathlib oleans
lake build
```

### Viewing the visualisations
Open any file under `Arithmetic_Formalization/Visualization/` in **VS Code** with the **Lean 4 extension** installed. Place your cursor on a `#html …` command and the rendered widget appears in the Lean infoview. Each file ends with several `#html` calls that step through an example (`step 0`, `step 1`, …).

## Project layout
```text
Arithmetic_Formalization/
├── Foundations.lean        -- digit/number representation (LSB-first) + toNat
├── Addition.lean           -- vertical addition + correctness
├── Subtraction.lean        -- vertical subtraction + correctness
├── Multiplication.lean     -- long multiplication (partial products) + correctness
├── Division.lean           -- long division (single & multi-digit divisor) + correctness
├── Squareroot.lean         -- integer square root (returns ⌊√n⌋) + correctness
└── Visualization/          -- ProofWidgets visualisations for each algorithm
```

Each core file imports only the specific Mathlib tactics it uses (`FinCases`, `Ring`, `SplitIfs`, `Linarith`) rather than the full `Mathlib.Tactic`, keeping the build's dependency closure small.

## Acknowledgements
Developed as a summer internship project at **FP Launchpad, IIT Madras**, under the guidance of **Prof. KC Sivaramakrishnan**.
