-- Foundations uses only core Lean tactics (omega, simp, rfl, cases),
-- so it needs no Mathlib import. Downstream files import the specific
-- Mathlib tactic modules they actually use.
--Core Represenation
abbrev Digit := Fin 10
--Ensures digits less than 10(i.e valid)
def MultiDigit := List Digit
-- Number represented LSD to MSD (will be justified subsequently)

--Represenation to Value
def toNat : MultiDigit → Nat
  | [] => 0
  | d :: ds => d.val + 10 * toNat ds
--Choice of LSB to MSB represenation makes for clean recursion

--Quick Check
#eval toNat [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
--Fin Requires proof that num is less than 10

/-
  A note on the `omega` tactic:

  `omega` is a decision procedure for linear arithmetic over natural numbers
  and integers. It automatically proves goals involving addition, subtraction,
  multiplication by constants, and inequalities — without requiring manual proof
  steps. For example:

    example (n : Nat) (h : n ≥ 10) : n - 10 < n := by omega
    example (a b : Nat) (h1 : a < 10) (h2 : b < 10) : a + b < 20 := by omega

  We shall use `omega` extensively to discharge arithmetic side
  conditions — bounds checks, carry conditions, and digit validity proofs —
  so we can focus on the mathematical structure of the algorithms rather than
  routine arithmetic reasoning.
-/
--Trivial Lemmas(Useful for proofs later)
@[simp] theorem toNat_nil : toNat [] = 0 := rfl
--True by base case
@[simp] theorem toNat_cons (d : Digit) (ds : MultiDigit) :
    toNat (d :: ds) = d.val + 10 * toNat ds := rfl
--True by recursive structure

--Helper Definition
def carryVal : Bool → Nat
  | true  => 1
  | false => 0
--Some theorems to help in simplification
@[simp] theorem carryVal_true : carryVal true = 1 := rfl
@[simp] theorem carryVal_false : carryVal false = 0 := rfl
@[simp] theorem carryVal_bound (c : Bool) : carryVal c ≤ 1 := by
  cases c <;> simp [carryVal]

def toNatPrefix (a : MultiDigit) (n : Nat) : Nat :=
  toNat (a.take n)
