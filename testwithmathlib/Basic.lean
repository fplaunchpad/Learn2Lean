import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
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
theorem toNat_nil : toNat [] = 0 := rfl
--True by base case
theorem toNat_cons (d : Digit) (ds : MultiDigit) :
    toNat (d :: ds) = d.val + 10 * toNat ds := rfl
--True by recursive structure

--Addition
--We want a function that we can chain together to implement our larger
--addition algorithm. Hence we need an input carry as well as an output
--carry alongside the two digits to be added
def addDigits (a b : Digit) (carry : Bool) : Digit × Bool :=
  let sum := a.val + b.val + if carry then 1 else 0
  --Proving an upperbound for
  have hsum : sum ≤ 19 := by
    have ha := a.isLt  -- a.val < 10
    have hb := b.isLt  -- b.val < 10
    simp [sum]
    split_ifs <;> omega
  -- split_ifs allows omega to reason about the two branches
  --(i.e with input carry and without) seperately
  if h : sum < 10
  --h serves as a proof that sum<10(if evaluated to true) and can be used subsequently
  then (⟨sum, h⟩, false)
  else (⟨sum - 10, by omega⟩, true)

--A few Testcases
#eval addDigits ⟨7, by omega⟩ ⟨8, by omega⟩ false  -- 7+8=15, expect (5, true)
#eval addDigits ⟨3, by omega⟩ ⟨4, by omega⟩ false  -- 3+4=7, expect (7, false)
#eval addDigits ⟨9, by omega⟩ ⟨9, by omega⟩ true   -- 9+9+1=19, expect (9, true)

--Correctness Proof
--
theorem addDigits_correct (a b : Digit) (carry : Bool) :
    (addDigits a b carry).1.val +
    10 * (if (addDigits a b carry).2 then 1 else 0) =
    a.val + b.val + if carry then 1 else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold addDigits
  --unfold replaces (addDigits a b carry) in the goal with its definition body
  simp only []
  split_ifs with h <;>
  --splits proof into case with carry and case without carry
  simp_all <;> omega

--Now that we have a verified method to add two digits along with a carry
--it is just needed to extend it to column wise addition
--mimicing the way we do it with pen and paper
def verticalAdd : MultiDigit → MultiDigit → Bool → MultiDigit
  | [], [], false => []
  | [], [], true  => [⟨1, by omega⟩]
  | [], b :: bs, c =>
      let (d, c') := addDigits ⟨0, by omega⟩ b c
      d :: verticalAdd [] bs c'
  | a :: as, [], c =>
      let (d, c') := addDigits a ⟨0, by omega⟩ c
      d :: verticalAdd as [] c'
  | a :: as, b :: bs, c =>
      let (d, c') := addDigits a b c
      d :: verticalAdd as bs c'
termination_by a b _ => a.length + b.length
--have to explicity justify termination as recursion is a bit complicated here

--Test cases
#eval toNat (verticalAdd
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]   -- 123
  [⟨1, by omega⟩, ⟨9, by omega⟩, ⟨8, by omega⟩]    -- 891
  false)
  --expect 1014
#eval toNat (verticalAdd
  [ ⟨2, by omega⟩, ⟨1, by omega⟩]   -- 12
  [⟨5, by omega⟩, ⟨6, by omega⟩, ⟨2, by omega⟩]    -- 265
  false)
  --expect 277
#eval toNat (verticalAdd
  [⟨9, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]   -- 109
  [⟨1, by omega⟩, ⟨9, by omega⟩, ⟨8, by omega⟩]    -- 891
  false)
  --expect 1000

theorem verticalAdd_correct (a b : MultiDigit) (carry : Bool) :
    toNat (verticalAdd a b carry) =
    toNat a + toNat b + if carry then 1 else 0 := by
    sorry
  --Will work on this requires bit more reading up
