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
@[simp] theorem toNat_nil : toNat [] = 0 := rfl
--True by base case
@[simp] theorem toNat_cons (d : Digit) (ds : MultiDigit) :
    toNat (d :: ds) = d.val + 10 * toNat ds := rfl
--True by recursive structure

--Addition
--We want a function that we can chain together to implement our larger
--addition algorithm. Hence we need an input carry as well as an output
--carry alongside the two digits to be added
--Helper Definition
def carryVal : Bool → Nat
  | true  => 1
  | false => 0
--Some theorems to help in simplification
@[simp] theorem carryVal_true : carryVal true = 1 := rfl
@[simp] theorem carryVal_false : carryVal false = 0 := rfl
@[simp] theorem carryVal_bound (c : Bool) : carryVal c ≤ 1 := by
  cases c <;> simp [carryVal]
--We shall first list the possible two digit addditions and their results
def addTable : Digit → Digit → Digit × Bool
  | ⟨0, _⟩, ⟨0, _⟩ => (⟨0, by omega⟩, false)
  | ⟨0, _⟩, ⟨1, _⟩ => (⟨1, by omega⟩, false)
  | ⟨0, _⟩, ⟨2, _⟩ => (⟨2, by omega⟩, false)
  | ⟨0, _⟩, ⟨3, _⟩ => (⟨3, by omega⟩, false)
  | ⟨0, _⟩, ⟨4, _⟩ => (⟨4, by omega⟩, false)
  | ⟨0, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, false)
  | ⟨0, _⟩, ⟨6, _⟩ => (⟨6, by omega⟩, false)
  | ⟨0, _⟩, ⟨7, _⟩ => (⟨7, by omega⟩, false)
  | ⟨0, _⟩, ⟨8, _⟩ => (⟨8, by omega⟩, false)
  | ⟨0, _⟩, ⟨9, _⟩ => (⟨9, by omega⟩, false)
  | ⟨1, _⟩, ⟨0, _⟩ => (⟨1, by omega⟩, false)
  | ⟨1, _⟩, ⟨1, _⟩ => (⟨2, by omega⟩, false)
  | ⟨1, _⟩, ⟨2, _⟩ => (⟨3, by omega⟩, false)
  | ⟨1, _⟩, ⟨3, _⟩ => (⟨4, by omega⟩, false)
  | ⟨1, _⟩, ⟨4, _⟩ => (⟨5, by omega⟩, false)
  | ⟨1, _⟩, ⟨5, _⟩ => (⟨6, by omega⟩, false)
  | ⟨1, _⟩, ⟨6, _⟩ => (⟨7, by omega⟩, false)
  | ⟨1, _⟩, ⟨7, _⟩ => (⟨8, by omega⟩, false)
  | ⟨1, _⟩, ⟨8, _⟩ => (⟨9, by omega⟩, false)
  | ⟨1, _⟩, ⟨9, _⟩ => (⟨0, by omega⟩, true)
  | ⟨2, _⟩, ⟨0, _⟩ => (⟨2, by omega⟩, false)
  | ⟨2, _⟩, ⟨1, _⟩ => (⟨3, by omega⟩, false)
  | ⟨2, _⟩, ⟨2, _⟩ => (⟨4, by omega⟩, false)
  | ⟨2, _⟩, ⟨3, _⟩ => (⟨5, by omega⟩, false)
  | ⟨2, _⟩, ⟨4, _⟩ => (⟨6, by omega⟩, false)
  | ⟨2, _⟩, ⟨5, _⟩ => (⟨7, by omega⟩, false)
  | ⟨2, _⟩, ⟨6, _⟩ => (⟨8, by omega⟩, false)
  | ⟨2, _⟩, ⟨7, _⟩ => (⟨9, by omega⟩, false)
  | ⟨2, _⟩, ⟨8, _⟩ => (⟨0, by omega⟩, true)
  | ⟨2, _⟩, ⟨9, _⟩ => (⟨1, by omega⟩, true)
  | ⟨3, _⟩, ⟨0, _⟩ => (⟨3, by omega⟩, false)
  | ⟨3, _⟩, ⟨1, _⟩ => (⟨4, by omega⟩, false)
  | ⟨3, _⟩, ⟨2, _⟩ => (⟨5, by omega⟩, false)
  | ⟨3, _⟩, ⟨3, _⟩ => (⟨6, by omega⟩, false)
  | ⟨3, _⟩, ⟨4, _⟩ => (⟨7, by omega⟩, false)
  | ⟨3, _⟩, ⟨5, _⟩ => (⟨8, by omega⟩, false)
  | ⟨3, _⟩, ⟨6, _⟩ => (⟨9, by omega⟩, false)
  | ⟨3, _⟩, ⟨7, _⟩ => (⟨0, by omega⟩, true)
  | ⟨3, _⟩, ⟨8, _⟩ => (⟨1, by omega⟩, true)
  | ⟨3, _⟩, ⟨9, _⟩ => (⟨2, by omega⟩, true)
  | ⟨4, _⟩, ⟨0, _⟩ => (⟨4, by omega⟩, false)
  | ⟨4, _⟩, ⟨1, _⟩ => (⟨5, by omega⟩, false)
  | ⟨4, _⟩, ⟨2, _⟩ => (⟨6, by omega⟩, false)
  | ⟨4, _⟩, ⟨3, _⟩ => (⟨7, by omega⟩, false)
  | ⟨4, _⟩, ⟨4, _⟩ => (⟨8, by omega⟩, false)
  | ⟨4, _⟩, ⟨5, _⟩ => (⟨9, by omega⟩, false)
  | ⟨4, _⟩, ⟨6, _⟩ => (⟨0, by omega⟩, true)
  | ⟨4, _⟩, ⟨7, _⟩ => (⟨1, by omega⟩, true)
  | ⟨4, _⟩, ⟨8, _⟩ => (⟨2, by omega⟩, true)
  | ⟨4, _⟩, ⟨9, _⟩ => (⟨3, by omega⟩, true)
  | ⟨5, _⟩, ⟨0, _⟩ => (⟨5, by omega⟩, false)
  | ⟨5, _⟩, ⟨1, _⟩ => (⟨6, by omega⟩, false)
  | ⟨5, _⟩, ⟨2, _⟩ => (⟨7, by omega⟩, false)
  | ⟨5, _⟩, ⟨3, _⟩ => (⟨8, by omega⟩, false)
  | ⟨5, _⟩, ⟨4, _⟩ => (⟨9, by omega⟩, false)
  | ⟨5, _⟩, ⟨5, _⟩ => (⟨0, by omega⟩, true)
  | ⟨5, _⟩, ⟨6, _⟩ => (⟨1, by omega⟩, true)
  | ⟨5, _⟩, ⟨7, _⟩ => (⟨2, by omega⟩, true)
  | ⟨5, _⟩, ⟨8, _⟩ => (⟨3, by omega⟩, true)
  | ⟨5, _⟩, ⟨9, _⟩ => (⟨4, by omega⟩, true)
  | ⟨6, _⟩, ⟨0, _⟩ => (⟨6, by omega⟩, false)
  | ⟨6, _⟩, ⟨1, _⟩ => (⟨7, by omega⟩, false)
  | ⟨6, _⟩, ⟨2, _⟩ => (⟨8, by omega⟩, false)
  | ⟨6, _⟩, ⟨3, _⟩ => (⟨9, by omega⟩, false)
  | ⟨6, _⟩, ⟨4, _⟩ => (⟨0, by omega⟩, true)
  | ⟨6, _⟩, ⟨5, _⟩ => (⟨1, by omega⟩, true)
  | ⟨6, _⟩, ⟨6, _⟩ => (⟨2, by omega⟩, true)
  | ⟨6, _⟩, ⟨7, _⟩ => (⟨3, by omega⟩, true)
  | ⟨6, _⟩, ⟨8, _⟩ => (⟨4, by omega⟩, true)
  | ⟨6, _⟩, ⟨9, _⟩ => (⟨5, by omega⟩, true)
  | ⟨7, _⟩, ⟨0, _⟩ => (⟨7, by omega⟩, false)
  | ⟨7, _⟩, ⟨1, _⟩ => (⟨8, by omega⟩, false)
  | ⟨7, _⟩, ⟨2, _⟩ => (⟨9, by omega⟩, false)
  | ⟨7, _⟩, ⟨3, _⟩ => (⟨0, by omega⟩, true)
  | ⟨7, _⟩, ⟨4, _⟩ => (⟨1, by omega⟩, true)
  | ⟨7, _⟩, ⟨5, _⟩ => (⟨2, by omega⟩, true)
  | ⟨7, _⟩, ⟨6, _⟩ => (⟨3, by omega⟩, true)
  | ⟨7, _⟩, ⟨7, _⟩ => (⟨4, by omega⟩, true)
  | ⟨7, _⟩, ⟨8, _⟩ => (⟨5, by omega⟩, true)
  | ⟨7, _⟩, ⟨9, _⟩ => (⟨6, by omega⟩, true)
  | ⟨8, _⟩, ⟨0, _⟩ => (⟨8, by omega⟩, false)
  | ⟨8, _⟩, ⟨1, _⟩ => (⟨9, by omega⟩, false)
  | ⟨8, _⟩, ⟨2, _⟩ => (⟨0, by omega⟩, true)
  | ⟨8, _⟩, ⟨3, _⟩ => (⟨1, by omega⟩, true)
  | ⟨8, _⟩, ⟨4, _⟩ => (⟨2, by omega⟩, true)
  | ⟨8, _⟩, ⟨5, _⟩ => (⟨3, by omega⟩, true)
  | ⟨8, _⟩, ⟨6, _⟩ => (⟨4, by omega⟩, true)
  | ⟨8, _⟩, ⟨7, _⟩ => (⟨5, by omega⟩, true)
  | ⟨8, _⟩, ⟨8, _⟩ => (⟨6, by omega⟩, true)
  | ⟨8, _⟩, ⟨9, _⟩ => (⟨7, by omega⟩, true)
  | ⟨9, _⟩, ⟨0, _⟩ => (⟨9, by omega⟩, false)
  | ⟨9, _⟩, ⟨1, _⟩ => (⟨0, by omega⟩, true)
  | ⟨9, _⟩, ⟨2, _⟩ => (⟨1, by omega⟩, true)
  | ⟨9, _⟩, ⟨3, _⟩ => (⟨2, by omega⟩, true)
  | ⟨9, _⟩, ⟨4, _⟩ => (⟨3, by omega⟩, true)
  | ⟨9, _⟩, ⟨5, _⟩ => (⟨4, by omega⟩, true)
  | ⟨9, _⟩, ⟨6, _⟩ => (⟨5, by omega⟩, true)
  | ⟨9, _⟩, ⟨7, _⟩ => (⟨6, by omega⟩, true)
  | ⟨9, _⟩, ⟨8, _⟩ => (⟨7, by omega⟩, true)
  | ⟨9, _⟩, ⟨9, _⟩ => (⟨8, by omega⟩, true)
  -- The cases below are mathematically impossible:
  -- a Fin 10 value is always less than 10 by definition
  -- absurd derives anything from the contradictory hypothesis
  | ⟨n+10, h⟩, _ => absurd h (by omega)
  | _, ⟨n+10, h⟩ => absurd h (by omega)

def addDigits (a b : Digit) (carry : Bool) : Digit × Bool :=
  -- First look up a + b in the addition table
  let (sum, c1) := addTable a b
  -- If no incoming carry we are done
  match carry with
  | false => (sum, c1)
  | true =>
    -- Incoming carry: look up sum + 1 in the table
    let (sum', c2) := addTable sum ⟨1, by omega⟩
    -- Carry out if either addition produced a carry
    (sum', c1 || c2)
--A few Testcases
#eval addDigits ⟨7, by omega⟩ ⟨8, by omega⟩ false  -- 7+8=15, expect (5, true)
#eval addDigits ⟨3, by omega⟩ ⟨4, by omega⟩ false  -- 3+4=7, expect (7, false)
#eval addDigits ⟨9, by omega⟩ ⟨9, by omega⟩ true   -- 9+9+1=19, expect (9, true)

--Correctness Proof
--We shall first prove that the table is correct
theorem addTable_correct (a b : Digit) :
    (addTable a b).1.val + 10 * carryVal (addTable a b).2 =
    a.val + b.val := by
  fin_cases a <;> fin_cases b <;> simp [addTable, carryVal]
  --fin_cases a expands into all 10 possible values of a. Then fin_cases b for each —
  --giving 100 cases total. simp [addTable, carryVal] closes each one by
  --just looking up the table entry.

theorem addDigits_correct (a b : Digit) (carry : Bool) :
    (addDigits a b carry).1.val +
    10 * carryVal (addDigits a b carry).2 =
    a.val + b.val + carryVal carry := by
  -- Correctness of first table lookup: sum of a and b
  have h1 := addTable_correct a b
  -- Correctness of second table lookup: sum + 1 when carry is true
  have h2 := addTable_correct (addTable a b).1 ⟨1, by omega⟩
  -- Expand all 100 digit combinations and both carry values
  -- giving 200 concrete cases total
  -- In each case addTable reduces to a specific entry
  -- and simp_all verifies correctness by direct computation
  fin_cases a <;> fin_cases b <;> cases carry <;>
  simp_all [addDigits, addTable, carryVal]


--Now that we have a verified method to add two digits along with a carry
--it is just needed to extend it to column wise addition
--mimicking the way we do it with pen and paper

def verticalAdd : MultiDigit → MultiDigit → Bool → MultiDigit
  -- Base Case: Both numbers are exhausted and there is no remaining carry.
  | [], [], false => []
  --Final Carry Case: Both numbers are exhausted, but we have a leftover carry.
  -- This corresponds to the leading carry digit in ordinary arithmetic.
  | [], [], true  => [⟨1, by omega⟩]
  -- Extension Case (Right): Second list is longer.
  -- We continue adding the carry to the remaining digits of 'b'.
  | [], b :: bs, c =>
      let (d, c') := addDigits ⟨0, by omega⟩ b c
      d :: verticalAdd [] bs c'
  -- Extension Case (Left): First list is longer.
  -- We continue adding the carry to the remaining digits of 'a'.
  | a :: as, [], c =>
      let (d, c') := addDigits a ⟨0, by omega⟩ c
      d :: verticalAdd as [] c'
  -- Recursive Case: Standard column addition where both numbers have digits remaining.
  | a :: as, b :: bs, c =>
      let (d, c') := addDigits a b c
      d :: verticalAdd as bs c'
termination_by a b _ => a.length + b.length
-- Lean cannot automatically infer termination here,
-- so we explicitly provide a decreasing measure.
/-
  To prove this function eventually stops, we show the sum of the lengths
  of both lists strictly decreases with every recursive call.
-/

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
--Correctness Proof
--The proof mirrors the recursive structure of the algorithm
theorem verticalAdd_correct (a b : MultiDigit) (carry : Bool) :
    toNat (verticalAdd a b carry) =
    toNat a + toNat b + carryVal carry := by
  --Note : we are including the carry parameter to make the induction easier
  --actual addition would always correspond to carry = False
  induction a generalizing b carry with
  --We induct on list a considering all possible b and carry
  | nil =>
    --First list exhausted induction on second list
    induction b generalizing carry with
    | nil =>
      --both list empty
      cases carry <;> simp [verticalAdd, carryVal]
      --split into cases and simplify
    | cons b bs ihb =>
      --second list still has digits
      --adding 0 to each digit left
      simp only [verticalAdd, toNat]
      --utilizing correctness of single column addition(addDigits)
      have hcorrect := addDigits_correct ⟨0, by omega⟩ b carry
      ---- inductive hypothesis for remaining digits with new carry
      have hih := ihb (addDigits ⟨0, by omega⟩ b carry).2
      simp [carryVal, toNat] at *
      omega
  | cons a as iha =>
    induction b with
    | nil =>
      --second list empty first has digits remaining
      --mirror to step above
      simp only [verticalAdd, toNat]
      have hcorrect := addDigits_correct a ⟨0, by omega⟩ carry
      have hih := iha [] (addDigits a ⟨0, by omega⟩ carry).2
      simp [carryVal, toNat] at *
      omega
    | cons b bs _ =>
      --Main case: both list have digits
      simp only [verticalAdd, toNat]
      have hcorrect := addDigits_correct a b carry
      --inductive hypothesis
      have hih := iha bs (addDigits a b carry).2
      simp [carryVal, toNat] at *
      omega

 --Some basic lemmas/definitions for proofs later
theorem toNat_nonnegative (xs : MultiDigit) :
    0 ≤ toNat xs := by
  omega

--Subtraction

def subTable : Digit → Digit → Digit × Bool
  | ⟨0, _⟩, ⟨0, _⟩ => (⟨0, by omega⟩, false)
  | ⟨0, _⟩, ⟨1, _⟩ => (⟨9, by omega⟩, true)
  | ⟨0, _⟩, ⟨2, _⟩ => (⟨8, by omega⟩, true)
  | ⟨0, _⟩, ⟨3, _⟩ => (⟨7, by omega⟩, true)
  | ⟨0, _⟩, ⟨4, _⟩ => (⟨6, by omega⟩, true)
  | ⟨0, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, true)
  | ⟨0, _⟩, ⟨6, _⟩ => (⟨4, by omega⟩, true)
  | ⟨0, _⟩, ⟨7, _⟩ => (⟨3, by omega⟩, true)
  | ⟨0, _⟩, ⟨8, _⟩ => (⟨2, by omega⟩, true)
  | ⟨0, _⟩, ⟨9, _⟩ => (⟨1, by omega⟩, true)
  | ⟨1, _⟩, ⟨0, _⟩ => (⟨1, by omega⟩, false)
  | ⟨1, _⟩, ⟨1, _⟩ => (⟨0, by omega⟩, false)
  | ⟨1, _⟩, ⟨2, _⟩ => (⟨9, by omega⟩, true)
  | ⟨1, _⟩, ⟨3, _⟩ => (⟨8, by omega⟩, true)
  | ⟨1, _⟩, ⟨4, _⟩ => (⟨7, by omega⟩, true)
  | ⟨1, _⟩, ⟨5, _⟩ => (⟨6, by omega⟩, true)
  | ⟨1, _⟩, ⟨6, _⟩ => (⟨5, by omega⟩, true)
  | ⟨1, _⟩, ⟨7, _⟩ => (⟨4, by omega⟩, true)
  | ⟨1, _⟩, ⟨8, _⟩ => (⟨3, by omega⟩, true)
  | ⟨1, _⟩, ⟨9, _⟩ => (⟨2, by omega⟩, true)
  | ⟨2, _⟩, ⟨0, _⟩ => (⟨2, by omega⟩, false)
  | ⟨2, _⟩, ⟨1, _⟩ => (⟨1, by omega⟩, false)
  | ⟨2, _⟩, ⟨2, _⟩ => (⟨0, by omega⟩, false)
  | ⟨2, _⟩, ⟨3, _⟩ => (⟨9, by omega⟩, true)
  | ⟨2, _⟩, ⟨4, _⟩ => (⟨8, by omega⟩, true)
  | ⟨2, _⟩, ⟨5, _⟩ => (⟨7, by omega⟩, true)
  | ⟨2, _⟩, ⟨6, _⟩ => (⟨6, by omega⟩, true)
  | ⟨2, _⟩, ⟨7, _⟩ => (⟨5, by omega⟩, true)
  | ⟨2, _⟩, ⟨8, _⟩ => (⟨4, by omega⟩, true)
  | ⟨2, _⟩, ⟨9, _⟩ => (⟨3, by omega⟩, true)
  | ⟨3, _⟩, ⟨0, _⟩ => (⟨3, by omega⟩, false)
  | ⟨3, _⟩, ⟨1, _⟩ => (⟨2, by omega⟩, false)
  | ⟨3, _⟩, ⟨2, _⟩ => (⟨1, by omega⟩, false)
  | ⟨3, _⟩, ⟨3, _⟩ => (⟨0, by omega⟩, false)
  | ⟨3, _⟩, ⟨4, _⟩ => (⟨9, by omega⟩, true)
  | ⟨3, _⟩, ⟨5, _⟩ => (⟨8, by omega⟩, true)
  | ⟨3, _⟩, ⟨6, _⟩ => (⟨7, by omega⟩, true)
  | ⟨3, _⟩, ⟨7, _⟩ => (⟨6, by omega⟩, true)
  | ⟨3, _⟩, ⟨8, _⟩ => (⟨5, by omega⟩, true)
  | ⟨3, _⟩, ⟨9, _⟩ => (⟨4, by omega⟩, true)
  | ⟨4, _⟩, ⟨0, _⟩ => (⟨4, by omega⟩, false)
  | ⟨4, _⟩, ⟨1, _⟩ => (⟨3, by omega⟩, false)
  | ⟨4, _⟩, ⟨2, _⟩ => (⟨2, by omega⟩, false)
  | ⟨4, _⟩, ⟨3, _⟩ => (⟨1, by omega⟩, false)
  | ⟨4, _⟩, ⟨4, _⟩ => (⟨0, by omega⟩, false)
  | ⟨4, _⟩, ⟨5, _⟩ => (⟨9, by omega⟩, true)
  | ⟨4, _⟩, ⟨6, _⟩ => (⟨8, by omega⟩, true)
  | ⟨4, _⟩, ⟨7, _⟩ => (⟨7, by omega⟩, true)
  | ⟨4, _⟩, ⟨8, _⟩ => (⟨6, by omega⟩, true)
  | ⟨4, _⟩, ⟨9, _⟩ => (⟨5, by omega⟩, true)
  | ⟨5, _⟩, ⟨0, _⟩ => (⟨5, by omega⟩, false)
  | ⟨5, _⟩, ⟨1, _⟩ => (⟨4, by omega⟩, false)
  | ⟨5, _⟩, ⟨2, _⟩ => (⟨3, by omega⟩, false)
  | ⟨5, _⟩, ⟨3, _⟩ => (⟨2, by omega⟩, false)
  | ⟨5, _⟩, ⟨4, _⟩ => (⟨1, by omega⟩, false)
  | ⟨5, _⟩, ⟨5, _⟩ => (⟨0, by omega⟩, false)
  | ⟨5, _⟩, ⟨6, _⟩ => (⟨9, by omega⟩, true)
  | ⟨5, _⟩, ⟨7, _⟩ => (⟨8, by omega⟩, true)
  | ⟨5, _⟩, ⟨8, _⟩ => (⟨7, by omega⟩, true)
  | ⟨5, _⟩, ⟨9, _⟩ => (⟨6, by omega⟩, true)
  | ⟨6, _⟩, ⟨0, _⟩ => (⟨6, by omega⟩, false)
  | ⟨6, _⟩, ⟨1, _⟩ => (⟨5, by omega⟩, false)
  | ⟨6, _⟩, ⟨2, _⟩ => (⟨4, by omega⟩, false)
  | ⟨6, _⟩, ⟨3, _⟩ => (⟨3, by omega⟩, false)
  | ⟨6, _⟩, ⟨4, _⟩ => (⟨2, by omega⟩, false)
  | ⟨6, _⟩, ⟨5, _⟩ => (⟨1, by omega⟩, false)
  | ⟨6, _⟩, ⟨6, _⟩ => (⟨0, by omega⟩, false)
  | ⟨6, _⟩, ⟨7, _⟩ => (⟨9, by omega⟩, true)
  | ⟨6, _⟩, ⟨8, _⟩ => (⟨8, by omega⟩, true)
  | ⟨6, _⟩, ⟨9, _⟩ => (⟨7, by omega⟩, true)
  | ⟨7, _⟩, ⟨0, _⟩ => (⟨7, by omega⟩, false)
  | ⟨7, _⟩, ⟨1, _⟩ => (⟨6, by omega⟩, false)
  | ⟨7, _⟩, ⟨2, _⟩ => (⟨5, by omega⟩, false)
  | ⟨7, _⟩, ⟨3, _⟩ => (⟨4, by omega⟩, false)
  | ⟨7, _⟩, ⟨4, _⟩ => (⟨3, by omega⟩, false)
  | ⟨7, _⟩, ⟨5, _⟩ => (⟨2, by omega⟩, false)
  | ⟨7, _⟩, ⟨6, _⟩ => (⟨1, by omega⟩, false)
  | ⟨7, _⟩, ⟨7, _⟩ => (⟨0, by omega⟩, false)
  | ⟨7, _⟩, ⟨8, _⟩ => (⟨9, by omega⟩, true)
  | ⟨7, _⟩, ⟨9, _⟩ => (⟨8, by omega⟩, true)
  | ⟨8, _⟩, ⟨0, _⟩ => (⟨8, by omega⟩, false)
  | ⟨8, _⟩, ⟨1, _⟩ => (⟨7, by omega⟩, false)
  | ⟨8, _⟩, ⟨2, _⟩ => (⟨6, by omega⟩, false)
  | ⟨8, _⟩, ⟨3, _⟩ => (⟨5, by omega⟩, false)
  | ⟨8, _⟩, ⟨4, _⟩ => (⟨4, by omega⟩, false)
  | ⟨8, _⟩, ⟨5, _⟩ => (⟨3, by omega⟩, false)
  | ⟨8, _⟩, ⟨6, _⟩ => (⟨2, by omega⟩, false)
  | ⟨8, _⟩, ⟨7, _⟩ => (⟨1, by omega⟩, false)
  | ⟨8, _⟩, ⟨8, _⟩ => (⟨0, by omega⟩, false)
  | ⟨8, _⟩, ⟨9, _⟩ => (⟨9, by omega⟩, true)
  | ⟨9, _⟩, ⟨0, _⟩ => (⟨9, by omega⟩, false)
  | ⟨9, _⟩, ⟨1, _⟩ => (⟨8, by omega⟩, false)
  | ⟨9, _⟩, ⟨2, _⟩ => (⟨7, by omega⟩, false)
  | ⟨9, _⟩, ⟨3, _⟩ => (⟨6, by omega⟩, false)
  | ⟨9, _⟩, ⟨4, _⟩ => (⟨5, by omega⟩, false)
  | ⟨9, _⟩, ⟨5, _⟩ => (⟨4, by omega⟩, false)
  | ⟨9, _⟩, ⟨6, _⟩ => (⟨3, by omega⟩, false)
  | ⟨9, _⟩, ⟨7, _⟩ => (⟨2, by omega⟩, false)
  | ⟨9, _⟩, ⟨8, _⟩ => (⟨1, by omega⟩, false)
  | ⟨9, _⟩, ⟨9, _⟩ => (⟨0, by omega⟩, false)
  | ⟨n+10, h⟩, _ => absurd h (by omega)
  | _, ⟨n+10, h⟩ => absurd h (by omega)
