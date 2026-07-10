import Mathlib.Tactic.FinCases       -- fin_cases (was: import Mathlib.Tactic)
import Mathlib.Data.Fintype.Basic    -- Fintype (Fin 10) instance that fin_cases needs
import Arithmetic_Formalization.Foundations
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

--Test cases

#eval subTable ⟨7, by omega⟩ ⟨3, by omega⟩  -- expect (4, false)
#eval subTable ⟨3, by omega⟩ ⟨7, by omega⟩  -- expect (6, true)
#eval subTable ⟨0, by omega⟩ ⟨0, by omega⟩  -- expect (0, false)
#eval subTable ⟨9, by omega⟩ ⟨9, by omega⟩  -- expect (0, false)

def subDigits (a b : Digit) (borrow : Bool) : Digit × Bool :=
  -- First subtract b from a using the table
  let (diff, borrow1) := subTable a b
  -- If no incoming borrow we are done
  match borrow with
  | false => (diff, borrow1)
  | true =>
    -- Incoming borrow: subtract 1 more from the result
    let (diff', borrow2) := subTable diff ⟨1, by omega⟩
    -- Borrow out if either subtraction needed a borrow
    (diff', borrow1 || borrow2)

--Some test cases
#eval subDigits ⟨7, by omega⟩ ⟨3, by omega⟩ false  -- expect (4, false)
#eval subDigits ⟨3, by omega⟩ ⟨7, by omega⟩ false  -- expect (6, true)
#eval subDigits ⟨5, by omega⟩ ⟨5, by omega⟩ true   -- expect (9, true)
#eval subDigits ⟨6, by omega⟩ ⟨5, by omega⟩ true   -- expect (0, false)

--Correctness Proof
theorem subTable_correct (a b : Digit) :
    (subTable a b).1.val + b.val =
    a.val + 10 * carryVal (subTable a b).2 := by
  fin_cases a <;> fin_cases b <;> simp [subTable, carryVal]
--Same as addition; just looking up each table value and verifying equality

theorem subDigits_correct (a b : Digit) (borrow : Bool) :
    a.val + 10 * carryVal (subDigits a b borrow).2 =
    (subDigits a b borrow).1.val + b.val + carryVal borrow := by
  -- Explore all 100 digit combinations and both borrow values
  -- creating 200 concrete cases total
  fin_cases a <;> fin_cases b <;> cases borrow <;>
  -- Since all cases are finite, Lean can verify correctness
  -- by exhaustive case analysis and simplification.
  simp_all [subDigits, subTable, carryVal]

  --Similar to addition we now need a function that subtracts
  --two numbers similar to how we do it column wise
  --on pen and paper

def verticalSub : MultiDigit → MultiDigit → Bool → MultiDigit
  --Pre-condition:minuend>=subtrahend
  | [], [], false =>
      -- Both numbers exhausted, no remaining borrow
      -- Subtraction is complete
      []
  | [], [], true  =>
      -- Both numbers exhausted but borrow remaining
      -- This means toNat a < toNat b -- precondition violated
      -- Return empty list as sentinel for undefined result
      []
  | [], _ :: _, _ =>
      -- First number exhausted but second still has digits.
      -- Reached either when a < b (precondition violated), or when the
      -- remaining digits of b are all zeros — in which case [] (value 0)
      -- is the correct answer. Under the theorem's hypothesis the
      -- remaining value of b is forced to 0, so [] is always honest there.
      []
  | a :: as, [], borrow =>
  --Lean syntax note:
  -- 'a :: as' means a list with head 'a' and tail 'as'
  -- [] means an empty list
  -- So '| a :: as, [], borrow =>' matches when
  -- the first number has at least one digit (head 'a', rest 'as')
  -- and the second number is empty
      -- Second number exhausted, first still has digits
      -- Subtract 0 from remaining digits of a, propagating borrow
      let (d, borrow') := subDigits a ⟨0, by omega⟩ borrow
      d :: verticalSub as [] borrow'
  | a :: as, b :: bs, borrow =>
      -- Main case: both numbers have digits available
      -- Subtract current digits with incoming borrow
      -- Pass outgoing borrow to next column
      let (d, borrow') := subDigits a b borrow
      d :: verticalSub as bs borrow'
termination_by a b _ => a.length + b.length
-- Termination: sum of list lengths decreases at every recursive call

--Some test cases
-- 123 - 91 = 32
#eval toNat (verticalSub
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [⟨1, by omega⟩, ⟨9, by omega⟩]
  false)
-- expect 32

-- 100 - 1 = 99
#eval toNat (verticalSub
  [⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]
  [⟨1, by omega⟩]
  false)
-- expect 99

-- 999 - 999 = 0
#eval toNat (verticalSub
  [⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩]
  [⟨9, by omega⟩, ⟨9, by omega⟩, ⟨9, by omega⟩]
  false)
-- expect 0

-- We now prove that `verticalSub` correctly implements
-- column-wise decimal subtraction.

theorem verticalSub_correct (a b : MultiDigit) (borrow : Bool)
    (h : toNat b + carryVal borrow ≤ toNat a) :
    toNat (verticalSub a b borrow) + toNat b + carryVal borrow =
    toNat a := by
  -- We induct on list a considering all possible b and borrow
  induction a generalizing b borrow with
  | nil =>
    -- First list exhausted
    -- induct on second list considering all possible borrow values
    induction b generalizing borrow with
    | nil =>
      -- Both lists empty
      -- simp reduces toNat [] to 0 and carryVal to concrete value
      -- at * applies simp to hypothesis h as well not just the goal
      simp only [toNat,  carryVal] at *
      cases borrow <;> simp_all [verticalSub]
    | cons b bs ihb =>
      -- First empty, second has digits
      -- algorithm returns [] for this case
      -- precondition h forces toNat (b::bs) + carryVal borrow = 0
      simp only [verticalSub, toNat, carryVal] at *
      cases borrow with
      | false =>
        simp only [] at *
        omega
      | true =>
        simp only [] at *
        omega
  | cons a as iha =>
    induction b with
    | nil =>
      -- Second empty, first has digits
      -- subtract 0 from remaining digits propagating borrow
      simp only [verticalSub, toNat]
      -- correctness of subtracting 0 from digit a with current borrow
      have hcorrect := subDigits_correct a ⟨0, by omega⟩ borrow
      -- precondition for recursive call with new borrow
      have hpre : toNat [] + carryVal (subDigits a ⟨0, by omega⟩ borrow).2 ≤
                  toNat as := by
        simp [toNat, carryVal] at h ⊢
        have := subDigits_correct a ⟨0, by omega⟩ borrow
        simp [carryVal] at this
        omega
      -- inductive hypothesis for remaining digits with new borrow
      have hih := iha [] (subDigits a ⟨0, by omega⟩ borrow).2 hpre
      simp [carryVal, toNat] at *
      omega
    | cons b bs _ =>
      -- Main case: both lists have digits
      simp only [verticalSub, toNat]
      -- correctness of subtracting digit b from digit a with current borrow
      have hcorrect := subDigits_correct a b borrow
      -- precondition for recursive call with new borrow
      have hpre : toNat bs + carryVal (subDigits a b borrow).2 ≤ toNat as := by
        simp [toNat, carryVal] at h ⊢
        have := subDigits_correct a b borrow
        simp [carryVal] at this
        omega
      -- inductive hypothesis for remaining digits with new borrow
      -- this handles the recursive part of the algorithm
      have hih := iha bs (subDigits a b borrow).2 hpre
      simp [carryVal, toNat] at *
      -- hcorrect and hih together give omega enough to close the goal
      omega

-- The main correctness theorem without borrow parameter
-- Only valid when toNat a ≥ toNat b
-- carryVal false = 0 so the borrow term vanishes
theorem verticalSub_correct' (a b : MultiDigit)
    (h : toNat b ≤ toNat a) :
    toNat (verticalSub a b false) + toNat b = toNat a := by
  have hpre : toNat b + carryVal false ≤ toNat a := by
    simp only [carryVal]
    exact h
  have hmain := verticalSub_correct a b false hpre
  simp only [carryVal] at hmain
  exact hmain
