import Arithmetic_Formalization.Foundations
import Arithmetic_Formalization.Multiplication

-- Find the largest q (0-9) such that b * q ≤ n
-- This is the "trial digit" step in pen and paper division
def findQuotientDigitHelper (n : Nat) (b : Digit) : Nat → Digit
  | 0 => ⟨0, by omega⟩
  | q + 1 =>
      if h : q + 1 < 10 then
        let qDigit : Digit := ⟨q + 1, h⟩
        let (units, tens) := mulTable qDigit b
        -- Reconstruct the full value from your multiplication table lookup
        if units.val + 10 * tens.val ≤ n then
          qDigit
        else
          findQuotientDigitHelper n b q
      else
        ⟨0, by omega⟩

-- Top-level cleaner definition initialized at 9
def findQuotientDigit (n : Nat) (b : Digit) : Digit :=
  findQuotientDigitHelper n b 9

#eval findQuotientDigit 23 ⟨5, by omega⟩  -- expect 4
#eval findQuotientDigit 45 ⟨5, by omega⟩  -- expect 9

/-
  Strips high-place-value zeros from the end of our LSB-first list.
  Turns [3, 3, 0] into [3, 3], and [0, 0, 0] into []
-/
def trimTrailingZeros : MultiDigit → MultiDigit
  | [] => []
  | d :: ds =>
      match trimTrailingZeros ds with
      | [] => if d.val == 0 then [] else [d]
      | ts => d :: ts

-- Long division of a MultiDigit number by a single Digit
def longDivHelper : List Digit → Digit → Nat → MultiDigit × Nat
  | [], _, acc => ([], acc)
  | d :: ds, b, acc =>
      let currentRem := acc * 10 + d.val
      let q := findQuotientDigit currentRem b
      -- Subtract the verified table value
      let (units, tens) := mulTable q b
      let newRem := currentRem - (units.val + 10 * tens.val)
      let (quotTail, finalRem) := longDivHelper ds b newRem
      (q :: quotTail, finalRem)

def longDiv (a : MultiDigit) (b : Digit) : MultiDigit × Nat :=
  let (quot, rem) := longDivHelper a.reverse b 0
  -- Clean up the reversed quotient using our trailing zero trimmer
  (trimTrailingZeros quot.reverse, rem)

--- Test Cases ---

-- 1234 ÷ 5 = 246 remainder 4
#eval longDiv
  [⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  ⟨5, by omega⟩
-- Expects: ([6, 4, 2], 4)  -> which is 246 LSB-first!

-- 100 ÷ 3 = 33 remainder 1
#eval longDiv
  [⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]
  ⟨3, by omega⟩
-- Expects: ([3, 3], 1)     -> No more dead trailing zeros!

-- 891 ÷ 9 = 99 remainder 0
#eval longDiv
  [⟨1, by omega⟩, ⟨9, by omega⟩, ⟨8, by omega⟩]
  ⟨9, by omega⟩
-- Expects: ([9, 9], 0)

--Correctness
-- The quotient digit is correct:
-- b * q ≤ n and n < b * (q + 1)
set_option maxHeartbeats 0 in
-- Required because combining `fin_cases` (10 cases)
-- with `split_ifs` (up to 10 nested conditions per case) creates a massive
-- combinatorial explosion that exceeds the default heartbeat budget.
theorem findQuotientDigit_correct (n : Nat) (b : Digit) (hb : b.val ≠ 0) (hn : n < 10 * b.val) :
    (findQuotientDigit n b).val * b.val ≤ n ∧
    n < ((findQuotientDigit n b).val + 1) * b.val := by
  -- Unfold definitions and rewrite mulTable lookups to raw multiplication
  simp [findQuotientDigit, findQuotientDigitHelper, mulTable_correct]
  -- Case-split digit b (0-9), break open nested if-statements, and let omega solve boundaries
  fin_cases b <;> try simp_all <;> try split_ifs <;> omega

theorem trimTrailingZeros_correct (a : MultiDigit) :
    toNat (trimTrailingZeros a) = toNat a := by
  -- Structural induction on the digit list.
  -- We show that removing redundant most-significant zeros
  -- does not change the represented natural number.
  induction a with
  | nil =>
    -- Base case: the empty list already has value 0.
    simp [trimTrailingZeros]
  | cons d ds ih =>
    -- Evaluate one step of trimTrailingZeros.
    -- The behaviour depends on what happens after trimming the tail.
    unfold trimTrailingZeros
    -- Split on the recursively trimmed tail.
    cases h : trimTrailingZeros ds with
    | nil =>
      -- The tail trims completely to [].
      -- By the inductive hypothesis, the original tail must also
      -- represent the number 0.
      have hds : toNat ds = 0 := by
        have := ih
        rw [h] at this
        simp [toNat] at this
        exact this.symm
      -- Now the result depends on whether the current digit is zero.
      by_cases hd : d.val = 0
      · -- If the current digit is also 0, the entire number represents 0.
        -- The trimming procedure returns [] and preserves the value.
        have hd' : d = ⟨0, by omega⟩ := by
          ext
          exact hd
        simp [hd', toNat, hds]
      · -- If the current digit is nonzero, it becomes the sole remaining digit.
        -- Since the tail contributes 0, the numeric value is unchanged.
        simp [hd, toNat, hds]
    | cons t ts =>
      -- The trimmed tail is nonempty.
      -- In this case trimTrailingZeros keeps the current digit and
      -- recursively trimmed tail.
      -- The inductive hypothesis tells us that replacing ds by
      -- trimTrailingZeros ds preserves the represented value.
      simp [toNat, ← ih, h]

theorem toNat_reverse_cons (d : Digit) (ds : List Digit) :
    toNat (d :: ds).reverse =
    toNat ds.reverse + d.val * 10^(ds.length) := by
  -- Reversing a cons places the head digit at the end.
  rw [List.reverse_cons]
  -- Expand the value of an appended digit list:
  -- toNat (a ++ b) = toNat a + 10^(length a) * toNat b.
  rw [toNat_append]
  -- The length of a list is unchanged by reversal.
  rw [List.length_reverse]
  -- The appended singleton contributes exactly the digit d.
  simp [toNat]
  -- Finish with elementary algebra.
  ring

theorem longDivHelper_length (ds : List Digit) (b : Digit) (acc : Nat) :
    (longDivHelper ds b acc).1.length = ds.length := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    -- 1. Unfold the recursive definition to expose the let-bindings
    unfold longDivHelper
    -- 2. dsimp cleans up the let-bindings so the goal becomes:
    -- (longDivHelper ds ...).1.length + 1 = ds.length + 1
    dsimp only
    -- 3. simp applies our Inductive Hypothesis, which instantly
    -- replaces the function call with 'ds.length', closing the goal.
    simp [ih]


theorem longDivHelper_correct (ds : List Digit) (b : Digit) (hb : b.val ≠ 0)
    (acc : Nat) (hacc : acc < b.val) :
    let (quot, rem) := longDivHelper ds b acc
    acc * 10^(ds.length) + toNat ds.reverse =
      toNat quot.reverse * b.val + rem ∧ rem < b.val := by
  -- Induction on the remaining digits.
  -- The accumulator stores the current remainder and satisfies acc < b.
  induction ds generalizing acc with
  | nil =>
      -- No digits remain: acc is the final remainder.
      simp [longDivHelper, hacc]
  | cons d ds ih =>
      unfold longDivHelper
      -- Bring down the next digit as in ordinary long division.
      set currentRem := acc * 10 + d.val
      -- Select the next quotient digit and resulting remainder.
      set q := findQuotientDigit currentRem b
      set units := (mulTable q b).1
      set tens := (mulTable q b).2
      set newRem := currentRem - (units.val + 10 * tens.val)
      have hd : d.val < 10 := d.isLt
      -- Since acc < b and d < 10, the current dividend is < 10*b.
      have h_bound : currentRem < 10 * b.val := by
        dsimp [currentRem]
        omega

      -- The quotient digit satisfies:
      --     q*b ≤ currentRem < (q+1)*b.
      have ⟨hq_lower, hq_upper⟩ :=
        findQuotientDigit_correct currentRem b hb h_bound
      have h_dist :
          (q.val + 1) * b.val =
          q.val * b.val + b.val := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [h_dist] at hq_upper
      -- Multiplication table correctness.
      have h_mul_eq :
          units.val + 10 * tens.val =
          q.val * b.val :=
        mulTable_correct q b
      -- The new remainder remains strictly smaller than the divisor.
      have h_newRem_bound : newRem < b.val := by
        dsimp [newRem, currentRem]
        rw [h_mul_eq]
        omega
      cases h_rec : longDivHelper ds b newRem with
      | mk quotTail finalRem =>
      -- Apply the induction hypothesis to the recursive call.
      have h_ih := ih newRem h_newRem_bound
      rw [h_rec] at h_ih
      dsimp only at h_ih
      dsimp only
      try rw [h_rec]
      dsimp only
      constructor
      · -- Combine recursive correctness with the current division step
        -- to obtain:
        --     dividend = divisor * quotient + remainder.
        rw [List.length_cons]
        rw [toNat_reverse_cons d ds]
        rw [toNat_reverse_cons q quotTail]
        have h_len := longDivHelper_length ds b newRem
        rw [h_rec] at h_len
        dsimp only at h_len
        rw [h_len]
        rw [Nat.pow_add, Nat.pow_one]
        have h_eq := h_ih.1
        generalize 10^(ds.length) = E at *
        -- Rewrite the current dividend as newRem + q*b.
        have h_sub :
            newRem =
            (acc * 10 + d.val) - q.val * b.val := by
          dsimp [newRem, currentRem]
          rw [h_mul_eq]
        have h_rem_add :
            acc * 10 + d.val =
            newRem + q.val * b.val := by
          rw [h_sub]
          exact (Nat.sub_add_cancel hq_lower).symm
        calc
          acc * (E * 10) + (toNat ds.reverse + d.val * E)
              = (acc * 10 + d.val) * E + toNat ds.reverse := by ring
          _ = (newRem + q.val * b.val) * E + toNat ds.reverse := by
                rw [h_rem_add]
          _ = (newRem * E + toNat ds.reverse) + q.val * E * b.val := by ring
          _ = (toNat quotTail.reverse * b.val + finalRem)
                + q.val * E * b.val := by
                rw [h_eq]
          _ = (toNat quotTail.reverse + q.val * E)
                * b.val + finalRem := by ring
      · -- The recursive call already guarantees the remainder bound.
        exact h_ih.2

theorem longDiv_correct (a : MultiDigit) (b : Digit) (hb : b.val ≠ 0) :
    let (q, r) := longDiv a b
    toNat a = toNat q * b.val + r ∧ r < b.val := by
  unfold longDiv
  -- Unpack the result of the helper function.
  cases h : longDivHelper a.reverse b 0 with
  | mk quotTail finalRem =>
  dsimp only
  -- Apply the correctness theorem for the helper with
  -- initial remainder 0.
  have h_helper :=
    longDivHelper_correct a.reverse b hb 0 (by omega)
  rw [h] at h_helper
  dsimp only at h_helper
  -- Trimming leading zeros from the quotient does not
  -- change its numeric value.
  have h_trim := trimTrailingZeros_correct quotTail.reverse
  rw [h_trim]
  -- Recover the original number from its double reversal.
  have h_rev_rev : a.reverse.reverse = a :=
    List.reverse_reverse a
  constructor
  · -- The helper theorem already establishes:
    -- dividend = divisor × quotient + remainder.
    have h_eq := h_helper.1
    rw [← h_rev_rev]
    omega
  · -- The helper theorem also guarantees the remainder bound.
    exact h_helper.2
