import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Arithmetic_Formalization.Foundations
import Arithmetic_Formalization.Subtraction
import Arithmetic_Formalization.Multiplication
import Arithmetic_Formalization.Division

--Integer square root: the standard pen-and-paper algorithm.

-- Group a LSB-first digit list into (lo, hi) pairs from the front.
-- The first pair is the RIGHTMOST pair of the original number.
-- A singleton at the end (odd-length input) is paired with a zero.
-- After reversing the result, pairs are in MSB-first processing order.
def chunkPairs : MultiDigit → List (Digit × Digit)
  | []           => []
  | [d]          => [(d, ⟨0, by omega⟩)]
  | d1 :: d2 :: ds => (d1, d2) :: chunkPairs ds
termination_by ds => ds.length

-- Find the largest x (0-9) such that (2q·10 + x) · x ≤ n.
-- twoQ = 2·q as a MultiDigit, precomputed by the caller.
-- Direct analog of findQuotientDigitHelper:
-- same downward search from 9, but the "divisor" shifts with x.
def findSqrtDigitHelper (n : Nat) (twoQ : MultiDigit) : Nat → Digit
  | 0 => ⟨0, by omega⟩
  | x + 1 =>
      if h : x + 1 < 10 then
        let xDigit : Digit := ⟨x + 1, h⟩
        -- Trial divisor: 2q·10 + x
        -- LSB-first: x is the units digit, twoQ is everything above
        -- toNat (xDigit :: twoQ) = x + 10 * (2 * toNat q) = 2·q·10 + x ✓
        let trialDivisor : MultiDigit := xDigit :: twoQ
        -- Trial product: (2q·10 + x) · x
        let trialProduct := mulDigit trialDivisor xDigit ⟨0, by omega⟩
        if toNat trialProduct ≤ n then
          xDigit
        else
          findSqrtDigitHelper n twoQ x
      else
        ⟨0, by omega⟩

def findSqrtDigit (n : Nat) (q : MultiDigit) : Digit :=
  -- Precompute 2q once; all nine trial values of x share it
  let twoQ := mulDigit q ⟨2, by omega⟩ ⟨0, by omega⟩
  findSqrtDigitHelper n twoQ 9

-- Basic test cases
#eval findSqrtDigit 12  []
  -- expect 3  (3²=9 ≤ 12 < 16=4²)
#eval findSqrtDigit 334 [⟨3, by omega⟩]
  -- expect 5  (q=3, (60+5)·5=325 ≤ 334 < 360=(60+6)·6)
#eval findSqrtDigit 956 [⟨5, by omega⟩, ⟨3, by omega⟩]
  -- expect 1  (q=35, (700+1)·1=701 ≤ 956 < 1404=(700+2)·2)

-- Core loop over pairs in MSB-first order.
-- acc : current partial remainder (LSB-first)
-- q   : partial root built so far (LSB-first, grown by prepending)
--   We process MSB → LSB, so each new digit is LESS significant
--   than all previous ones. Prepending puts it at position 0 = units.
def sqrtHelper
    : List (Digit × Digit) → MultiDigit → MultiDigit → MultiDigit × MultiDigit
  | [], acc, q => (q, acc)
  | (lo, hi) :: pairs, acc, q =>
      -- Bring down the next pair.
      -- lo :: hi :: acc represents lo + hi·10 + 100·toNat(acc)
      --                        = (hi·10 + lo) + 100·toNat(acc)
      let currentRem : MultiDigit := lo :: hi :: acc
      -- Precompute 2q — used both in the search and in the subtraction
      let twoQ := mulDigit q ⟨2, by omega⟩ ⟨0, by omega⟩
      -- Find x: largest digit s.t. (2q·10 + x)·x ≤ currentRem
      let x := findSqrtDigitHelper (toNat currentRem) twoQ 9
      -- Trial divisor: 2q·10 + x
      let trialDivisor : MultiDigit := x :: twoQ
      -- Trial product: the amount subtracted this step
      let trialProduct := mulDigit trialDivisor x ⟨0, by omega⟩
      -- Subtract: safe because findSqrtDigit guarantees trialProduct ≤ currentRem
      let newRem := verticalSub currentRem trialProduct false
      -- Prepend x: x is the next (less significant) digit of the root
      sqrtHelper pairs newRem (x :: q)
termination_by pairs _ _ => pairs.length

def intSqrt (a : MultiDigit) : MultiDigit × MultiDigit :=
  -- Convert the number into digit-pairs and process them
-- from most significant pair to least significant pair,
-- exactly as in the standard pen-and-paper square root algorithm.
  let pairs := (chunkPairs a).reverse
  let (q, r) := sqrtHelper pairs [] []
  (trimTrailingZeros q, trimTrailingZeros r)

--- Test Cases ---

-- √1234 = 35, remainder 9   (35²=1225, 1234-1225=9)
#eval intSqrt
  [⟨4,by omega⟩, ⟨3,by omega⟩, ⟨2,by omega⟩, ⟨1,by omega⟩]
-- expect ([5,3], [9])

-- √12345 = 111, remainder 24   (111²=12321, 12345-12321=24)
#eval intSqrt
  [⟨5,by omega⟩, ⟨4,by omega⟩, ⟨3,by omega⟩, ⟨2,by omega⟩, ⟨1,by omega⟩]
-- expect ([1,1,1], [4,2])

-- √123456 = 351, remainder 255   (351²=123201, 123456-123201=255)
#eval intSqrt
  [⟨6,by omega⟩, ⟨5,by omega⟩, ⟨4,by omega⟩,
   ⟨3,by omega⟩, ⟨2,by omega⟩, ⟨1,by omega⟩]
-- expect ([1,5,3], [5,5,2])

-- √100 = 10, remainder 0
#eval intSqrt [⟨0,by omega⟩, ⟨0,by omega⟩, ⟨1,by omega⟩]
-- expect ([0,1], [])

-- √9999 = 99, remainder 198   (99²=9801, 9999-9801=198)
#eval intSqrt
  [⟨9,by omega⟩, ⟨9,by omega⟩, ⟨9,by omega⟩, ⟨9,by omega⟩]
-- expect ([9,9], [8,9,1])

-- √0 = 0
#eval intSqrt []
-- expect ([], [])


/-

The core invariant of the digit search:
The returned digit `res`, when combined with `twoQ`, produces a trial product
that is mathematically less than or equal to `n`.
-/
theorem findSqrtDigitHelper_correct (n : Nat) (twoQ : MultiDigit) (x : Nat) :
  let res := findSqrtDigitHelper n twoQ x
  (toNat twoQ * 10 + res.val) * res.val ≤ n := by
  induction x with
  | zero =>
    -- Base case: x = 0. findSqrtDigitHelper returns 0.
    -- (toNat twoQ * 10 + 0) * 0 ≤ n reduces to 0 ≤ n, which is true.
    simp [findSqrtDigitHelper]
  | succ x ih =>
    -- 1. Unfold to expose the function body and crush let bindings
    simp only [findSqrtDigitHelper]
    -- 2. Split the outer 'if' (x + 1 < 10)
    split
    · case isTrue h =>
      -- 3. Split the inner 'if' (toNat trialProduct ≤ n)
      split
      · case isTrue h_leq =>
        -- 4. Bridge the structural multiplication to pure algebraic multiplication
        have h_arith : toNat (mulDigit (⟨x + 1, h⟩ :: twoQ) ⟨x + 1, h⟩ ⟨0, by omega⟩) =
                       (toNat twoQ * 10 + (x + 1)) * (x + 1) := by
          rw [mulDigit_correct]
          simp [toNat]
          ring
        -- Rewrite the structural product into the algebraic product to match h_leq
        rw [h_arith] at h_leq
        exact h_leq
      · case isFalse h_nleq =>
        -- If trial product > n, it recurses to x. The inductive hypothesis holds.
        exact ih
    · case isFalse h =>
      -- If x + 1 < 10 is false, it returns 0.
      simp

-- Correctness
-- Proves the lower bound for findSqrtDigit:
-- the returned digit x satisfies (2q·10 + x)·x ≤ n.
-- This is the safe-subtraction guarantee — sqrtHelper uses it
-- to justify that verticalSub won't underflow.
theorem findSqrtDigit_correct (n : Nat) (q : MultiDigit) :
    let x    := findSqrtDigit n q
    let twoQ := mulDigit q ⟨2, by omega⟩ ⟨0, by omega⟩
    (toNat twoQ * 10 + x.val) * x.val ≤ n := by
  -- Unfold the wrapper to expose the twoQ precomputation
  -- and the call to findSqrtDigitHelper at starting value 9
  simp only [findSqrtDigit]
  -- Delegate to the helper theorem; the underscore infers twoQ
  exact findSqrtDigitHelper_correct n _ 9

-- Proves that chunking a digit list into pairs preserves its numeric value.
-- The foldr reconstructs the number from LSB pairs rightward,
-- matching how toNat builds the value from individual digits.
theorem chunkPairs_correct (a : MultiDigit) :
    (chunkPairs a).foldr (fun p acc =>
      p.1.val + p.2.val * 10 + acc * 100) 0 = toNat a := by
  -- Use the custom induction principle matching chunkPairs' three cases:
  -- nil, singleton, and two-or-more — avoids awkward raw structural induction
  induction a using chunkPairs.induct with
  | case1 =>
    -- Empty list: both sides are 0
    simp [chunkPairs, toNat]
  | case2 d =>
    -- Singleton: paired with phantom zero ⟨0,_⟩
    -- foldr gives d.val + 0·10 + 0·100 = d.val = toNat [d] ✓
    simp [chunkPairs, toNat]
  | case3 d1 d2 ds ih =>
    -- Two-or-more: (d1,d2) is the current pair, ih handles the tail ds
    -- simp unfolds one chunkPairs step and substitutes ih for the tail;
    -- ring closes the positional arithmetic identity
    simp [chunkPairs, toNat, ih]
    ring


-- Proves the upper bound for the digit search:
-- any digit y strictly larger than the result has trial product > n.
-- Combined with findSqrtDigitHelper_correct (lower bound), this
-- establishes that the returned digit is the LARGEST valid one
-- Statement: if y > res and y ≤ start (y was tried and rejected),
-- then (twoQ·10 + y)·y > n.
theorem findSqrtDigitHelper_maximal (n : Nat) (twoQ : MultiDigit) :
    ∀ start, start < 10 → ∀ y,
      (findSqrtDigitHelper n twoQ start).val < y → y ≤ start →
      n < (toNat twoQ * 10 + y) * y := by
  intro start
  induction start with
  | zero =>
    -- y > res ≥ 0 and y ≤ 0 is a contradiction
    intro _ y hy hyle
    omega
  | succ x ih =>
    intro hstart y hy hyle
    -- Unfold one step of findSqrtDigitHelper to expose
    -- the two if-branches (x+1 < 10, and product ≤ n)
    simp only [findSqrtDigitHelper] at hy
    split at hy
    · rename_i h
      -- Bridge mulDigit's result to plain algebraic multiplication
      -- so h_nleq and later goals can reason about (twoQ·10 + x+1)·(x+1)
      have h_arith :
          toNat (mulDigit (⟨x + 1, h⟩ :: twoQ) ⟨x + 1, h⟩ ⟨0, by omega⟩)
            = (toNat twoQ * 10 + (x + 1)) * (x + 1) := by
        rw [mulDigit_correct]; simp [toNat]; ring
      split at hy
      · -- Inner if was true: result is ⟨x+1,h⟩
        -- hy says result.val < y, i.e. x+1 < y
        -- but hyle says y ≤ x+1 — contradiction
        have hxv : (x + 1 : Nat) < y := hy
        omega
      · -- Inner if was false: trial product > n, so we recurse to x
        rename_i h_nleq
        -- Rewrite h_nleq into algebraic form
        rw [h_arith] at h_nleq
        rcases Nat.lt_or_ge y (x + 1) with hyx | hyx
        · -- y < x+1: y was also rejected at an earlier step; apply IH
          exact ih (by omega) y hy (by omega)
        · -- y = x+1: this is exactly the candidate that failed the check
          -- h_nleq directly gives n < (twoQ·10 + y)·y
          have hye : y = x + 1 := by omega
          subst hye
          exact Nat.not_le.mp h_nleq
    · -- x+1 ≥ 10: impossible since start < 10
      rename_i h
      omega

def pairsVal (l : List (Digit × Digit)) : Nat :=
  l.foldl (fun v p => p.1.val + p.2.val * 10 + v * 100) 0

-- Generalizes the foldl accumulator for pairsVal:
-- a fold starting from c equals 100^length × c plus the fold from zero.
-- This is the key lemma for the sqrtHelper invariant —
-- it lets us split the positional value at any point in the pair list,
-- exactly as toNat_append does for ordinary digit lists.
theorem pairsVal_foldl_init (l : List (Digit × Digit)) (c : Nat) :
    l.foldl (fun v p => p.1.val + p.2.val * 10 + v * 100) c
      = 100 ^ l.length * c + pairsVal l := by
  unfold pairsVal
  -- Induct on l generalizing c — the accumulator changes at every
  -- recursive call so the IH must hold for all starting values
  induction l generalizing c with
  | nil =>
    -- Empty list: 100^0 × c + 0 = c ✓
    simp
  | cons p l ih =>
    -- Step one foldl forward on both sides, exposing the tail fold.
    -- Two ih instantiations are needed:
    --   one for the general-c fold (left side)
    --   one for the zero-init fold (right side, inside pairsVal)
    -- ring then closes the base-100 positional arithmetic identity.
    rw [show (p :: l).foldl (fun v p => p.1.val + p.2.val * 10 + v * 100) c
          = l.foldl (fun v p => p.1.val + p.2.val * 10 + v * 100)
              (p.1.val + p.2.val * 10 + c * 100) from rfl,
        show (p :: l).foldl (fun v p => p.1.val + p.2.val * 10 + v * 100) 0
          = l.foldl (fun v p => p.1.val + p.2.val * 10 + v * 100)
              (p.1.val + p.2.val * 10 + 0 * 100) from rfl,
        -- IH at the general-c accumulator (left side)
        ih (p.1.val + p.2.val * 10 + c * 100),
        -- IH at the zero accumulator (right side, pairsVal)
        ih (p.1.val + p.2.val * 10 + 0 * 100),
        List.length_cons, pow_succ]
    ring

-- Bridges the two value representations:
-- pairsVal (MSB-first foldl) of the reversed chunk list equals toNat a.
-- Used in intSqrt_correct to connect the helper's output to the original number.
theorem pairsVal_chunkPairs (a : MultiDigit) :
    pairsVal (chunkPairs a).reverse = toNat a := by
  unfold pairsVal
  -- foldl on the reversed list equals foldr on the original —
  -- converting pairsVal's left fold into chunkPairs_correct's right fold
  rw [List.foldl_reverse]
  exact chunkPairs_correct a

-- One unfolding step of pairsVal: the head pair contributes its value
-- shifted left by 100^(remaining pairs), plus the value of the tail.
-- Used in sqrtHelper_correct to split off the current pair's contribution
-- at each inductive step — analogous to List.length_cons for lengths.
theorem pairsVal_cons (p : Digit × Digit) (l : List (Digit × Digit)) :
    pairsVal (p :: l) = 100 ^ l.length * (p.1.val + p.2.val * 10) + pairsVal l := by
  -- Unfold one foldl_cons step on the left to expose the tail fold
  conv_lhs => rw [pairsVal, List.foldl_cons]
  -- pairsVal_foldl_init handles the general-init foldl
  rw [pairsVal_foldl_init]
  congr 1


theorem sqrtHelper_correct :
    ∀ (pairs : List (Digit × Digit)) (acc q : MultiDigit),
      toNat acc ≤ 2 * toNat q →
      toNat (sqrtHelper pairs acc q).1 * toNat (sqrtHelper pairs acc q).1
          + toNat (sqrtHelper pairs acc q).2
        = 100 ^ pairs.length * (toNat q * toNat q + toNat acc) + pairsVal pairs
      ∧ toNat (sqrtHelper pairs acc q).2 ≤ 2 * toNat (sqrtHelper pairs acc q).1 := by
  -- acc and q are universally quantified in the statement, so the IH
  -- is automatically general over them — no `generalizing` needed.
  -- This lets us apply the IH at newRem and x::q in the recursive step.
  intro pairs
  induction pairs with
  | nil =>
    -- No pairs: sqrtHelper returns (q, acc) immediately.
    -- Equation: q²+acc = 100^0*(q²+acc) + 0 ✓
    -- Bound:    acc ≤ 2q is exactly hinv ✓
    intro acc q hinv
    refine ⟨by simp [sqrtHelper, pairsVal], by simpa [sqrtHelper] using hinv⟩
  | cons p rest ih =>
    intro acc q hinv
    obtain ⟨lo, hi⟩ := p
    -- Unfold one step of sqrtHelper to expose the let-bindings
    simp only [sqrtHelper]
    -- Name all intermediate values for readability.
    -- set replaces every occurrence in the goal and hypotheses,
    -- and records the definition as a named equation (e.g. hcur).
    set cur    : MultiDigit := lo :: hi :: acc with hcur
    set twoQ   : MultiDigit := mulDigit q ⟨2, by omega⟩ ⟨0, by omega⟩ with htwoQ
    set x      : Digit      := findSqrtDigitHelper (toNat cur) twoQ 9 with hx
    set trial  : MultiDigit := mulDigit (x :: twoQ) x ⟨0, by omega⟩ with htrial
    set newRem : MultiDigit := verticalSub cur trial false with hnewRem
    --  Numeric value facts
    -- Convert MultiDigit expressions to plain Nat for ring/linarith.
    -- Bring-down value: lo + hi·10 + 100·acc
    have hC : toNat cur = lo.val + hi.val * 10 + 100 * toNat acc := by
      rw [hcur]; simp [toNat] <;> ring
    -- 2q as a Nat
    have hTQ : toNat twoQ = 2 * toNat q := by
      rw [htwoQ, mulDigit_correct]; simp <;> ring
    -- Trial product value: (2q·10 + x)·x
    have hP : toNat trial = (toNat twoQ * 10 + x.val) * x.val := by
      rw [htrial, mulDigit_correct]
      change toNat (x :: twoQ) * x.val + (0 : Nat) = (toNat twoQ * 10 + x.val) * x.val
      rw [show toNat (x :: twoQ) = x.val + 10 * toNat twoQ from rfl]
      ring
    -- New partial root value: x + 10·q
    have hxqv : toNat (x :: q) = x.val + 10 * toNat q := by
      simp [toNat] <;> ring
    --  Safe subtraction
    -- findSqrtDigitHelper_correct guarantees trial ≤ cur,
    -- so verticalSub is exact (no underflow).
    have hX_le : toNat trial ≤ toNat cur := by
      have hfc := findSqrtDigitHelper_correct (toNat cur) twoQ 9
      rw [← hx] at hfc
      rw [hP]; exact hfc
    have hsub : toNat newRem + toNat trial + carryVal false = toNat cur := by
      rw [hnewRem]
      exact verticalSub_correct cur trial false (by simpa [carryVal] using hX_le)
    -- Strip the carryVal false = 0 term
    have h0 : toNat newRem + toNat trial = toNat cur := by
      have h := hsub; simp only [carryVal] at h; omega
    -- Rewrite h0 into pure Nat form — the workhorse fact for what follows
    have e1 : toNat newRem + (2 * toNat q * 10 + x.val) * x.val
                = lo.val + hi.val * 10 + 100 * toNat acc := by
      have h := h0; rw [hP, hTQ, hC] at h; exact h
    -- Loop invariant: bound
    -- Show newRem ≤ 2·(x+10q) so the recursive call is valid.
    -- Key intermediate: cur ≤ trial + 2·(x+10q).
    -- Case split on x because x=9 has no "next candidate" to reject.
    have hrem_bound : toNat newRem ≤ 2 * toNat (x :: q) := by
      have hkey : toNat cur ≤ toNat trial + 2 * toNat (x :: q) := by
        rw [hxqv, hP, hTQ, hC]
        rcases Nat.lt_or_ge x.val 9 with hlt | hge
        · -- x < 9: candidate x+1 was tried and rejected by the search,
          -- so cur < (twoQ·10 + x+1)·(x+1).
          -- Expanding gives cur ≤ trial + 2·(x+10q).
          have hmax := findSqrtDigitHelper_maximal (toNat cur) twoQ 9 (by omega)
                        (x.val + 1) (by rw [← hx]; omega) (by omega)
          rw [hTQ, hC] at hmax
          nlinarith [hmax]
        · -- x = 9: no candidate 10 exists to reject, so use digit bounds
          -- lo < 10, hi < 10, acc ≤ 2q (hinv) to bound cur directly.
          have hx9 : x.val = 9 := by omega
          rw [hx9]
          nlinarith [hinv, lo.2, hi.2]
      omega
    --  Loop invariant: equation
    -- The bring-down identity: (x+10q)² + newRem = 100·(q²+acc) + (lo+hi·10)
    -- Proof: expand (x+10q)² = x² + 20qx + 100q²,
    --        note trial = (2q·10+x)·x = x² + 20qx,
    --        so (x+10q)² = trial + 100q².
    --        Then (x+10q)² + newRem = trial + newRem + 100q²
    --                               = cur + 100q²       (by h0)
    --                               = lo+hi·10+100·acc+100q² (by hC)
    --                               = 100·(q²+acc) + (lo+hi·10) ✓
    have hbring : toNat (x :: q) * toNat (x :: q) + toNat newRem
        = 100 * (toNat q * toNat q + toNat acc) + (lo.val + hi.val * 10) := by
      have e2 : toNat (x :: q) * toNat (x :: q)
          = x.val * x.val + 20 * (toNat q * x.val) + 100 * (toNat q * toNat q) := by
        rw [hxqv]; ring
      have e3 : (2 * toNat q * 10 + x.val) * x.val
          = 20 * (toNat q * x.val) + x.val * x.val := by ring
      rw [e2]; rw [e3] at e1; linarith
    --  Apply IH and assemble
    -- Instantiate the IH at (rest, newRem, x::q) with hrem_bound.
    -- The bound conjunct closes immediately via ih_le.
    -- For the equation: substitute ih_eq, hbring, pairsVal_cons,
    -- adjust the 100^k exponent, then ring finishes.
    obtain ⟨ih_eq, ih_le⟩ := ih newRem (x :: q) hrem_bound
    refine ⟨?_, ih_le⟩
    have hpv : pairsVal ((lo, hi) :: rest)
        = 100 ^ rest.length * (lo.val + hi.val * 10) + pairsVal rest := by
      simpa using pairsVal_cons (lo, hi) rest
    rw [ih_eq, hbring, hpv, List.length_cons, pow_succ]
    ring

-- Top-level correctness: the returned (q, r) satisfy q²+r = toNat a
-- and r ≤ 2q. Assembles the helper theorem, trim correctness,
-- and the pair-value bridge in three rewrites.
theorem intSqrt_correct (a : MultiDigit) :
    toNat (intSqrt a).1 * toNat (intSqrt a).1 + toNat (intSqrt a).2 = toNat a
    ∧ toNat (intSqrt a).2 ≤ 2 * toNat (intSqrt a).1 := by
  -- Unfold intSqrt to expose the sqrtHelper call
  simp only [intSqrt]
  -- Initial invariants are trivial: 0² + 0 = 0 and 0 ≤ 2·0
  obtain ⟨heq, hle⟩ :=
    sqrtHelper_correct (chunkPairs a).reverse [] [] (by simp [toNat])
  -- trimTrailingZeros preserves numeric value on both outputs
  rw [trimTrailingZeros_correct, trimTrailingZeros_correct]
  refine ⟨?_, hle⟩
  -- heq is in terms of pairsVal; rewrite to toNat a via pairsVal_chunkPairs
  rw [heq]; simp only [toNat, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  rw [pairsVal_chunkPairs]

-- The floor-sqrt characterization: q² ≤ a < (q+1)².
-- This is the mathematical statement that q = ⌊√a⌋ —
-- the unique integer whose square is ≤ a but whose successor's square exceeds a.
theorem intSqrt_is_floor (a : MultiDigit) :
    toNat (intSqrt a).1 * toNat (intSqrt a).1 ≤ toNat a
    ∧ toNat a < (toNat (intSqrt a).1 + 1) * (toNat (intSqrt a).1 + 1) := by
  obtain ⟨heq, hle⟩ := intSqrt_correct a
  exact ⟨
    by omega,           -- q² ≤ q²+r = a
    by nlinarith [heq, hle]  -- a = q²+r ≤ q²+2q < (q+1)²
  ⟩
