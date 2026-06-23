import Arithmetic_Formalization.Foundations
import Arithmetic_Formalization.Multiplication
import Mathlib.Tactic.IntervalCases
/-
  The Liam Delap cube root trick for perfect cubes up to 6 digits
  (cube roots 1–99).

  Two key observations make the trick work:

  1. The units digit of n³ uniquely determines the units digit of n.
     The mapping is a bijection — every digit 0–9 maps to a distinct
     cube units digit, so the reverse lookup is always unambiguous.

  2. The tens digit of the root comes from the thousands-and-above
     part of n³: find the largest d such that d³ ≤ (n³ / 1000).
     This works because (10a + b)³ = 1000a³ + (lower terms),
     so the thousands part is dominated by a³.

  Algorithm:
    cubeRootTrick n = (unitsDigit, tensDigit)
    where
      unitsDigit = cubeUnitsDigit (n % 10)
      tensDigit  = largest d s.t. d³ ≤ n / 1000
-/


-- The cube table: n³ for n = 0..9

def cubeTable : Digit → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 8
  | ⟨3, _⟩ => 27
  | ⟨4, _⟩ => 64
  | ⟨5, _⟩ => 125
  | ⟨6, _⟩ => 216
  | ⟨7, _⟩ => 343
  | ⟨8, _⟩ => 512
  | ⟨9, _⟩ => 729
  | ⟨n + 10, h⟩ => absurd h (by omega)

-- Correctness: cubeTable d = d³
theorem cubeTable_correct (d : Digit) :
    cubeTable d = d.val ^ 3 := by
  fin_cases d <;> simp [cubeTable]


-- Units digit lookup: given the units digit of a perfect cube,
-- return the units digit of the cube root.
-- The mapping is a bijection so the reverse is well-defined.
--
-- Cube units digits:
--   0³→0  1³→1  2³→8  3³→7  4³→4
--   5³→5  6³→6  7³→3  8³→2  9³→9


def cubeUnitsDigit : Digit → Digit
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨8, by omega⟩
  | ⟨3, _⟩ => ⟨7, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨3, by omega⟩
  | ⟨8, _⟩ => ⟨2, by omega⟩
  | ⟨9, _⟩ => ⟨9, by omega⟩
  | ⟨n + 10, h⟩ => absurd h (by omega)

-- Correctness: the units digit of (cubeUnitsDigit d)³ equals d
-- i.e. the lookup correctly inverts the units digit of a cube
theorem cubeUnitsDigit_correct (d : Digit) :
    (cubeUnitsDigit d).val ^ 3 % 10 = d.val := by
  fin_cases d <;> simp [cubeUnitsDigit]

-- Test cases
#eval cubeUnitsDigit ⟨8, by omega⟩  -- 157464 ends in 4, root ends in 4 → expect 4
#eval cubeUnitsDigit ⟨3, by omega⟩  -- cube ends in 3 → root ends in 7
#eval cubeUnitsDigit ⟨7, by omega⟩  -- cube ends in 7 → root ends in 3

-- Tens digit: largest d (0-9) such that d³ ≤ n / 1000
-- Downward search from 9, comparing d³ with n/1000

def findCubeTensHelper (upper : Nat) : Nat → Digit
  | 0 => ⟨0, by omega⟩
  | d + 1 =>
      if h : d + 1 < 10 then
        let dDigit : Digit := ⟨d + 1, h⟩
        -- Try d³ ≤ upper using cubeTable
        if cubeTable dDigit ≤ upper then
          dDigit
        else
          findCubeTensHelper upper d
      else
        ⟨0, by omega⟩

-- Correctness: the returned digit d satisfies d³ ≤ upper
theorem findCubeTensHelper_correct (upper : Nat) (k : Nat) :
    let d := findCubeTensHelper upper k
    cubeTable d ≤ upper := by
  induction k with
  | zero => simp [findCubeTensHelper, cubeTable]
  | succ k ih =>
    simp only [findCubeTensHelper]
    split
    · rename_i h
      split
      · rename_i h_le
        -- candidate d+1 satisfies the bound — return it
        exact h_le
      · -- candidate failed, recurse; IH closes it
        exact ih
    · -- d+1 ≥ 10: return 0, cubeTable 0 = 0 ≤ upper
      simp [cubeTable]

-- Maximality: any digit strictly larger than the result
-- has cube strictly greater than upper
theorem findCubeTensHelper_maximal (upper : Nat) :
    ∀ start, start < 10 → ∀ y, y < 10 →
      (findCubeTensHelper upper start).val < y → y ≤ start →
      upper < y ^ 3 := by
  intro start
  induction start with
  | zero =>
    -- res = 0, so y > 0 and y ≤ 0 contradict
    intro _ y _ hy hyle
    omega
  | succ k ih =>
    intro hstart y hy10 hy hyle
    simp only [findCubeTensHelper] at hy
    split at hy
    · rename_i h
      -- bridge cubeTable lookup to plain (k+1)³ for arithmetic
      have hcube : cubeTable ⟨k + 1, h⟩ = (k + 1) ^ 3 := cubeTable_correct ⟨k + 1, h⟩
      split at hy
      · -- inner if true: res = k+1, so y > k+1 contradicts y ≤ k+1
        have hval : (⟨k + 1, h⟩ : Digit).val = k + 1 := rfl
        omega
      · -- inner if false: (k+1)³ > upper, so any y ≥ k+1 also fails
        rename_i h_nle
        have h_nle' : upper < (k + 1) ^ 3 := by rw [← hcube]; omega
        rcases Nat.lt_or_ge y (k + 1) with hyk | hyk
        · -- y < k+1: not yet tried, recurse into IH
          exact ih (by omega) y hy10 hy (by omega)
        · -- y = k+1: exactly the candidate that just failed
          have hye : y = k + 1 := by omega
          subst hye; exact h_nle'
    · -- k+1 ≥ 10: impossible since start < 10
      rename_i h; omega


-- Top-level tens digit finder
def cubeTensDigit (n : MultiDigit) : Digit :=
  -- Divide by 1000 to get the thousands-and-above part,
  -- then find the largest d with d³ ≤ that value
  findCubeTensHelper (toNat n / 1000) 9


-- Main function: the cube root trick
-- Returns (units digit of root, tens digit of root)

-- We require
-- The units digit — the least significant digit.
-- This is just the head of the LSB-first list.
def unitsDigit (a : MultiDigit) : Nat :=
  match a with
  | []     => 0
  | d :: _ => d.val

def cubeRootTrick (n : MultiDigit) : Digit × Digit :=
  let u := match n with
    | []     => ⟨0, by omega⟩
    | d :: _ => cubeUnitsDigit d  -- d is already a Digit, pass directly
  let t := cubeTensDigit n
  (u, t)

-- Convenience: reconstruct root as a Nat
def cubeRootVal (n : MultiDigit) : Nat :=
  let (u, t) := cubeRootTrick n
  u.val + 10 * t.val

-- Test cases

-- 54³ = 157464
#eval cubeRootVal
  [⟨4,by omega⟩,⟨6,by omega⟩,⟨4,by omega⟩,
   ⟨7,by omega⟩,⟨5,by omega⟩,⟨1,by omega⟩]
-- expect 54

-- 99³ = 970299
#eval cubeRootVal
  [⟨9,by omega⟩,⟨9,by omega⟩,⟨2,by omega⟩,
   ⟨0,by omega⟩,⟨7,by omega⟩,⟨9,by omega⟩]
-- expect 99

-- 12³ = 1728
#eval cubeRootVal
  [⟨8,by omega⟩,⟨2,by omega⟩,⟨7,by omega⟩,⟨1,by omega⟩]
-- expect 12

-- 1³ = 1
#eval cubeRootVal [⟨1,by omega⟩]
-- expect 1

-- 10³ = 1000
#eval cubeRootVal
  [⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩,⟨1,by omega⟩]
-- expect 10

#eval cubeRootVal (fromNat (54 ^ 3))  -- expect 54
#eval cubeRootVal (fromNat (99 ^ 3))  -- expect 99
#eval cubeRootVal (fromNat (1 ^ 3))   -- expect 1
#eval cubeRootVal (fromNat (10 ^ 3))  -- expect 10

--Correctness of the algorithm
--One approach , since we have finite cases
--is to check wether the algorithm returns the correct value
--for perfect cubes upto 6 digits

theorem cubeRootTrick_correct1 (m : Nat) (hm : m ≤ 99) :
    cubeRootVal (fromNat (m ^ 3)) = m := by
  interval_cases m <;> native_decide

-- Verified by native evaluation over all 100 cases (m ≤ 99).
-- Uses native_decide (trusts the compiler) because fromNat is defined by
-- well-founded recursion and so doesn't reduce under the kernel's `decide`.

--the second approach is more involved

-- If a³ ≤ upper < (a+1)³ with a a digit, the search returns exactly a.
-- This is where findCubeTensHelper_correct (lower bound) and
-- findCubeTensHelper_maximal (upper bound) combine to pin the result.
theorem findCubeTensHelper_eq (upper a : Nat) (ha : a < 10)
    (hlo : a ^ 3 ≤ upper) (hhi : upper < (a + 1) ^ 3) :
    (findCubeTensHelper upper 9).val = a := by
  set r := (findCubeTensHelper upper 9).val with hr
  have hr9 : r < 10 := (findCubeTensHelper upper 9).2
  rcases Nat.lt_trichotomy r a with hlt | heq | hgt
  · -- r < a: maximality says a (a larger digit) fails, i.e. upper < a³,
    -- contradicting hlo : a³ ≤ upper.
    exfalso
    have hmax := findCubeTensHelper_maximal upper 9 (by omega) a ha
                   (by rw [← hr]; exact hlt) (by omega)
    omega
  · exact heq
  · -- r > a: correctness says r³ ≤ upper, but r ≥ a+1 ⇒ r³ ≥ (a+1)³ > upper.
    exfalso
    have hcorr : cubeTable (findCubeTensHelper upper 9) ≤ upper :=
      findCubeTensHelper_correct upper 9
    rw [cubeTable_correct] at hcorr
    rw [← hr] at hcorr          -- fold (findCubeTensHelper upper 9).val → r
    -- hcorr : r ^ 3 ≤ upper
    have hmono : (a + 1) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega

-- For m ≤ 99, the tens-digit search on m³/1000 returns m/10.
theorem cubeTensDigit_eq (m : Nat) (hm : m ≤ 99) :
    (findCubeTensHelper (m ^ 3 / 1000) 9).val = m / 10 := by
  set a := m / 10 with ha_def
  have ha10 : a < 10 := by omega
  refine findCubeTensHelper_eq (m ^ 3 / 1000) a ha10 ?_ ?_
  · -- Lower bound:
    -- a³ ≤ m³ / 1000
    have hmab : 10 * a ≤ m := by omega
    have hle : (10 * a) ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hmab 3
    have hexp : (10 * a) ^ 3 = 1000 * a ^ 3 := by ring
    rw [hexp] at hle
    -- hle : 1000 * a ^ 3 ≤ m ^ 3
    omega
  · -- Upper bound:
    -- ⇒ m^3 / 1000 < (a+1)^3
    have hmlt : m < 10 * (a + 1) := by omega
    have hlt : m ^ 3 < (10 * (a + 1)) ^ 3 := Nat.pow_lt_pow_left hmlt (by omega)
    have hexp : (10 * (a + 1)) ^ 3 = 1000 * (a + 1) ^ 3 := by ring
    rw [hexp] at hlt
    -- hlt : m ^ 3 < 1000 * (a + 1) ^ 3
    omega

-- The units lookup inverts the cube's units digit: feeding cubeUnitsDigit
-- the units digit of m³ recovers m % 10. Depends only on m % 10, so it's a
-- finite 10-case check after reducing via Nat.pow_mod.
theorem cubeUnitsDigit_inverts (m : Nat) :
    (cubeUnitsDigit ⟨m ^ 3 % 10, Nat.mod_lt _ (by omega)⟩).val = m % 10 := by
  have hpow : m ^ 3 % 10 = (m % 10) ^ 3 % 10 := by rw [Nat.pow_mod]
  have hlt : m % 10 < 10 := Nat.mod_lt _ (by omega)
  -- the Digit fed to cubeUnitsDigit depends only on m % 10; enumerate it
  interval_cases h : (m % 10) <;> simp_all [cubeUnitsDigit]

--helper lemmas
--for any positive n, the first digit of fromNat n is n % 10
theorem fromNat_head_pos (n : Nat) (hn : 0 < n) :
    fromNat n = ⟨n % 10, by omega⟩ :: fromNat (n / 10) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [fromNat]

--Main theorem variant2
-- for 0 < m ≤ 99, the trick recovers m exactly.
-- Two independent facts combine: the units lookup inverts m³'s last digit
-- (cubeUnitsDigit_inverts), and the tens search recovers m/10 from m³/1000
-- (cubeTensDigit_eq). Their values are m%10 and m/10, which sum to m.
theorem cubeRootTrick_correct2 (m : Nat) (hm : m ≤ 99) (hm0 : 0 < m) :
    cubeRootVal (fromNat (m ^ 3)) = m := by
  -- Tens digit = m/10. Established up front so it's a clean rewrite later:
  -- cubeTensDigit runs the search on toNat(fromNat m³)/1000 = m³/1000.
  have htens : (cubeTensDigit (fromNat (m ^ 3))).val = m / 10 := by
    unfold cubeTensDigit; rw [toNat_fromNat]; exact cubeTensDigit_eq m hm
  unfold cubeRootVal cubeRootTrick
  -- Expose m³'s head digit ⟨m³%10,_⟩ so the units `match … | d :: _` reduces.
  rw [fromNat_head_pos (m ^ 3) (by positivity)]
  simp only []
  -- Units digit = m%10 (cube-units lookup is a bijection).
  rw [cubeUnitsDigit_inverts m]
  -- Discharge the tens digit with htens, then m%10 + 10*(m/10) = m.
  rw [← fromNat_head_pos (m ^ 3) (by positivity), htens]
  omega
