import Arithmetic_Formalization.Foundations
import Arithmetic_Formalization.Subtraction
import Arithmetic_Formalization.Multiplication
import Arithmetic_Formalization.Division
import Mathlib.Data.Nat.ModEq

-- All of the common divisibility tests rely fundamentally on modular arithmetic
-- Modular arithmetic studies remainders after division.
-- For example:
--   10 = 3 * 3 + 1
-- so 10 leaves remainder 1 when divided by 3.
-- Mathematicians write:
--   10 ≡ 1 (mod 3)
-- meaning that 10 and 1 have the same remainder upon division by 3.
-- Two useful facts are:
--   (a + b) mod m = ((a mod m) + (b mod m)) mod m
--   (a * b) mod m = ((a mod m) * (b mod m)) mod m
-- These allow us to reason about divisibility digit-by-digit.


-- The modulo operator, built on top of our own longDiv.
-- myMod a b returns the remainder when the MultiDigit number a
-- is divided by the single digit b — using the same long division
-- algorithm we formalized and proved correct earlier.


def myMod (a : MultiDigit) (b : Digit) : Nat :=
  (longDiv a b).2

-- Test cases
#eval myMod [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨3,by omega⟩
-- 1234 % 3 = 1  (1234 = 411×3 + 1)

#eval myMod [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨9,by omega⟩
-- 1234 % 9 = 1  (digit sum = 10, 10 % 9 = 1)

#eval myMod [⟨0,by omega⟩,⟨0,by omega⟩,⟨1,by omega⟩] ⟨3,by omega⟩
-- 100 % 3 = 1

#eval myMod [⟨8,by omega⟩,⟨9,by omega⟩] ⟨9,by omega⟩
-- 98 % 9 = 8  (digit sum = 17, 17 % 9 = 8)

#eval myMod [] ⟨7,by omega⟩
-- 0 % 7 = 0


-- Bridge theorem: myMod agrees with Lean's native Nat.mod.
-- This is the key lemma that allows us to use some basic Mathlib theorems
-- Every divisibility proof below is stated in terms of myMod
-- and proved by rewriting through this bridge.


theorem myMod_eq_natMod (a : MultiDigit) (b : Digit) (hb : b.val ≠ 0) :
    myMod a b = toNat a % b.val := by
  unfold myMod
  simp only [longDiv]
  cases h_rec : longDivHelper a.reverse b 0 with
  | mk q r =>
  simp only []
  have h := longDivHelper_correct a.reverse b hb 0 (by omega)
  rw [h_rec] at h
  simp only at h
  obtain ⟨heq, hlt⟩ := h
  simp only [Nat.zero_mul, Nat.zero_add, List.reverse_reverse] at heq
  symm
  calc toNat a % b.val
      = (toNat q.reverse * b.val + r) % b.val := by rw [← heq]
    _ = r % b.val := by simp [Nat.add_mod]
    _ = r          := Nat.mod_eq_of_lt hlt


-- The two modular arithmetic laws, stated for Nat.
-- Proved by rewriting to Lean's native modular arithmetic —
-- Nat.add_mod and Nat.mul_mod are already in the standard library.
-- These two laws are all we need to prove every divisibility test below.

--The two modular arithmetic laws
-- I simply present the main proof idea as they are already proved in Lean's core library as
-- Nat.add_mod and Nat.mul_mod, so we simply note them here
-- rather than reproving them from scratch.

-- Law 1: addition distributes over mod.
-- (a + b) % m = ((a % m) + (b % m)) % m
-- Proof idea: write a = q₁·m + r₁ and b = q₂·m + r₂.
-- Then a+b = (q₁+q₂)·m + (r₁+r₂),
-- so (a+b) % m = (r₁+r₂) % m = ((a%m)+(b%m)) % m ✓
#check Nat.add_mod


-- Law 2: multiplication distributes over mod.
-- (a * b) % m = ((a % m) * (b % m)) % m
-- Proof idea: write a = q₁·m + r₁ and b = q₂·m + r₂.
-- Then a·b = (q₁·q₂·m + q₁·r₂ + q₂·r₁)·m + r₁·r₂,
-- so (a·b) % m = (r₁·r₂) % m = ((a%m)·(b%m)) % m

#check Nat.mul_mod

--Now lets us move onto the divisibility tests

-- We require
-- The units digit — the least significant digit.
-- This is just the head of the LSB-first list.
def unitsDigit (a : MultiDigit) : Nat :=
  match a with
  | []     => 0
  | d :: _ => d.val
-- sum of all digits
def digitSum (a : MultiDigit) : Nat :=
  a.foldl (fun acc d => acc + d.val) 0

--For 2 & 5
-- Keyfacts
-- 10 ≡ 0 (mod 2): every power of 10 above 10^0 is divisible by 2
theorem ten_mod_2 : 10 % 2 = 0 := by decide
-- 10 ≡ 0 (mod 5): every power of 10 above 10^0 is divisible by 5
theorem ten_mod_5 : 10 % 5 = 0 := by decide
-- 10 ≡ 1 (mod 9): every power of 10 is congruent to 1 mod 9
theorem ten_mod_9 : 10 % 9 = 1 := by decide
-- 10 ≡ 1 (mod 3): same reason as mod 9 (9 divides 10-1=9)
theorem ten_mod_3 : 10 % 3 = 1 := by decide

theorem div_by_2 (a : MultiDigit) :
    2 ∣ toNat a ↔ 2 ∣ unitsDigit a := by
  induction a with
  | nil =>
    -- toNat [] = 0 = unitsDigit []; 2 | 0 ↔ 2 | 0 ✓
    simp [toNat, unitsDigit]
  | cons d ds _ =>
    rw [toNat_cons, unitsDigit]
    -- 2 | 10*toNat ds always holds since 10 = 2×5
    -- so the tail contributes nothing to divisibility by 2
    have h10 : 2 ∣ 10 * toNat ds := ⟨5 * toNat ds, by ring⟩
    constructor
    · intro h
      -- 2 | d + 10*ds and 2 | 10*ds → 2 | d
      have h' : 2 ∣ 10 * toNat ds + d.val := by rwa [Nat.add_comm] at h
      exact (Nat.dvd_add_right h10).mp h'
    · intro h
      -- 2 | d and 2 | 10*ds → 2 | d + 10*ds
      exact Nat.dvd_add h h10

--connect with myMod
theorem myMod_div_by_2 (a : MultiDigit) :
    myMod a ⟨2, by decide⟩ = 0 ↔ 2 ∣ unitsDigit a := by
  rw [myMod_eq_natMod a ⟨2, by decide⟩ (by decide)]
  rw [← Nat.dvd_iff_mod_eq_zero]
  exact div_by_2 a

--Similarly for 5
theorem div_by_5 (a : MultiDigit) :
    5 ∣ toNat a ↔ 5 ∣ unitsDigit a := by
  induction a with
  | nil =>
    simp [toNat, unitsDigit]
  | cons d ds _ =>
    rw [toNat_cons, unitsDigit]
    have h10 : 5 ∣ 10 * toNat ds := ⟨2 * toNat ds, by ring⟩
    constructor
    · intro h
      have h' : 5 ∣ 10 * toNat ds + d.val := by rwa [Nat.add_comm] at h
      exact (Nat.dvd_add_right h10).mp h'
    · intro h
      exact Nat.dvd_add h h10

theorem myMod_div_by_5 (a : MultiDigit) :
    myMod a ⟨5, by decide⟩ = 0 ↔ 5 ∣ unitsDigit a := by
  rw [myMod_eq_natMod a ⟨5, by decide⟩ (by decide)]
  rw [← Nat.dvd_iff_mod_eq_zero]
  exact div_by_5 a

--For 3
--We shall first prove a stronger result
--The digit sum of a number has is congruent to the number itself mod 3

--Helper lemma
-- A foldl with a non-zero starting accumulator n
-- equals n plus the result of folding from zero (digitSum).
-- This lets us rewrite foldl expressions that arise when
-- simp unfolds digitSum on a cons cell.
theorem digitSum_foldl (ds : MultiDigit) (n : Nat) :
    ds.foldl (fun acc d => acc + d.val) n = n + digitSum ds := by
  unfold digitSum
  induction ds generalizing n with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons]
    -- IH at two different inits; omega closes the linear arithmetic
    rw [ih (n + d.val), ih (0 + d.val)]
    omega

-- digitSum on an empty list is 0
theorem digitSum_nil : digitSum [] = 0 := by
  simp [digitSum]

-- digitSum on a cons cell equals the head digit plus the tail's digit sum.
-- Proved by unfolding one foldl step and applying digitSum_foldl
-- to handle the non-zero accumulator that appears.
theorem digitSum_cons (d : Digit) (ds : MultiDigit) :
    digitSum (d :: ds) = d.val + digitSum ds := by
  unfold digitSum
  simp only [List.foldl_cons]
  rw [digitSum_foldl ds (0 + d.val)]
  unfold digitSum
  omega

-- The key congruence fact underlying divisibility by 3:
-- toNat a and digitSum a have the same remainder mod 3.
-- Proof: 10 ≡ 1 (mod 3), so each digit d_i * 10^i ≡ d_i (mod 3),
-- and the sum of all digits mod 3 equals toNat a mod 3.
theorem toNat_mod3_eq_digitSum_mod3 (a : MultiDigit) :
    toNat a % 3 = digitSum a % 3 := by
  induction a with
  | nil => simp [toNat, digitSum]
  | cons d ds ih =>
    rw [toNat_cons, digitSum_cons]
    -- Write 10 = 1 + 9 so that 9*toNat ds vanishes mod 3
    have hten : 10 * toNat ds = toNat ds + 9 * toNat ds := by ring
    rw [hten]
    -- Rearrange so the 9*toNat ds term is isolated at the end
    rw [show d.val + (toNat ds + 9 * toNat ds)
            = (d.val + toNat ds) + 9 * toNat ds by ring]
    -- 9*toNat ds ≡ 0 (mod 3) since 3 | 9
    have h9 : (9 * toNat ds) % 3 = 0 := by simp [Nat.mul_mod]
    -- Strip the vanishing term, then substitute the IH
    rw [Nat.add_mod, h9, Nat.add_zero, Nat.mod_mod]
    rw [Nat.add_mod d.val (toNat ds), ih,
        ← Nat.add_mod d.val (digitSum ds)]

-- A number is divisible by 3 if and only if its digit sum is divisible by 3.
-- Proof: rewrite both sides using the congruence theorem above —
-- 3 | toNat a ↔ toNat a % 3 = 0 ↔ digitSum a % 3 = 0 ↔ 3 | digitSum a
theorem div_by_3 (a : MultiDigit) :
    3 ∣ toNat a ↔ 3 ∣ digitSum a := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
      toNat_mod3_eq_digitSum_mod3]

theorem myMod_div_by_3 (a : MultiDigit) :
    myMod a ⟨3, by decide⟩ = 0 ↔ 3 ∣ digitSum a := by
  rw [myMod_eq_natMod a ⟨3, by decide⟩ (by decide)]
  rw [← Nat.dvd_iff_mod_eq_zero]
  exact div_by_3 a

--Similarly for 9
theorem toNat_mod9_eq_digitSum_mod9 (a : MultiDigit) :
    toNat a % 9 = digitSum a % 9 := by
  induction a with
  | nil => simp [toNat, digitSum]
  | cons d ds ih =>
    rw [toNat_cons, digitSum_cons]
    have hten : 10 * toNat ds = toNat ds + 9 * toNat ds := by ring
    rw [hten]
    rw [show d.val + (toNat ds + 9 * toNat ds)
            = (d.val + toNat ds) + 9 * toNat ds by ring]
    have h9 : (9 * toNat ds) % 9 = 0 := by simp []
    rw [Nat.add_mod, h9, Nat.add_zero, Nat.mod_mod]
    rw [Nat.add_mod d.val (toNat ds), ih,
        ← Nat.add_mod d.val (digitSum ds)]

theorem div_by_9 (a : MultiDigit) :
    9 ∣ toNat a ↔ 9 ∣ digitSum a := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
      toNat_mod9_eq_digitSum_mod9]

theorem myMod_div_by_9 (a : MultiDigit) :
    myMod a ⟨9, by decide⟩ = 0 ↔ 9 ∣ digitSum a := by
  rw [myMod_eq_natMod a ⟨9, by decide⟩ (by decide)]
  rw [← Nat.dvd_iff_mod_eq_zero]
  exact div_by_9 a

--For 11
--To avoid differences we shall compute both odd sum and even sum
--Then compare their remainder mod 11

-- (evenPositionSum, oddPositionSum), positions 0-indexed from the LSB.
-- Prepending a digit shifts every existing position up by one, which
-- swaps even ↔ odd — hence the components swap in the recursive step.
def altSums : MultiDigit → Nat × Nat
  | []      => (0, 0)
  | d :: ds => (d.val + (altSums ds).2, (altSums ds).1)

-- Unfolding altSums on a cons cell: the new head digit lands in the
-- even-position sum (it sits at position 0), and the tail's even/odd sums
-- swap roles (every previous position shifts up by one). Holds definitionally,
-- so `rfl` closes it — the analogue of digitSum_cons for the 11 test.
theorem altSums_cons (d : Digit) (ds : MultiDigit) :
    altSums (d :: ds) = (d.val + (altSums ds).2, (altSums ds).1) := rfl

-- toNat a ≡ E − O (mod 11), stated subtraction-free as toNat a + O ≡ E.
-- Each step uses 10 ≡ −1 (mod 11): the 10·tail term combines with the tail
-- (supplied by the IH) into 11·tail, which vanishes mod 11.
theorem toNat_mod11_eq_altSum (a : MultiDigit) :
    (toNat a + (altSums a).2) % 11 = (altSums a).1 % 11 := by
  induction a with
  | nil =>
    -- Base case: the empty number is 0 and altSums [] = (0, 0),
    -- so both sides reduce to 0 % 11.
    simp [toNat, altSums]
  | cons d ds ih =>
    -- Expose the head digit d and the tail's even/odd sums (now swapped).
    rw [toNat_cons, altSums_cons]
    -- ih : (toNat ds + (altSums ds).2) % 11 = (altSums ds).1 % 11
    -- 11·tail is a multiple of 11, so it vanishes in any mod-11 comparison.
    have h11 : (11 * toNat ds) ≡ 0 [MOD 11] :=
      (Nat.modEq_zero_iff_dvd).mpr ⟨toNat ds, rfl⟩
    -- Restate the inductive hypothesis as a ModEq so it chains inside the calc.
    have ihm : (altSums ds).1 ≡ (toNat ds + (altSums ds).2) [MOD 11] := ih.symm
    -- Cons step: d is now an even-position digit. Using 10 ≡ −1 (mod 11),
    -- the 10·tail term and the tail's own value (supplied by ih) merge into
    -- 11·tail, which drops out — leaving exactly the new (even, odd) split.
    have goal : (d.val + 10 * toNat ds + (altSums ds).1)
                  ≡ (d.val + (altSums ds).2) [MOD 11] :=
      calc (d.val + 10 * toNat ds + (altSums ds).1)
          -- substitute the tail's odd-sum for its value via the IH
          ≡ (d.val + 10 * toNat ds + (toNat ds + (altSums ds).2)) [MOD 11] :=
            Nat.ModEq.add_left _ ihm
        -- regroup: 10·tail + tail = 11·tail
        _ = ((d.val + (altSums ds).2) + 11 * toNat ds) := by ring
        -- discard the 11·tail term, since 11·tail ≡ 0 (mod 11)
        _ ≡ ((d.val + (altSums ds).2) + 0) [MOD 11] := Nat.ModEq.add_left _ h11
        _ = (d.val + (altSums ds).2) := by ring
    exact goal

-- A number is divisible by 11 iff its even-position and odd-position digit
-- sums are congruent mod 11 — the classic alternating-sum test, stated here
-- subtraction-free as E ≡ O (mod 11). Both directions fall out of the
-- congruence toNat a + O ≡ E (mod 11) proved above, by cancelling the shared O.
theorem div_by_11 (a : MultiDigit) :
    11 ∣ toNat a ↔ (altSums a).1 % 11 = (altSums a).2 % 11 := by
  -- Reduce 11 ∣ toNat a to toNat a % 11 = 0.
  rw [Nat.dvd_iff_mod_eq_zero]
  -- key : (toNat a + O) % 11 = E % 11
  have key := toNat_mod11_eq_altSum a
  constructor
  · intro hN
    -- (→) toNat a ≡ 0, so adding O leaves just O on the left;
    -- rewriting by key turns that into E % 11 = O % 11.
    have h : (toNat a + (altSums a).2) % 11 = (altSums a).2 % 11 := by
      rw [Nat.add_mod, hN, Nat.zero_add, Nat.mod_mod]
    rw [key] at h; exact h
  · intro hEO
    -- (←) given E ≡ O, substitute into key to get toNat a + O ≡ O,
    rw [hEO] at key
    have h : (toNat a + (altSums a).2) ≡ (0 + (altSums a).2) [MOD 11] := by
      rw [Nat.zero_add]; exact key
    -- then cancel the common +O from both sides to recover toNat a ≡ 0.
    have := Nat.ModEq.add_right_cancel' (altSums a).2 h
    simpa using this
