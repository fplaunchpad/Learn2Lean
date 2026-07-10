import Arithmetic_Formalization.Addition
import Arithmetic_Formalization.Subtraction
import Arithmetic_Formalization.Multiplication
import Arithmetic_Formalization.Division
import Arithmetic_Formalization.Divisibility
import Arithmetic_Formalization.EuclidGCDAlgo
import Arithmetic_Formalization.CuberootTrick
import Arithmetic_Formalization.Squareroot

/-!
  Reference fills for the web exercises (so we know the scaffolds compile).
  The Flask checker uses these same scaffolds with `__CODE__` replaced by the
  student's input. Here the gaps are filled with the intended answers.
-/

-- Exercise A — the student fills the `[], b :: bs, c =>` case (top number empty,
-- bottom has digits), mirroring the `a :: as, []` case shown.
def studentAdd : MultiDigit → MultiDigit → Bool → MultiDigit
  | [], [], false => []
  | [], [], true  => [⟨1, by omega⟩]
  | [], b :: bs, c => let (d, c') := addDigits ⟨0, by omega⟩ b c; d :: studentAdd [] bs c'   -- __CODE__
  | a :: as, [], c => let (d, c') := addDigits a ⟨0, by omega⟩ c; d :: studentAdd as [] c'
  | a :: as, b :: bs, c => let (d, c') := addDigits a b c; d :: studentAdd as bs c'
termination_by a b _ => a.length + b.length

-- automatic checks the Flask route runs (concrete cases, compiled with native_decide)
example :
    toNat (studentAdd [] [⟨5,by omega⟩,⟨2,by omega⟩] false) = 25
  ∧ toNat (studentAdd [] [⟨9,by omega⟩] true) = 10
  ∧ toNat (studentAdd [⟨3,by omega⟩] [⟨4,by omega⟩,⟨5,by omega⟩] false) = 57 := by native_decide

-- Exercise B — the student fills the one-line proof.
theorem add_correct_nocarry (a b : MultiDigit) :
    toNat (verticalAdd a b false) = toNat a + toNat b := by
  simpa using verticalAdd_correct a b false   -- __CODE__

-- Exercise C — prove a concrete column evaluation. 9 + 9 with carry-in 1 gives
-- digit 9 and a carry-out. The whole thing is decidable, so `decide` settles it.
example : addDigits ⟨9, by omega⟩ ⟨9, by omega⟩ true = (⟨9, by omega⟩, true) := by
  decide   -- __CODE__

-- Exercise D — adding zero to a digit, no incoming carry, returns it unchanged;
-- proved by exhausting the ten digits (mirrors the subtraction fin_cases drill).
theorem add_zero_no_carry (a : Digit) :
    addDigits a ⟨0, by omega⟩ false = (a, false) := by
  fin_cases a <;> simp [addDigits, addTable]   -- __CODE__

-- Exercise E — write the WHOLE proof (no scaffold, just the statement): the
-- single-digit addition table is symmetric. Both digits range over 0–9, so split
-- each into cases and decide every combination.
theorem addTable_comm (a b : Digit) : addTable a b = addTable b a := by
  fin_cases a <;> fin_cases b <;> decide   -- __CODE__


/-! ===================== SUBTRACTION ===================== -/

-- Exercise S-A — the student fills the `a :: as, [], borrow` case (bottom number
-- empty, top still has digits), mirroring the main `a :: as, b :: bs` case shown.
def studentSub : MultiDigit → MultiDigit → Bool → MultiDigit
  | [], [], _ => []
  | [], _ :: _, _ => []
  | a :: as, [], borrow => let (d, b') := subDigits a ⟨0, by omega⟩ borrow; d :: studentSub as [] b'   -- __CODE__
  | a :: as, b :: bs, borrow => let (d, b') := subDigits a b borrow; d :: studentSub as bs b'
termination_by a b _ => a.length + b.length

example :
    toNat (studentSub [⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] [⟨1,by omega⟩,⟨9,by omega⟩] false) = 32
  ∧ toNat (studentSub [⟨0,by omega⟩,⟨0,by omega⟩,⟨1,by omega⟩] [⟨1,by omega⟩] false) = 99
  ∧ toNat (studentSub [⟨5,by omega⟩,⟨7,by omega⟩] [] false) = 75 := by native_decide

-- Exercise S-B — prove a concrete column evaluation. 3 − 7 borrows: difference 6
-- with a borrow-out. Decidable, so `decide` settles it.
example : subDigits ⟨3, by omega⟩ ⟨7, by omega⟩ false = (⟨6, by omega⟩, true) := by
  decide   -- __CODE__

-- Exercise S-C — prove the no-borrow corollary. The general theorem
-- verticalSub_correct, specialised to borrow = false; the precondition h carries
-- over once the `+ carryVal false` is simplified away.
theorem sub_correct_noborrow (a b : MultiDigit) (h : toNat b ≤ toNat a) :
    toNat (verticalSub a b false) + toNat b = toNat a := by
  simpa using verticalSub_correct a b false (by simpa using h)   -- __CODE__

-- Exercise S-D — prove, by exhausting the ten digits, that subtracting a digit
-- from itself with no incoming borrow gives (0, false). The student supplies the
-- combinator + simp after fin_cases.
theorem self_sub_no_borrow (a : Digit) :
    subDigits a a false = (⟨0, by omega⟩, false) := by
  fin_cases a <;> simp [subDigits, subTable]   -- __CODE__


/-! ===================== MULTIPLICATION ===================== -/

-- Exercise M-A — fill the case where the digits run out but a carry remains:
-- the leftover carry becomes the final, most-significant digit.
def studentMulDigit : MultiDigit → Digit → Digit → MultiDigit
  | [], _, ⟨0, _⟩ => []
  | [], _, carry => [carry]   -- __CODE__
  | d :: ds, b, carry =>
      let (units, tens) := mulTable d b
      let (units', carry') := addTable units carry
      let carryDigit : Digit := if carry' then ⟨1, by omega⟩ else ⟨0, by omega⟩
      let (finalCarry, _) := addTable tens carryDigit
      units' :: studentMulDigit ds b finalCarry
termination_by a _ _ => a.length

example :
    toNat (studentMulDigit [⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨7,by omega⟩ ⟨0,by omega⟩) = 861
  ∧ toNat (studentMulDigit [⟨9,by omega⟩,⟨9,by omega⟩] ⟨9,by omega⟩ ⟨0,by omega⟩) = 891 := by native_decide

-- Exercise M-B — concrete table lookup: 3 × 7 = 21 → units 1, tens 2.
example : mulTable ⟨3, by omega⟩ ⟨7, by omega⟩ = (⟨1, by omega⟩, ⟨2, by omega⟩) := by
  decide   -- __CODE__

-- Exercise M-C — by exhaustion: multiplying any digit by 0 gives (0, 0).
theorem mul_by_zero (a : Digit) :
    mulTable a ⟨0, by omega⟩ = (⟨0, by omega⟩, ⟨0, by omega⟩) := by
  fin_cases a <;> rfl   -- __CODE__

-- Exercise M-D — apply the main theorem: anything × 0 (the empty list) is 0.
theorem mul_empty (a : MultiDigit) :
    toNat (verticalMulPP a []) = 0 := by
  simpa using verticalMulPP_correct a []   -- __CODE__

-- Exercise M-E — one shift is one factor of ten: rewrite with the proved lemma,
-- then close the pure-algebra rearrangement (10^1 vs 10·) with ring.
example (a : MultiDigit) : toNat (shiftLeft a 1) = 10 * toNat a := by
  rw [shiftLeft_correct]; ring   -- __CODE__


/-! ===================== DIVISION ===================== -/

-- Exercise V-A — trimTrailingZeros: when the trimmed tail is nonempty, keep the
-- current digit in front of it.
def studentTrim : MultiDigit → MultiDigit
  | [] => []
  | d :: ds =>
      match studentTrim ds with
      | [] => if d.val == 0 then [] else [d]
      | ts => d :: ts   -- __CODE__

example :
    toNat (studentTrim [⟨4,by omega⟩,⟨3,by omega⟩,⟨0,by omega⟩]) = 34
  ∧ (studentTrim [⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩]).length = 0 := by native_decide

-- Exercise V-B — the trial digit: the largest q ≤ 9 with q × 5 ≤ 23 is 4.
example : findQuotientDigit 23 ⟨5, by omega⟩ = ⟨4, by omega⟩ := by native_decide   -- __CODE__

-- Exercise V-E — the invariant-survival bound, stripped to its arithmetic:
-- the trial-digit bracket alone forces the new remainder below b.
-- ((q+1)·b is written expanded, q·b + b, so the arithmetic stays linear.)
example (v b q : Nat) (h1 : q * b ≤ v) (h2 : v < q * b + b) : v - q * b < b := by
  omega   -- __CODE__

-- Exercise V-C — the whole algorithm: 1234 ÷ 5 = 246 remainder 4.
example :
    (longDiv [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨5,by omega⟩).2 = 4
  ∧ toNat (longDiv [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨5,by omega⟩).1 = 246 := by native_decide

-- Exercise V-D — cite the proved lemma: trimming the quotient never changes its value.
example (a : MultiDigit) : toNat (trimTrailingZeros a) = toNat a := by
  exact trimTrailingZeros_correct a   -- __CODE__


/-! ===================== DIVISIBILITY ===================== -/

-- Exercise B-A — digitSum: the fold adds each digit's value to the accumulator.
def studentDigitSum (a : MultiDigit) : Nat :=
  a.foldl (fun acc d => acc + d.val) 0   -- __CODE__ is `acc + d.val`

example :
    studentDigitSum [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] = 10
  ∧ studentDigitSum [] = 0 := by native_decide

-- Exercise B-B — 1234 mod 9 = 1 (its digit sum is 10, and 10 mod 9 = 1).
example : myMod [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨9, by omega⟩ = 1 := by
  native_decide   -- __CODE__

-- Exercise B-C — the (even-position, odd-position) sums of 1234 are (6, 4).
example : altSums [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] = (6, 4) := by
  decide   -- __CODE__

-- Exercise B-D — cite the proved test: divisible by 9 iff the digit sum is.
example (a : MultiDigit) : 9 ∣ toNat a ↔ 9 ∣ digitSum a := by
  exact div_by_9 a   -- __CODE__

-- Exercise B-E — the ÷3 test from its congruence, by rewriting: turn both
-- divisibilities into mod-equations, then substitute the congruence theorem.
example (a : MultiDigit) : 3 ∣ toNat a ↔ 3 ∣ digitSum a := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
      toNat_mod3_eq_digitSum_mod3]   -- __CODE__


/-! ===================== EUCLID'S GCD ===================== -/

-- Exercise G-A — run the algorithm: gcd(48, 36) = 12 (§1's worked example).
example : toNat (gcdSub [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩]) = 12 := by
  native_decide   -- __CODE__

-- Exercise G-B — the termination argument, stripped to its arithmetic: a positive
-- amount that fits inside x, once subtracted, strictly shrinks the sum.
example (x y : Nat) (h1 : 0 < y) (h2 : y ≤ x) : (x - y) + y < x + y := by
  omega   -- __CODE__

-- Exercise G-C — fill the carving branch of studentGcd (a copy of gcdSub):
-- subtract the smaller side from the larger and recurse on the smaller rectangle.
def studentGcd (a b : MultiDigit) : MultiDigit :=
  if toNat a = 0 then b
  else if toNat b = 0 then a
  else if toNat a = toNat b then a
  else if toNat b < toNat a then
    studentGcd (verticalSub a b false) b   -- __CODE__
  else
    studentGcd a (verticalSub b a false)
termination_by toNat a + toNat b
decreasing_by
  · have hle : toNat b ≤ toNat a := by omega
    have hsub : toNat (verticalSub a b false) + toNat b = toNat a :=
      verticalSub_correct' a b hle
    omega
  · have hle : toNat a ≤ toNat b := by omega
    have hsub : toNat (verticalSub b a false) + toNat a = toNat b :=
      verticalSub_correct' b a hle
    omega

example : toNat (studentGcd [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩]) = 12 := by
  native_decide

-- Exercise G-D — harvest the tiling theorem: the gcd divides the first side.
-- The statement is ((∣ a ∧ ∣ b) ∧ maximality); project out the first half's first part.
example (a b : MultiDigit) : toNat (gcdSub a b) ∣ toNat a := by
  exact (gcdSub_tiles a b).1.1   -- __CODE__

-- Exercise G-E — gcd is symmetric: rewrite through gcdSub_correct, then cite Nat.gcd_comm.
example (a b : MultiDigit) : toNat (gcdSub a b) = toNat (gcdSub b a) := by
  rw [gcdSub_correct, gcdSub_correct]
  exact Nat.gcd_comm (toNat a) (toNat b)   -- __CODE__


/-! ===================== CUBE-ROOT TRICK ===================== -/

-- Exercise C-A — read a cube backwards: a cube ending in 3 has a root ending in 7.
example : cubeUnitsDigit ⟨3, by omega⟩ = ⟨7, by omega⟩ := by
  decide   -- __CODE__

-- Exercise C-B — run the whole trick: it recovers 54 from 54³ = 157464.
example : cubeRootVal (fromNat (54 ^ 3)) = 54 := by
  native_decide   -- __CODE__

-- Exercise C-C — the units lookup really inverts a cube's last digit, for every digit.
example (d : Digit) : (cubeUnitsDigit d).val ^ 3 % 10 = d.val := by
  fin_cases d <;> simp [cubeUnitsDigit]   -- __CODE__

-- Exercise C-D — cite the finished (brute-force) theorem for all of 1–99.
example (m : Nat) (hm : m ≤ 99) : cubeRootVal (fromNat (m ^ 3)) = m := by
  exact cubeRootTrick_correct1 m hm   -- __CODE__

-- Exercise C-E — the tens search on its own: largest d with d³ ≤ 157 is 5.
example : findCubeTensHelper 157 9 = ⟨5, by omega⟩ := by
  decide   -- __CODE__


/-! ===================== SQUARE ROOTS ===================== -/

-- Exercise Q-A — the first root digit: with no root yet, largest x with x² ≤ 12 is 3.
example : findSqrtDigit 12 [] = ⟨3, by omega⟩ := by
  native_decide   -- __CODE__

-- Exercise Q-B — the shifting-divisor step: with q = [3], largest x with (60+x)·x ≤ 334 is 5.
example : findSqrtDigit 334 [⟨3, by omega⟩] = ⟨5, by omega⟩ := by
  native_decide   -- __CODE__

-- Exercise Q-C — the identity behind "double the root, append the digit".
example (q x : Nat) : (10 * q + x) ^ 2 = (2 * q * 10 + x) * x + 100 * q ^ 2 := by
  ring   -- __CODE__

-- Exercise Q-D — run the whole algorithm: √1234 has root 35.
example : toNat (intSqrt [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩]).1 = 35 := by
  native_decide   -- __CODE__

-- Exercise Q-E — harvest the floor property: the returned root squared is ≤ the input.
example (a : MultiDigit) : toNat (intSqrt a).1 * toNat (intSqrt a).1 ≤ toNat a := by
  exact (intSqrt_is_floor a).1   -- __CODE__


/-! ============= WRITE THE WHOLE PROOF (one per chapter) =============
  The student sees only the statement and writes the entire proof after `by`.
  These reference fills are verified to compile. -/

-- Subtraction: subtracting zero, no borrow, returns the digit unchanged.
example (a : Digit) : subDigits a ⟨0, by omega⟩ false = (a, false) := by
  fin_cases a <;> simp [subDigits, subTable]   -- __CODE__

-- Multiplication: shifting left by two places multiplies by 100.
example (a : MultiDigit) : toNat (shiftLeft a 2) = 100 * toNat a := by
  rw [shiftLeft_correct]; ring   -- __CODE__

-- Division: the full quotient/remainder spec, by citing the flagship theorem.
example (a : MultiDigit) (b : Digit) (hb : b.val ≠ 0) :
    toNat a = toNat (longDiv a b).1 * b.val + (longDiv a b).2 ∧ (longDiv a b).2 < b.val := by
  exact longDiv_correct a b hb   -- __CODE__

-- Divisibility: the ÷9 test, built like the ÷3 test.
example (a : MultiDigit) : 9 ∣ toNat a ↔ 9 ∣ digitSum a := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, toNat_mod9_eq_digitSum_mod9]   -- __CODE__

-- Euclid's GCD: the algorithm computes exactly Nat.gcd (invoke the flagship).
example (a b : MultiDigit) : toNat (gcdSub a b) = Nat.gcd (toNat a) (toNat b) := by
  exact gcdSub_correct a b   -- __CODE__

-- Cube root: the units lookup is its own inverse (an involution).
example (d : Digit) : cubeUnitsDigit (cubeUnitsDigit d) = d := by
  fin_cases d <;> decide   -- __CODE__

-- Square root: the algebra the method rests on, fully expanded.
example (q x : Nat) : (10 * q + x) ^ 2 = 100 * q ^ 2 + 20 * q * x + x ^ 2 := by
  ring   -- __CODE__


/-! ============= MULTI-STEP CONSTRUCTION EXERCISES =============
  Short proofs the student assembles from two or three steps. Verified below. -/

-- Division: pull the remainder bound out of the flagship conjunction.
example (a : MultiDigit) (b : Digit) (hb : b.val ≠ 0) : (longDiv a b).2 < b.val := by
  have h := longDiv_correct a b hb   -- __CODE__ (line 1)
  exact h.2                          -- __CODE__ (line 2)

-- Divisibility: divisible by 9 implies divisible by 3.
example (a : MultiDigit) (h : 9 ∣ toNat a) : 3 ∣ toNat a := by
  rw [div_by_3]                       -- __CODE__ (line 1)
  rw [div_by_9] at h                  -- __CODE__ (line 2)
  exact Nat.dvd_trans (by decide) h   -- __CODE__ (line 3)

-- Euclid's GCD: with the second side zero, the gcd is the first side.
example (a b : MultiDigit) (h : toNat b = 0) : toNat (gcdSub a b) = toNat a := by
  rw [gcdSub_correct, h]   -- __CODE__ (line 1)
  simp                     -- __CODE__ (line 2)
