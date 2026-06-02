import Arithmetic_Formalization.Foundations
import Arithmetic_Formalization.Addition

--Let us as before start with listing out the possible
--single digit x single digit multiplications

def mulTable : Digit → Digit → Digit × Digit
  | ⟨0, _⟩, _ => (⟨0, by omega⟩, ⟨0, by omega⟩)
  | _, ⟨0, _⟩ => (⟨0, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨1, _⟩ => (⟨1, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨2, _⟩ => (⟨2, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨3, _⟩ => (⟨3, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨4, _⟩ => (⟨4, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨6, _⟩ => (⟨6, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨7, _⟩ => (⟨7, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨8, _⟩ => (⟨8, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, ⟨9, _⟩ => (⟨9, by omega⟩, ⟨0, by omega⟩)
  | ⟨2, _⟩, ⟨1, _⟩ => (⟨2, by omega⟩, ⟨0, by omega⟩)
  | ⟨2, _⟩, ⟨2, _⟩ => (⟨4, by omega⟩, ⟨0, by omega⟩)
  | ⟨2, _⟩, ⟨3, _⟩ => (⟨6, by omega⟩, ⟨0, by omega⟩)
  | ⟨2, _⟩, ⟨4, _⟩ => (⟨8, by omega⟩, ⟨0, by omega⟩)
  | ⟨2, _⟩, ⟨5, _⟩ => (⟨0, by omega⟩, ⟨1, by omega⟩)
  | ⟨2, _⟩, ⟨6, _⟩ => (⟨2, by omega⟩, ⟨1, by omega⟩)
  | ⟨2, _⟩, ⟨7, _⟩ => (⟨4, by omega⟩, ⟨1, by omega⟩)
  | ⟨2, _⟩, ⟨8, _⟩ => (⟨6, by omega⟩, ⟨1, by omega⟩)
  | ⟨2, _⟩, ⟨9, _⟩ => (⟨8, by omega⟩, ⟨1, by omega⟩)
  | ⟨3, _⟩, ⟨1, _⟩ => (⟨3, by omega⟩, ⟨0, by omega⟩)
  | ⟨3, _⟩, ⟨2, _⟩ => (⟨6, by omega⟩, ⟨0, by omega⟩)
  | ⟨3, _⟩, ⟨3, _⟩ => (⟨9, by omega⟩, ⟨0, by omega⟩)
  | ⟨3, _⟩, ⟨4, _⟩ => (⟨2, by omega⟩, ⟨1, by omega⟩)
  | ⟨3, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, ⟨1, by omega⟩)
  | ⟨3, _⟩, ⟨6, _⟩ => (⟨8, by omega⟩, ⟨1, by omega⟩)
  | ⟨3, _⟩, ⟨7, _⟩ => (⟨1, by omega⟩, ⟨2, by omega⟩)
  | ⟨3, _⟩, ⟨8, _⟩ => (⟨4, by omega⟩, ⟨2, by omega⟩)
  | ⟨3, _⟩, ⟨9, _⟩ => (⟨7, by omega⟩, ⟨2, by omega⟩)
  | ⟨4, _⟩, ⟨1, _⟩ => (⟨4, by omega⟩, ⟨0, by omega⟩)
  | ⟨4, _⟩, ⟨2, _⟩ => (⟨8, by omega⟩, ⟨0, by omega⟩)
  | ⟨4, _⟩, ⟨3, _⟩ => (⟨2, by omega⟩, ⟨1, by omega⟩)
  | ⟨4, _⟩, ⟨4, _⟩ => (⟨6, by omega⟩, ⟨1, by omega⟩)
  | ⟨4, _⟩, ⟨5, _⟩ => (⟨0, by omega⟩, ⟨2, by omega⟩)
  | ⟨4, _⟩, ⟨6, _⟩ => (⟨4, by omega⟩, ⟨2, by omega⟩)
  | ⟨4, _⟩, ⟨7, _⟩ => (⟨8, by omega⟩, ⟨2, by omega⟩)
  | ⟨4, _⟩, ⟨8, _⟩ => (⟨2, by omega⟩, ⟨3, by omega⟩)
  | ⟨4, _⟩, ⟨9, _⟩ => (⟨6, by omega⟩, ⟨3, by omega⟩)
  | ⟨5, _⟩, ⟨1, _⟩ => (⟨5, by omega⟩, ⟨0, by omega⟩)
  | ⟨5, _⟩, ⟨2, _⟩ => (⟨0, by omega⟩, ⟨1, by omega⟩)
  | ⟨5, _⟩, ⟨3, _⟩ => (⟨5, by omega⟩, ⟨1, by omega⟩)
  | ⟨5, _⟩, ⟨4, _⟩ => (⟨0, by omega⟩, ⟨2, by omega⟩)
  | ⟨5, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, ⟨2, by omega⟩)
  | ⟨5, _⟩, ⟨6, _⟩ => (⟨0, by omega⟩, ⟨3, by omega⟩)
  | ⟨5, _⟩, ⟨7, _⟩ => (⟨5, by omega⟩, ⟨3, by omega⟩)
  | ⟨5, _⟩, ⟨8, _⟩ => (⟨0, by omega⟩, ⟨4, by omega⟩)
  | ⟨5, _⟩, ⟨9, _⟩ => (⟨5, by omega⟩, ⟨4, by omega⟩)
  | ⟨6, _⟩, ⟨1, _⟩ => (⟨6, by omega⟩, ⟨0, by omega⟩)
  | ⟨6, _⟩, ⟨2, _⟩ => (⟨2, by omega⟩, ⟨1, by omega⟩)
  | ⟨6, _⟩, ⟨3, _⟩ => (⟨8, by omega⟩, ⟨1, by omega⟩)
  | ⟨6, _⟩, ⟨4, _⟩ => (⟨4, by omega⟩, ⟨2, by omega⟩)
  | ⟨6, _⟩, ⟨5, _⟩ => (⟨0, by omega⟩, ⟨3, by omega⟩)
  | ⟨6, _⟩, ⟨6, _⟩ => (⟨6, by omega⟩, ⟨3, by omega⟩)
  | ⟨6, _⟩, ⟨7, _⟩ => (⟨2, by omega⟩, ⟨4, by omega⟩)
  | ⟨6, _⟩, ⟨8, _⟩ => (⟨8, by omega⟩, ⟨4, by omega⟩)
  | ⟨6, _⟩, ⟨9, _⟩ => (⟨4, by omega⟩, ⟨5, by omega⟩)
  | ⟨7, _⟩, ⟨1, _⟩ => (⟨7, by omega⟩, ⟨0, by omega⟩)
  | ⟨7, _⟩, ⟨2, _⟩ => (⟨4, by omega⟩, ⟨1, by omega⟩)
  | ⟨7, _⟩, ⟨3, _⟩ => (⟨1, by omega⟩, ⟨2, by omega⟩)
  | ⟨7, _⟩, ⟨4, _⟩ => (⟨8, by omega⟩, ⟨2, by omega⟩)
  | ⟨7, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, ⟨3, by omega⟩)
  | ⟨7, _⟩, ⟨6, _⟩ => (⟨2, by omega⟩, ⟨4, by omega⟩)
  | ⟨7, _⟩, ⟨7, _⟩ => (⟨9, by omega⟩, ⟨4, by omega⟩)
  | ⟨7, _⟩, ⟨8, _⟩ => (⟨6, by omega⟩, ⟨5, by omega⟩)
  | ⟨7, _⟩, ⟨9, _⟩ => (⟨3, by omega⟩, ⟨6, by omega⟩)
  | ⟨8, _⟩, ⟨1, _⟩ => (⟨8, by omega⟩, ⟨0, by omega⟩)
  | ⟨8, _⟩, ⟨2, _⟩ => (⟨6, by omega⟩, ⟨1, by omega⟩)
  | ⟨8, _⟩, ⟨3, _⟩ => (⟨4, by omega⟩, ⟨2, by omega⟩)
  | ⟨8, _⟩, ⟨4, _⟩ => (⟨2, by omega⟩, ⟨3, by omega⟩)
  | ⟨8, _⟩, ⟨5, _⟩ => (⟨0, by omega⟩, ⟨4, by omega⟩)
  | ⟨8, _⟩, ⟨6, _⟩ => (⟨8, by omega⟩, ⟨4, by omega⟩)
  | ⟨8, _⟩, ⟨7, _⟩ => (⟨6, by omega⟩, ⟨5, by omega⟩)
  | ⟨8, _⟩, ⟨8, _⟩ => (⟨4, by omega⟩, ⟨6, by omega⟩)
  | ⟨8, _⟩, ⟨9, _⟩ => (⟨2, by omega⟩, ⟨7, by omega⟩)
  | ⟨9, _⟩, ⟨1, _⟩ => (⟨9, by omega⟩, ⟨0, by omega⟩)
  | ⟨9, _⟩, ⟨2, _⟩ => (⟨8, by omega⟩, ⟨1, by omega⟩)
  | ⟨9, _⟩, ⟨3, _⟩ => (⟨7, by omega⟩, ⟨2, by omega⟩)
  | ⟨9, _⟩, ⟨4, _⟩ => (⟨6, by omega⟩, ⟨3, by omega⟩)
  | ⟨9, _⟩, ⟨5, _⟩ => (⟨5, by omega⟩, ⟨4, by omega⟩)
  | ⟨9, _⟩, ⟨6, _⟩ => (⟨4, by omega⟩, ⟨5, by omega⟩)
  | ⟨9, _⟩, ⟨7, _⟩ => (⟨3, by omega⟩, ⟨6, by omega⟩)
  | ⟨9, _⟩, ⟨8, _⟩ => (⟨2, by omega⟩, ⟨7, by omega⟩)
  | ⟨9, _⟩, ⟨9, _⟩ => (⟨1, by omega⟩, ⟨8, by omega⟩)
  | ⟨n+10, h⟩, _ => absurd h (by omega)
  | _, ⟨n+10, h⟩ => absurd h (by omega)

--Some test cases
#eval mulTable ⟨3, by omega⟩ ⟨7, by omega⟩  -- expect (1, 2) -- 3×7=21
#eval mulTable ⟨9, by omega⟩ ⟨9, by omega⟩  -- expect (1, 8) -- 9×9=81
#eval mulTable ⟨5, by omega⟩ ⟨5, by omega⟩  -- expect (5, 2) -- 5×5=25
#eval mulTable ⟨0, by omega⟩ ⟨7, by omega⟩  -- expect (0, 0) -- 0×7=0

--Proving correctness of the table boils down
--to unfolding all cases
theorem mulTable_correct (a b : Digit) :
    (mulTable a b).1.val + 10 * (mulTable a b).2.val =
    a.val * b.val := by
  fin_cases a <;> fin_cases b <;> simp [mulTable]

-- Multiply a MultiDigit number by a single digit
-- carry is a Digit representing the carry from the previous column
def mulDigit : MultiDigit → Digit → Digit → MultiDigit
  | [], _, ⟨0, _⟩ =>
      -- No remaining digits and no carry -- multiplication complete
      []
  | [], _, carry =>
      -- No remaining digits but carry remains
      -- Write the carry as the final most significant digit
      [carry]
  | d :: ds, b, carry =>
      -- Main case: multiply current digit d by b
      -- then handle the incoming carry from the previous column

      -- Step 1: Look up d × b in the times table
      -- units is the ones digit of the product
      -- tens is the tens digit of the product (the carry from multiplication)
      let (units, tens) := mulTable d b
      -- Step 2: Add the incoming carry to the units digit
      -- This may produce a new carry carry' if units + carry ≥ 10
      let (units', carry') := addTable units carry
      -- Step 3: Convert Bool carry to Digit for the next addition
      -- addTable returns a Bool carry but addTable expects a Digit
      let carryDigit : Digit := if carry' then ⟨1, by omega⟩ else ⟨0, by omega⟩
      -- Step 4: Combine the tens digit from multiplication
      -- with any carry produced in Step 2
      -- This gives the carry to pass to the next column
      let (finalCarry, _) := addTable tens carryDigit
      -- Step 5: Write the units digit and recurse on remaining digits
      -- passing the combined carry forward to the next column
      units' :: mulDigit ds b finalCarry
termination_by a _ _ => a.length
-- Termination: the first list gets shorter at every recursive call

--Some test cases
-- 123 × 7 = 861
#eval toNat (mulDigit
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  ⟨7, by omega⟩
  ⟨0, by omega⟩)
-- expect 861

-- 99 × 9 = 891
#eval toNat (mulDigit
  [⟨9, by omega⟩, ⟨9, by omega⟩]
  ⟨9, by omega⟩
  ⟨0, by omega⟩)
-- expect 891

-- 0 × 5 = 0
#eval toNat (mulDigit [] ⟨5, by omega⟩ ⟨0, by omega⟩)
-- expect 0

--Now lets us prove correctness

--first a helper lemma
-- The value of two concatenated digit lists
-- equals the first number plus 10^length * the second number
-- This is the key lemma for reasoning about shifted partial products
theorem toNat_append (a b : List Digit) :
  toNat (a ++ b) = toNat a + 10^(a.length) * toNat b := by
  -- Structural induction on the first list 'a'
  induction a with
  | nil =>
    -- Base case: 'a' is empty. toNat([]) evaluates to 0.
    -- Equation trivially reduces to: toNat b = 0 + 1 * toNat b.
    simp [toNat]
  | cons d ds ih =>
    -- 1. Unfold toNat to extract the head digit 'd' from the combined list.
    simp [toNat]
    -- 2. Substitute the inductive assumption for the tail 'ds'.
    rw [ih]
    -- 3. Solve the algebra. 'ring' natively groups the terms and matches
    -- the outer '10 *' to the '+ 1' in the exponent (10^(ds.length + 1)).
    ring

-- Single digit multiplication is correct:
-- the result represents toNat a * b + carry

set_option maxHeartbeats 0 in
-- We disable the heartbeat limit here because the proof requires
-- exhaustive case analysis over all combinations of digits (0-9)
-- and carry values (0-9), generating up to 1000 concrete cases.
-- Each case is closed by computation but the sheer number of cases
-- exceeds Lean's default heartbeat limit.
-- This is intentional and safe -- the proof is purely computational.
theorem mulDigit_correct (a : MultiDigit) (b : Digit) (carry : Digit) :
    toNat (mulDigit a b carry) = toNat a * b.val + carry.val := by
  induction a generalizing carry with
  | nil =>
    -- Base case: empty list
    -- expand all carry and b combinations
    -- rfl closes since both sides reduce to same literal
    fin_cases carry <;> fin_cases b <;>
    simp only [mulDigit, toNat]
  | cons d ds ih =>
    -- Recursive case: current digit d, remaining digits ds
    simp only [mulDigit, toNat]
    -- correctness of times table lookup for d × b
    have hmul := mulTable_correct d b
    -- correctness of adding incoming carry to units digit
    have hadd1 := addTable_correct (mulTable d b).1 carry
    -- converts Bool carry from addTable to Digit for next addTable call
    set carryDigit : Digit :=
      if (addTable (mulTable d b).1 carry).2
      then ⟨1, by omega⟩
      else ⟨0, by omega⟩ with hcd
    -- correctness of combining tens digit with carryDigit
    have hadd2 := addTable_correct (mulTable d b).2 carryDigit
    -- inductive hypothesis applied with new carry
    have hih := ih (addTable (mulTable d b).2 carryDigit).1
    -- expand all digit and carry combinations
    -- with everything concrete simp_all reduces to arithmetic
    -- omega closes each case
    fin_cases d <;> fin_cases b <;> fin_cases carry <;>
    simp_all [mulTable, addTable, carryVal] <;>
    omega

-- Full Multi-Digit Multiplication using a Running Sum Accumulator
def mulHelper (a : MultiDigit) (b : MultiDigit) (acc : MultiDigit) : MultiDigit :=
  match b with
  | [] => acc  -- Base case: multiplier digits exhausted, return the accumulated sum
  | d :: ds =>
    -- 1. Multiply the current shifted 'a' by the single multiplier digit 'd'
    -- We pass an initial digit carry of 0 matching mulDigit definition
    let row := mulDigit a d ⟨0, by omega⟩
    -- 2. Add this row to our running total using  verticalAdd with an initial carry of false
    let newAcc := verticalAdd acc row false
    -- 3. Shift 'a' left by a factor of 10 for the next place-value position.
    -- Prepending 0 to a LSB first list multiplies its total value by 10.
    let shiftedA := ⟨0, by omega⟩ :: a
    -- 4. Recurse into the remaining digits of the multiplier
    mulHelper shiftedA ds newAcc

-- The top-level multiplication
def verticalMul (a b : MultiDigit) : MultiDigit :=
  mulHelper a b []

-- Test Case 1: 123 × 891 = 109593
#eval toNat (verticalMul
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]   -- 123
  [⟨1, by omega⟩, ⟨9, by omega⟩, ⟨8, by omega⟩])  -- 891
-- Expects: 109593

-- Test Case 2: 99 × 9 = 891
#eval toNat (verticalMul
  [⟨9, by omega⟩, ⟨9, by omega⟩]                 -- 99
  [⟨9, by omega⟩])                               -- 9
-- Expects: 891

-- Test Case 3: 456 × 0 = 0
#eval toNat (verticalMul
  [⟨6, by omega⟩, ⟨5, by omega⟩, ⟨4, by omega⟩]   -- 456
  [])                                            -- 0 (Empty list representation)
-- Expects: 0

--Correctness Proof
--Let us first prove the shifting property
theorem toNat_cons_zero (a : MultiDigit) :
    toNat (⟨0, by omega⟩ :: a) = 10 * toNat a := by
  simp [toNat]
-- simple unfolding of the new number plus some algebraic multiplication is
-- sufficient to finish the proof

theorem mulHelper_correct (a b : MultiDigit) (acc : MultiDigit) :
    toNat (mulHelper a b acc) =
    toNat acc + toNat a * toNat b := by
  -- Induct on b generalizing a and acc
  -- both change at every recursive call
  induction b generalizing a acc with
  | nil =>
    -- Base case: b is empty
    -- mulHelper returns acc directly
    -- toNat acc + toNat a * 0 = toNat acc
    simp [mulHelper, toNat]
  | cons d ds ih =>
    -- Recursive case: current digit d, remaining digits ds
    simp only [mulHelper, toNat]
    -- correctness of multiplying a by single digit d
    have hmul := mulDigit_correct a d ⟨0, by omega⟩
    -- toNat of shifted a is 10 * toNat a
    have hshift := toNat_cons_zero a
    -- apply inductive hypothesis to shifted a and new acc
    have hih := ih (⟨0, by omega⟩ :: a) (verticalAdd acc (mulDigit a d ⟨0, by omega⟩) false)
    -- verticalAdd_correct connects addition to natural number addition
    have hadd := verticalAdd_correct' acc (mulDigit a d ⟨0, by omega⟩)
    -- combine everything
    simp [toNat, mulDigit_correct] at *
    linarith

-- Main correctness theorem
-- mulActual is just mulHelper with empty accumulator
-- toNat [] = 0 so the accumulator term vanishes
theorem verticalMul_correct (a b : MultiDigit) :
    toNat (verticalMul a b) = toNat a * toNat b := by
  simp [verticalMul, mulHelper_correct, toNat]

-- Shift a MultiDigit left by n positions (multiply by 10^n)
-- Implemented by prepending n zeros (least significant first)
def shiftLeft : MultiDigit → Nat → MultiDigit
  | xs, 0     => xs
  | xs, n + 1 => ⟨0, by omega⟩ :: shiftLeft xs n

-- A single partial product: multiply a by one digit of b
-- then shift left by the digit's position
def partialProduct (a : MultiDigit) (b : Digit) (pos : Nat) : MultiDigit :=
  shiftLeft (mulDigit a b ⟨0, by omega⟩) pos

-- Collect all partial products
-- Each digit of b generates one partial product shifted by its position
def partialProducts : MultiDigit → MultiDigit → Nat → List MultiDigit
  | _, [], _        => []
  | a, b :: bs, pos =>
      partialProduct a b pos :: partialProducts a bs (pos + 1)

-- Add a list of MultiDigit numbers together
def sumAll : List MultiDigit → MultiDigit
  | []      => []
  | x :: xs => verticalAdd x (sumAll xs) false

-- Full long multiplication using partial products
def verticalMulPP (a b : MultiDigit) : MultiDigit :=
  sumAll (partialProducts a b 0)

-- 123 × 45 = 5535
#eval toNat (verticalMulPP
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [⟨5, by omega⟩, ⟨4, by omega⟩])
-- expect 5535

-- 99 × 99 = 9801
#eval toNat (verticalMulPP
  [⟨9, by omega⟩, ⟨9, by omega⟩]
  [⟨9, by omega⟩, ⟨9, by omega⟩])
-- expect 9801

-- 123 × 891 = 109593
#eval toNat (verticalMulPP
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [⟨1, by omega⟩, ⟨9, by omega⟩, ⟨8, by omega⟩])
-- expect 109593

-- anything × 0 = 0
#eval toNat (verticalMulPP
  [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]
  [])
-- expect 0

-- shiftLeft multiplies by 10^n
theorem shiftLeft_correct (a : MultiDigit) (n : Nat) :
    toNat (shiftLeft a n) = toNat a * 10^n := by
  induction n with
  | zero => simp [shiftLeft]
  | succ n ih =>
    simp [shiftLeft, ih]
    ring

-- partialProduct correctness
theorem partialProduct_correct (a : MultiDigit) (b : Digit) (pos : Nat) :
    toNat (partialProduct a b pos) = toNat a * b.val * 10^pos := by
  simp [partialProduct, shiftLeft_correct, mulDigit_correct]


-- sumAll correctness
theorem sumAll_correct (products : List MultiDigit) :
    toNat (sumAll products) = (products.map toNat).sum := by
  induction products with
  | nil => simp [sumAll]
  | cons x xs ih =>
    simp [sumAll, verticalAdd_correct', ih]


-- partialProducts correctness
theorem partialProducts_correct (a b : MultiDigit) (pos : Nat) :
    (partialProducts a b pos).map toNat =
    b.mapIdx (fun i d => toNat a * d.val * 10^(pos + i)) := by
  --The list of partial product values equals what you'd get by mapping each digit of b with its
  -- index to toNat a * digit * 10^(pos + index).
  induction b generalizing pos with
  | nil =>
    -- Base case: Both sides evaluate to empty lists.
    -- rfl forces the kernel to compute both sides to [], closing the goal instantly.
    rfl
  | cons d ds ih =>
    -- Step 1: Use standard list lemmas to evaluate one step of both sides
    simp only [partialProducts, List.map_cons, List.mapIdx_cons]
    -- Step 2: Split into Head equality and Tail equality
    congr 1
    · -- Subgoal 1: Head equality
      simp [partialProduct_correct]
    · -- Subgoal 2: Tail equality
      -- Apply the inductive hypothesis to the tail
      rw [ih (pos + 1)]
      -- We now have: ds.mapIdx (f) = ds.mapIdx (g).
      -- congr 1 strips the mapIdx constructor, leaving just the inner functions to prove equal.
      congr 1
      -- ext introduces the function arguments: index 'i' and digit 'y'
      ext i y
      -- Remove the common multiplicative factor.
      congr 1
      -- 2nd congr 1 strips the base 10:
      congr 1
      -- Now that the non-linear exponentiation is gone, omega handles the linear
      --addition perfectly!
      omega

-- Helper lemma that generalizes the position index to allow step-by-step index shifting
lemma verticalMulPP_helper (a b : MultiDigit) (pos : Nat) :
    toNat (sumAll (partialProducts a b pos)) = toNat a * toNat b * 10^pos := by
  induction b generalizing pos with
  | nil =>
    -- simp automatically handles the 'X * 0 = 0' arithmetic
    simp [partialProducts, sumAll, toNat]
  | cons d ds ih =>
    -- Step 1: Explicitly unfold definitions to expose the head and tail structure
    unfold partialProducts sumAll
    -- Step 2: Apply verticalAdd_correct' to split the addition
    -- This exposes the trapped recursive sumAll term so we can rewrite it.
    simp [verticalAdd_correct', partialProduct_correct, toNat]
    -- Step 3: Now that the term is exposed, the generalized IH matches perfectly.
    rw [ih (pos + 1)]
    -- Step 4: Clean up the algebraic polynomial distribution
    ring


-- Main theorem
theorem verticalMulPP_correct (a b : MultiDigit) :
    toNat (verticalMulPP a b) = toNat a * toNat b := by
  -- Step 1: Unfold the top-level definition
  unfold verticalMulPP
  -- Step 2: Instantiate our helper lemma at position 0
  rw [verticalMulPP_helper a b 0]
  -- Step 3: Since 10^0 = 1, ring perfectly simplifies the multiplication to finish the proof
  ring
