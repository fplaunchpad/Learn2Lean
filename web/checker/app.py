"""
Tiny "submit & check" Lean exercise server.

Each exercise is a Lean scaffold with a `__CODE__` slot. On POST /check the
student's code is spliced in, written to a temp .lean file, compiled with
`lake env lean`, and the result (✓ or Lean's first error block) is returned.

The reference fills for these scaffolds are verified to compile in
  Arithmetic_Formalization/ExerciseScaffolds.lean

Run:  see web/checker/README.md
"""
import os, subprocess, tempfile
from flask import Flask, request, jsonify, send_from_directory

# --- configuration (edit LEAN_PROJECT or set the env var) ---
LEAN_PROJECT = os.environ.get(
    "LEAN_PROJECT",
    r"C:\Users\Anubhav\Downloads\Lean4\Arithmetic_Formalization",
)
WEB_DIR  = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # the web/ folder
TIMEOUT  = 120  # seconds per check (first check is slow: it cold-loads Mathlib)

# --- exercises: a Lean scaffold with one `__CODE__` slot each ---
EXERCISES = {
    # Fill the case where the top number is empty and the bottom still has digits.
    "add_bcase": """import Arithmetic_Formalization.Addition

def studentAdd : MultiDigit → MultiDigit → Bool → MultiDigit
  | [], [], false => []
  | [], [], true  => [⟨1, by omega⟩]
  | [], b :: bs, c => __CODE__
  | a :: as, [], c => let (d, c') := addDigits a ⟨0, by omega⟩ c; d :: studentAdd as [] c'
  | a :: as, b :: bs, c => let (d, c') := addDigits a b c; d :: studentAdd as bs c'
termination_by a b _ => a.length + b.length

example :
    toNat (studentAdd [] [⟨5,by omega⟩,⟨2,by omega⟩] false) = 25
  ∧ toNat (studentAdd [] [⟨9,by omega⟩] true) = 10
  ∧ toNat (studentAdd [⟨3,by omega⟩] [⟨4,by omega⟩,⟨5,by omega⟩] false) = 57 := by native_decide
""",
    # Fill the one-line proof.
    "add_proof": """import Arithmetic_Formalization.Addition

theorem add_correct_nocarry (a b : MultiDigit) :
    toNat (verticalAdd a b false) = toNat a + toNat b := by
  __CODE__
""",
    # Prove a concrete column evaluation (computation, not a lemma).
    "add_eval": """import Arithmetic_Formalization.Addition

example : addDigits ⟨9, by omega⟩ ⟨9, by omega⟩ true = (⟨9, by omega⟩, true) := by
  __CODE__
""",
    # Prove, by exhausting the ten digits, that a + 0 (no carry) is (a, false).
    "add_zero": """import Arithmetic_Formalization.Addition

theorem add_zero_no_carry (a : Digit) :
    addDigits a ⟨0, by omega⟩ false = (a, false) := by
  __CODE__
""",
    # Write the WHOLE proof: the single-digit addition table is symmetric.
    "add_whole": """import Arithmetic_Formalization.Addition

theorem addTable_comm (a b : Digit) : addTable a b = addTable b a := by
  __CODE__
""",
    # --- subtraction ---
    # Fill the case where the bottom number is empty and the top still has digits.
    "sub_acase": """import Arithmetic_Formalization.Subtraction

def studentSub : MultiDigit → MultiDigit → Bool → MultiDigit
  | [], [], _ => []
  | [], _ :: _, _ => []
  | a :: as, [], borrow => __CODE__
  | a :: as, b :: bs, borrow => let (d, b') := subDigits a b borrow; d :: studentSub as bs b'
termination_by a b _ => a.length + b.length

example :
    toNat (studentSub [⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] [⟨1,by omega⟩,⟨9,by omega⟩] false) = 32
  ∧ toNat (studentSub [⟨0,by omega⟩,⟨0,by omega⟩,⟨1,by omega⟩] [⟨1,by omega⟩] false) = 99
  ∧ toNat (studentSub [⟨5,by omega⟩,⟨7,by omega⟩] [] false) = 75 := by native_decide
""",
    # Prove a concrete column evaluation: 3 − 7 borrows.
    "sub_eval": """import Arithmetic_Formalization.Subtraction

example : subDigits ⟨3, by omega⟩ ⟨7, by omega⟩ false = (⟨6, by omega⟩, true) := by
  __CODE__
""",
    # Prove, by exhausting the ten digits, that a − a (no borrow) is (0, false).
    "sub_self": """import Arithmetic_Formalization.Subtraction

theorem self_sub_no_borrow (a : Digit) :
    subDigits a a false = (⟨0, by omega⟩, false) := by
  __CODE__
""",
    # Prove the no-borrow corollary, carrying the precondition through.
    "sub_proof": """import Arithmetic_Formalization.Subtraction

theorem sub_correct_noborrow (a b : MultiDigit) (h : toNat b ≤ toNat a) :
    toNat (verticalSub a b false) + toNat b = toNat a := by
  __CODE__
""",
    # --- multiplication ---
    # Fill the case where the digits run out but a carry remains.
    "mul_acase": """import Arithmetic_Formalization.Multiplication

def studentMulDigit : MultiDigit → Digit → Digit → MultiDigit
  | [], _, ⟨0, _⟩ => []
  | [], _, carry => __CODE__
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
""",
    # Prove a concrete times-table entry: 3 × 7 = 21 → (1, 2).
    "mul_eval": """import Arithmetic_Formalization.Multiplication

example : mulTable ⟨3, by omega⟩ ⟨7, by omega⟩ = (⟨1, by omega⟩, ⟨2, by omega⟩) := by
  __CODE__
""",
    # Prove, by exhausting the ten digits, that a × 0 is (0, 0).
    "mul_zero": """import Arithmetic_Formalization.Multiplication

theorem mul_by_zero (a : Digit) :
    mulTable a ⟨0, by omega⟩ = (⟨0, by omega⟩, ⟨0, by omega⟩) := by
  __CODE__
""",
    # Apply the main theorem: multiplying by the empty list is 0.
    "mul_empty": """import Arithmetic_Formalization.Multiplication

theorem mul_empty (a : MultiDigit) :
    toNat (verticalMulPP a []) = 0 := by
  __CODE__
""",
    # One shift is one factor of ten: rewrite with shiftLeft_correct, close with ring.
    "mul_shift": """import Arithmetic_Formalization.Multiplication

example (a : MultiDigit) : toNat (shiftLeft a 1) = 10 * toNat a := by
  __CODE__
""",
    # --- division ---
    # Fill trimTrailingZeros' keep-the-digit case.
    "div_trim": """import Arithmetic_Formalization.Division

def studentTrim : MultiDigit → MultiDigit
  | [] => []
  | d :: ds =>
      match studentTrim ds with
      | [] => if d.val == 0 then [] else [d]
      | ts => __CODE__

example :
    toNat (studentTrim [⟨4,by omega⟩,⟨3,by omega⟩,⟨0,by omega⟩]) = 34
  ∧ (studentTrim [⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩]).length = 0 := by native_decide
""",
    # The invariant-survival bound, stripped to its arithmetic.
    "div_bound": """import Arithmetic_Formalization.Division

example (v b q : Nat) (h1 : q * b ≤ v) (h2 : v < q * b + b) : v - q * b < b := by
  __CODE__
""",
    # Evaluate the trial digit.
    "div_trial": """import Arithmetic_Formalization.Division

example : findQuotientDigit 23 ⟨5, by omega⟩ = ⟨4, by omega⟩ := by
  __CODE__
""",
    # Run the whole algorithm on 1234 ÷ 5.
    "div_eval": """import Arithmetic_Formalization.Division

example :
    (longDiv [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨5,by omega⟩).2 = 4
  ∧ toNat (longDiv [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨5,by omega⟩).1 = 246 := by
  __CODE__
""",
    # Cite the trimming lemma.
    "div_cite": """import Arithmetic_Formalization.Division

example (a : MultiDigit) : toNat (trimTrailingZeros a) = toNat a := by
  __CODE__
""",
    # --- divisibility ---
    # Fill digitSum's fold step.
    "divis_dsum": """import Arithmetic_Formalization.Divisibility

def studentDigitSum (a : MultiDigit) : Nat :=
  a.foldl (fun acc d => __CODE__) 0

example :
    studentDigitSum [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] = 10
  ∧ studentDigitSum [] = 0 := by native_decide
""",
    # 1234 mod 9 = 1.
    "divis_mod": """import Arithmetic_Formalization.Divisibility

example : myMod [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] ⟨9, by omega⟩ = 1 := by
  __CODE__
""",
    # even/odd position sums of 1234 are (6, 4).
    "divis_alt": """import Arithmetic_Formalization.Divisibility

example : altSums [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩] = (6, 4) := by
  __CODE__
""",
    # Cite the ÷9 test.
    "divis_cite": """import Arithmetic_Formalization.Divisibility

example (a : MultiDigit) : 9 ∣ toNat a ↔ 9 ∣ digitSum a := by
  __CODE__
""",
    # The ÷3 test from its congruence, by rewriting.
    "divis_rw": """import Arithmetic_Formalization.Divisibility

example (a : MultiDigit) : 3 ∣ toNat a ↔ 3 ∣ digitSum a := by
  __CODE__
""",
    # --- Euclid's GCD ---
    # Run the algorithm: gcd(48, 36) = 12.
    "gcd_eval": """import Arithmetic_Formalization.EuclidGCDAlgo

example : toNat (gcdSub [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩]) = 12 := by
  __CODE__
""",
    # The termination argument, stripped to its arithmetic.
    "gcd_term": """import Arithmetic_Formalization.EuclidGCDAlgo

example (x y : Nat) (h1 : 0 < y) (h2 : y ≤ x) : (x - y) + y < x + y := by
  __CODE__
""",
    # Fill the carving branch of studentGcd (a copy of gcdSub).
    "gcd_case": """import Arithmetic_Formalization.EuclidGCDAlgo

def studentGcd (a b : MultiDigit) : MultiDigit :=
  if toNat a = 0 then b
  else if toNat b = 0 then a
  else if toNat a = toNat b then a
  else if toNat b < toNat a then
    __CODE__
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

example : toNat (studentGcd [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩]) = 12 := by native_decide
""",
    # Harvest the tiling theorem: the gcd divides the first side.
    "gcd_cite": """import Arithmetic_Formalization.EuclidGCDAlgo

example (a b : MultiDigit) : toNat (gcdSub a b) ∣ toNat a := by
  __CODE__
""",
    # gcd is symmetric: rewrite through gcdSub_correct, then cite Nat.gcd_comm.
    "gcd_comm": """import Arithmetic_Formalization.EuclidGCDAlgo

example (a b : MultiDigit) : toNat (gcdSub a b) = toNat (gcdSub b a) := by
  rw [gcdSub_correct, gcdSub_correct]
  __CODE__
""",
    # --- cube-root trick ---
    # Read a cube backwards: cube ending in 3 -> root ending in 7.
    "cube_units": """import Arithmetic_Formalization.CuberootTrick

example : cubeUnitsDigit ⟨3, by omega⟩ = ⟨7, by omega⟩ := by
  __CODE__
""",
    # Run the whole trick on 54^3.
    "cube_eval": """import Arithmetic_Formalization.CuberootTrick

example : cubeRootVal (fromNat (54 ^ 3)) = 54 := by
  __CODE__
""",
    # The units lookup really inverts a cube's last digit, for every digit.
    "cube_bij": """import Arithmetic_Formalization.CuberootTrick

example (d : Digit) : (cubeUnitsDigit d).val ^ 3 % 10 = d.val := by
  __CODE__
""",
    # Cite the finished brute-force theorem.
    "cube_cite": """import Arithmetic_Formalization.CuberootTrick

example (m : Nat) (hm : m ≤ 99) : cubeRootVal (fromNat (m ^ 3)) = m := by
  __CODE__
""",
    # The tens search on its own: largest d with d^3 <= 157 is 5.
    "cube_tens": """import Arithmetic_Formalization.CuberootTrick

example : findCubeTensHelper 157 9 = ⟨5, by omega⟩ := by
  __CODE__
""",
    # --- square roots ---
    # First root digit: largest x with x^2 <= 12 is 3.
    "sqrt_digit": """import Arithmetic_Formalization.Squareroot

example : findSqrtDigit 12 [] = ⟨3, by omega⟩ := by
  __CODE__
""",
    # The shifting-divisor step: with q = [3], largest x with (60+x)*x <= 334 is 5.
    "sqrt_step": """import Arithmetic_Formalization.Squareroot

example : findSqrtDigit 334 [⟨3, by omega⟩] = ⟨5, by omega⟩ := by
  __CODE__
""",
    # The identity behind "double the root, append the digit".
    "sqrt_ring": """import Arithmetic_Formalization.Squareroot

example (q x : Nat) : (10 * q + x) ^ 2 = (2 * q * 10 + x) * x + 100 * q ^ 2 := by
  __CODE__
""",
    # Run the whole algorithm: sqrt 1234 has root 35.
    "sqrt_eval": """import Arithmetic_Formalization.Squareroot

example : toNat (intSqrt [⟨4,by omega⟩,⟨3,by omega⟩,⟨2,by omega⟩,⟨1,by omega⟩]).1 = 35 := by
  __CODE__
""",
    # Harvest the floor property: the returned root squared is <= the input.
    "sqrt_cite": """import Arithmetic_Formalization.Squareroot

example (a : MultiDigit) : toNat (intSqrt a).1 * toNat (intSqrt a).1 ≤ toNat a := by
  __CODE__
""",
    # --- "write the whole proof" (one per chapter; nothing pre-filled) ---
    "sub_whole": """import Arithmetic_Formalization.Subtraction

example (a : Digit) : subDigits a ⟨0, by omega⟩ false = (a, false) := by
  __CODE__
""",
    "mul_whole": """import Arithmetic_Formalization.Multiplication

example (a : MultiDigit) : toNat (shiftLeft a 2) = 100 * toNat a := by
  __CODE__
""",
    "div_whole": """import Arithmetic_Formalization.Division

example (a : MultiDigit) (b : Digit) (hb : b.val ≠ 0) :
    toNat a = toNat (longDiv a b).1 * b.val + (longDiv a b).2 ∧ (longDiv a b).2 < b.val := by
  __CODE__
""",
    "divis_whole": """import Arithmetic_Formalization.Divisibility

example (a : MultiDigit) : 9 ∣ toNat a ↔ 9 ∣ digitSum a := by
  __CODE__
""",
    "gcd_whole": """import Arithmetic_Formalization.EuclidGCDAlgo

example (a b : MultiDigit) : toNat (gcdSub a b) = Nat.gcd (toNat a) (toNat b) := by
  __CODE__
""",
    "cube_whole": """import Arithmetic_Formalization.CuberootTrick

example (d : Digit) : cubeUnitsDigit (cubeUnitsDigit d) = d := by
  __CODE__
""",
    "sqrt_whole": """import Arithmetic_Formalization.Squareroot

example (q x : Nat) : (10 * q + x) ^ 2 = 100 * q ^ 2 + 20 * q * x + x ^ 2 := by
  __CODE__
""",
    # --- multi-step construction exercises (student builds a short proof) ---
    "div_build": """import Arithmetic_Formalization.Division

example (a : MultiDigit) (b : Digit) (hb : b.val ≠ 0) : (longDiv a b).2 < b.val := by
  __CODE__
""",
    "divis_build": """import Arithmetic_Formalization.Divisibility

example (a : MultiDigit) (h : 9 ∣ toNat a) : 3 ∣ toNat a := by
  __CODE__
""",
    "gcd_build": """import Arithmetic_Formalization.EuclidGCDAlgo

example (a b : MultiDigit) (h : toNat b = 0) : toNat (gcdSub a b) = toNat a := by
  __CODE__
""",
}

app = Flask(__name__, static_folder=WEB_DIR, static_url_path="")


def first_error_block(text: str) -> str:
    """Show from the first `error:` onward, capped at ~25 lines."""
    i = text.find("error:")
    seg = text[i:] if i >= 0 else text
    return "\n".join(seg.splitlines()[:25]).strip()


@app.route("/")
def home():
    return send_from_directory(WEB_DIR, "addition.html")


@app.post("/check")
def check():
    data = request.get_json(force=True, silent=True) or {}
    template = EXERCISES.get(data.get("exercise", ""))
    code = (data.get("code") or "").strip()
    if template is None:
        return jsonify(ok=False, output="Unknown exercise id."), 400
    if not code:
        return jsonify(ok=False, output="Write something first.")

    source = template.replace("__CODE__", code)
    fd, path = tempfile.mkstemp(suffix=".lean")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(source)
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", path],
                cwd=LEAN_PROJECT, capture_output=True, text=True, timeout=TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            return jsonify(ok=False, output=f"Timed out after {TIMEOUT}s.")
        except FileNotFoundError:
            return jsonify(ok=False, output="`lake` not found — is Lean/elan on PATH?"), 500
        out = (proc.stdout + "\n" + proc.stderr)
        ok = (proc.returncode == 0 and "error:" not in out)
        return jsonify(ok=ok, output="" if ok else first_error_block(out))
    finally:
        try: os.remove(path)
        except OSError: pass


if __name__ == "__main__":
    # Defaults to 127.0.0.1 (local only). On a server, expose it with
    #   CHECKER_HOST=0.0.0.0 python app.py
    # but only AFTER sandboxing — this endpoint runs arbitrary Lean (see README).
    host = os.environ.get("CHECKER_HOST", "127.0.0.1")
    port = int(os.environ.get("CHECKER_PORT", "5000"))
    app.run(host=host, port=port, debug=False)
