import Arithmetic_Formalization.Foundations
import Arithmetic_Formalization.Subtraction

-- Subtractive Euclid — the rectangular-tiling algorithm.
-- Stop at a square (equal sides); else remove the largest square that fits
-- along the shorter side, i.e. subtract the shorter side from the longer.
def gcdSub (a b : MultiDigit) : MultiDigit :=
  if toNat a = 0 then b
  else if toNat b = 0 then a
  else if toNat a = toNat b then a
  else if toNat b < toNat a then
    gcdSub (verticalSub a b false) b
  else
    gcdSub a (verticalSub b a false)
termination_by toNat a + toNat b
decreasing_by
  · -- a - b branch: new measure toNat(a-b) + toNat b = toNat a < toNat a + toNat b
    have hle : toNat b ≤ toNat a := by omega
    have hsub : toNat (verticalSub a b false) + toNat b = toNat a :=
      verticalSub_correct' a b hle
    omega
  · -- b - a branch: symmetric
    have hle : toNat a ≤ toNat b := by omega
    have hsub : toNat (verticalSub b a false) + toNat a = toNat b :=
      verticalSub_correct' b a hle
    omega

theorem gcdSub_correct (a b : MultiDigit) :
    toNat (gcdSub a b) = Nat.gcd (toNat a) (toNat b) := by
  induction a, b using gcdSub.induct with
  | case1 a b ha =>
    -- toNat a = 0: returns b; gcd 0 (toNat b) = toNat b
    rw [gcdSub, if_pos ha, ha, Nat.gcd_zero_left]
  | case2 a b ha hb =>
    -- toNat b = 0: returns a; gcd (toNat a) 0 = toNat a
    rw [gcdSub, if_neg ha, if_pos hb, hb, Nat.gcd_zero_right]
  | case3 a b ha hb hab =>
    -- toNat a = toNat b: returns a; gcd n n = n
    rw [gcdSub, if_neg ha, if_neg hb, if_pos hab, hab, Nat.gcd_self]
  | case4 a b ha hb hab hlt ih =>
    -- toNat b < toNat a: recurse on (a-b, b); gcd (a-b) b = gcd a b
    rw [gcdSub, if_neg ha, if_neg hb, if_neg hab, if_pos hlt, ih]
    have hle : toNat b ≤ toNat a := by omega
    have hsub : toNat (verticalSub a b false) = toNat a - toNat b := by
      have := verticalSub_correct' a b hle; omega
    rw [hsub]
    exact Nat.gcd_sub_self_left hle
  | case5 a b ha hb hab hge ih =>
    -- toNat a < toNat b: recurse on (a, b-a); gcd a (b-a) = gcd a b
    rw [gcdSub, if_neg ha, if_neg hb, if_neg hab, if_neg hge, ih]
    have hle : toNat a ≤ toNat b := by omega
    have hsub : toNat (verticalSub b a false) = toNat b - toNat a := by
      have := verticalSub_correct' b a hle; omega
    rw [hsub]
    -- goal: gcd (toNat a) (toNat b - toNat a) = gcd (toNat a) (toNat b)
    rw [Nat.gcd_comm (toNat a), Nat.gcd_comm (toNat a)]
    exact Nat.gcd_sub_self_left hle

#eval toNat (gcdSub [⟨8,by omega⟩,⟨4,by omega⟩] [⟨6,by omega⟩,⟨3,by omega⟩])  -- expect 12
#eval toNat (gcdSub [⟨4,by omega⟩,⟨5,by omega⟩] [⟨4,by omega⟩,⟨2,by omega⟩])  -- expect 6
#eval toNat (gcdSub [⟨0,by omega⟩,⟨0,by omega⟩,⟨1,by omega⟩] [⟨5,by omega⟩,⟨2,by omega⟩])

/-
  The rectangular-tiling characterization of gcd.

  Picture a (a × b) rectangle. Ask: what is the largest square tile that
  can pave it exactly — no gaps, no overhang, every tile the same size?

  Claim: that side length is exactly gcd(a, b), and Euclid's subtractive
  algorithm computes it. The connection is not a coincidence — it is what
  the algorithm is *doing* geometrically. Each subtraction step "a - b"
  removes the largest b×b square block that fits along the short edge,
  leaving a smaller rectangle with the same tiling answer. Repeating until
  the rectangle becomes a square lands you on the tile size: gcdSub a b.

  A square of side s tiles the rectangle exactly precisely when s divides
  BOTH sides (s fits a whole number of times along each edge). So:

    • "s tiles the rectangle"      ⟺  s ∣ a  AND  s ∣ b   (s is a COMMON divisor)
    • "largest tile that works"    ⟺  s is the GREATEST such divisor

  That is the definition of gcd. This theorem proves both halves: the value
  gcdSub returns is a valid tile size (divides both sides), and it is the
  best one (every other valid tile size divides it, hence is no larger).
-/
theorem gcdSub_tiles (a b : MultiDigit) :
    -- Part 1: gcdSub a b is a valid square tile — it divides both edges,
    -- so squares of this side pave the rectangle with no remainder.
    (toNat (gcdSub a b) ∣ toNat a ∧ toNat (gcdSub a b) ∣ toNat b)
    -- Part 2: it is the LARGEST valid tile — any side `s` that also tiles
    -- the rectangle (divides both edges) must divide gcdSub a b, and so
    -- cannot exceed it. No bigger square paves the rectangle exactly.
    ∧ ∀ s, s ∣ toNat a → s ∣ toNat b → s ∣ toNat (gcdSub a b) := by
  -- The algorithm's output equals the mathematical gcd (proved earlier),
  -- so every gcd fact transfers directly to the tiling statement.
  rw [gcdSub_correct]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- gcd divides the first edge: the tile fits a whole number of times across `a`.
    exact Nat.gcd_dvd_left (toNat a) (toNat b)
  · -- gcd divides the second edge: likewise along `b`.
    exact Nat.gcd_dvd_right (toNat a) (toNat b)
  · -- Maximality: any common tile size `s` divides the gcd. Since a positive
    -- divisor is never larger than the number it divides, gcd is the biggest
    -- tile that works — exactly the "largest square" we were after.
    intro s hsa hsb
    exact Nat.dvd_gcd hsa hsb
