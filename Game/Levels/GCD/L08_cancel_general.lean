import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L07_gcd_div_coprime

World "GCD"
Level 8
Title "The General Cancellation Law"

Introduction "
Time to combine the last two levels into the *fully general* cancellation law — no coprimality assumption required!

If $a \\cdot c \\equiv b \\cdot c \\pmod m$ and `IsGCD(c, m) d` with $d \\neq 0$, and we write $c = c_1 \\cdot d$, $m = m_1 \\cdot d$ (exactly as in Level 7), then $a \\equiv b \\pmod{m_1}$.

**Strategy — assemble, don't reprove:**
1. Apply `gcd_div_coprime` (Level 7) to get `IsGCD(c_1, m_1) 1`.
2. Unfold the congruence hypothesis, substitute $c = c_1 \\cdot d$ and $m = m_1 \\cdot d$, and cancel the shared factor $d$ (using `mul_left_cancel₀` again). This will leave you with a plain algebraic equation!
3. **Reassemble the congruence:** create the specific hypothesis you need using `have h1' : (a * c1) ≡ (b * c1) (mod m1) := by ...`. Prove it by unfolding `ModEq` and using the cancelled equation from step 2.
4. Feed both pieces into `mod_cancel_coprime` (Level 6) to finish in one line!

This is exactly the reuse pattern from `mod_mul` back in World 2: build small intermediate facts with `have`, then `exact` the final theorem.
"


/-- The fully general cancellation law for congruences. -/
Statement mod_cancel_general (a b c m d c1 m1 : ℤ) (hd : d ≠ 0) (h1 : (a * c) ≡ (b * c) (mod m)) (h2 : IsGCD(c, m) d) (hc : c = c1 * d) (hm : m = m1 * d) : a ≡ b (mod m1) := by
  have hcoprime := gcd_div_coprime c m d c1 m1 hd h2 hc hm
  unfold ModEq at h1
  obtain ⟨k, hk⟩ := h1
  rw [hc, hm] at hk
  have e : a * (c1 * d) - b * (c1 * d) = d * (a * c1 - b * c1) := by ring
  have e2 : m1 * d * k = d * (m1 * k) := by ring
  rw [e, e2] at hk

  have hk2 : a * c1 - b * c1 = m1 * k := mul_left_cancel₀ hd hk

  Hint (hidden := true) "You have a plain equation now, {a} * {c1} − {b} * {c1} = {m1} * {k}, but mod_cancel_coprime needs an actual congruence, not a bare equation. Wrap it back up: state the congruence, unfold it, and it reduces to exactly the equation you already have."
  have h1' : (a * c1) ≡ (b * c1) (mod m1) := by
    unfold ModEq
    use k

  exact mod_cancel_coprime a b c1 m1 h1' hcoprime

Conclusion "
Incredible! You just built the full cancellation law for modular congruences by gluing together two previous theorems and one careful algebraic cancellation. This is exactly how real number-theory results get assembled from smaller pieces.
"
