import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L09_dvd_antisymm

World "GCD"
Level 10
Title "A Shift Doesn't Change the GCD (Boss)"

Introduction "
Welcome to the final boss of World 3!

We prove the fact that sits at the heart of the **Euclidean Algorithm**: shifting a number by a multiple of $m$ does not change its greatest common divisor with $m$.

Formulation: if $d_1$ is a (non-negative) gcd of $(a + m \\cdot k)$ and $m$, and $d_2$ is a (non-negative) gcd of $a$ and $m$, then $d_1 = d_2$.

**Strategy** (this is a long one — take it one step at a time!):

1. Show $d_1$ is also a common divisor of $a$ and $m$ (not just of $a + m \\cdot k$): since $a = (a + m \\cdot k) - m \\cdot k$, and $d_1$ divides both $(a + mk)$ and $m$, it divides $a$ too. Now $d_1$ is a common divisor of $a$ and $m$, and $d_2$ is *the greatest one* (Level 3!), so $d_1 \\mid d_2$.
2. Symmetrically, show $d_2$ is also a common divisor of $(a + m \\cdot k)$ and $m$: since $d_2$ divides both $a$ and $m$, it divides the combination $a + m \\cdot k$ too. Applying Level 3 again (this time with $d_1$ as \"the greatest\"), you get $d_2 \\mid d_1$.
3. Finally, `d1 ∣ d2` and `d2 ∣ d1`, together with `0 ≤ d1` and `0 ≤ d2`, give `d1 = d2` by the antisymmetry lemma from the previous level!
"

/--
**Shift Invariance of the GCD**

For any integers $a, k, m$, and non-negative gcd-witnesses $d_1, d_2$:
if `IsGCD(a + m * k, m) d1` and `IsGCD(a, m) d2`, then $d_1 = d_2$.

**Why this matters:**
This is the *engine* of the Euclidean Algorithm for computing GCDs: $\gcd(a + mk, m) = \gcd(a, m)$ for any integer $k$. In particular, replacing $a$ by its remainder after dividing by $m$ never changes the GCD with $m$ — which is exactly what lets the Euclidean Algorithm shrink its numbers step by step until it reaches the answer.
-/
TheoremDoc gcd_shift_invariant as "gcd_shift_invariant" in "GCD"
NewTheorem Int.dvd_antisymm

/-- Shifting by a multiple of m does not change the gcd with m. -/
Statement gcd_shift_invariant (a k m d1 d2 : ℤ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (h1 : IsGCD((a + m * k), m) d1) (h2 : IsGCD(a, m) d2) : d1 = d2 := by

  unfold IsGCD at h1 h2

  have hd1_amk : d1 ∣ a + m * k := h1.1.1
  have hd1_m : d1 ∣ m := h1.1.2
  have h_bez1 : ∃ x y : ℤ, (a + m * k) * x + m * y = d1 := h1.2

  have hd2_a : d2 ∣ a := h2.1.1
  have hd2_m : d2 ∣ m := h2.1.2
  have h_bez2 : ∃ x y : ℤ, a * x + m * y = d2 := h2.2

  have hd1_a : d1 ∣ a := by
    obtain ⟨k1, hk1⟩ := hd1_amk
    obtain ⟨k2, hk2⟩ := hd1_m
    use k1 - k2 * k
    have h_eq1 : a = (a + m * k) - m * k := by ring
    rw [h_eq1, hk1, hk2]
    ring

  have hd1_d2 : d1 ∣ d2 := by
    obtain ⟨x2, y2, h_eq2⟩ := h_bez2
    obtain ⟨ka, hka⟩ := hd1_a
    obtain ⟨km, hkm⟩ := hd1_m
    use ka * x2 + km * y2
    rw [← h_eq2, hka, hkm]
    ring

  have hd2_amk : d2 ∣ a + m * k := by
    obtain ⟨k3, hk3⟩ := hd2_a
    obtain ⟨k4, hk4⟩ := hd2_m
    use k3 + k4 * k
    rw [hk3, hk4]
    ring

  have hd2_d1 : d2 ∣ d1 := by
    obtain ⟨x1, y1, h_eq1⟩ := h_bez1
    obtain ⟨ka2, hka2⟩ := hd2_amk
    obtain ⟨km2, hkm2⟩ := hd2_m
    use ka2 * x1 + km2 * y1
    rw [← h_eq1, hka2, hkm2]
    ring

  exact Int.dvd_antisymm hd1 hd2 hd1_d2 hd2_d1

Conclusion "
🎉 MAGNIFICENT! 🎉

You have conquered World 3! You built a working theory of the greatest common divisor from a single Bézout-style definition, proved it truly deserves the name \"greatest\", derived the coprime cancellation law — the central tool of the whole game — and finished by proving the very fact that powers the Euclidean Algorithm.

You've mastered nested `obtain`, chained `have`-based lemma reuse, and careful case-by-case algebra. Get ready for World 4, where all of this comes together to solve linear congruences and prove the Chinese Remainder Theorem!
"
