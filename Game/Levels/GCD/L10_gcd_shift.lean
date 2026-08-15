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
if `gcd((a + m * k), m) = d1` and ` gcd(a, m) = d2`, then $d_1 = d_2$.

**Why this matters:**
This is the *engine* of the Euclidean Algorithm for computing GCDs: $\gcd(a + mk, m) = \gcd(a, m)$ for any integer $k$. In particular, replacing $a$ by its remainder after dividing by $m$ never changes the GCD with $m$ — which is exactly what lets the Euclidean Algorithm shrink its numbers step by step until it reaches the answer.
-/
TheoremDoc gcd_shift_invariant as "gcd_shift_invariant" in "GCD"

/-- Shifting by a multiple of m does not change the gcd with m. -/
Statement gcd_shift_invariant (a k m d1 d2 : ℤ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (h1 : gcd((a + m * k), m)= d1) (h2 : gcd(a, m)= d2) : d1 = d2 := by
  have hcopy1 := h1
  have hcopy2 := h2
  unfold IsGCD at hcopy1
  unfold IsGCD at hcopy2
  obtain ⟨⟨hd1s, hd1m⟩, _⟩ := hcopy1
  obtain ⟨⟨hd2a, hd2m⟩, _⟩ := hcopy2
  obtain ⟨p, hp⟩ := hd1s
  obtain ⟨q, hq⟩ := hd1m
  have hd1a : d1 ∣ a := by
    use p - q * k
    have e : a = (a + m * k) - m * k := by ring
    rw [e]
    rw [hp, hq]
    ring
  have hle1 : d1 ∣ d2 := gcd_is_greatest a m d1 d2 h2 hd1a hd1m
  obtain ⟨p2, hp2⟩ := hd2a
  obtain ⟨q2, hq2⟩ := hd2m
  have hd2s : d2 ∣ (a + m * k) := by
    use p2 + q2 * k
    rw [hp2, hq2]
    ring
  have hle2 : d2 ∣ d1 := gcd_is_greatest (a + m * k) m d2 d1 h1 hd2s hd2m
  exact dvd_antisymm d1 d2 hd1 hd2 hle1 hle2

Conclusion "
🎉 MAGNIFICENT! 🎉

You have conquered World 3! You built a working theory of the greatest common divisor from a single Bézout-style definition, proved it truly deserves the name \"greatest\", derived the coprime cancellation law — the central tool of the whole game — and finished by proving the very fact that powers the Euclidean Algorithm.

You've mastered nested `obtain`, chained `have`-based lemma reuse, and careful case-by-case algebra. Get ready for World 4, where all of this comes together to solve linear congruences and prove the Chinese Remainder Theorem!
"
