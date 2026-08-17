import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L08_cancel_general

World "GCD"
Level 9
Title "A Shift Doesn't Change the GCD (Boss)"

Introduction "
Welcome to the final boss of World 3!

We prove the fact that sits at the heart of the **Euclidean Algorithm**: shifting a number by a multiple of $m$ does not change its greatest common divisor with $m$.

Formulation: if $d_1$ is a (non-negative) gcd of $(a + m \\cdot k)$ and $m$, and $d_2$ is a (non-negative) gcd of $a$ and $m$, then $d_1 = d_2$.

**Lean Syntax Tip:** Before we start, a quick trick! Since `IsGCD` is a nested logical AND (`∧`), you can extract its pieces directly using **dot notation** without destroying the original hypothesis. For example, `h.1.1` gets the very first fact, and `h.1.2` gets the second. Because we will need to pass the intact hypotheses `h1` and `h2` to `gcd_is_greatest` later, using dot notation is safer here than using `obtain`!

**Strategy** (this is a long one — take it one step at a time!):

1. Show $d_1$ is also a common divisor of $a$ and $m$ (not just of $a + m \\cdot k$): since $a = (a + m \\cdot k) - m \\cdot k$, and $d_1$ divides both $(a + mk)$ and $m$, it divides $a$ too. Now $d_1$ is a common divisor of $a$ and $m$, and $d_2$ is *the greatest one* (Level 3!), so $d_1 \\mid d_2$.
2. Symmetrically, show $d_2$ is also a common divisor of $(a + m \\cdot k)$ and $m$: since $d_2$ divides both $a$ and $m$, it divides the combination $a + m \\cdot k$ too. Applying Level 3 again (this time with $d_1$ as \"the greatest\"), you get $d_2 \\mid d_1$.
3. Finally, `d1 ∣ d2` and `d2 ∣ d1`, together with `0 ≤ d1` and `0 ≤ d2`, give `d1 = d2` by the antisymmetry lemma (`Int.dvd_antisymm`) that has just been added to your inventory!
"

/--
**Shift Invariance of the GCD**

For any integers $a, k, m$, and non-negative gcd-witnesses $d_1, d_2$:
if `IsGCD(a + m * k, m) d1` and `IsGCD(a, m) d2`, then $d_1 = d_2$.

**Why this matters:**
This is the *engine* of the Euclidean Algorithm for computing GCDs: $\gcd(a + mk, m) = \gcd(a, m)$ for any integer $k$. In particular, replacing $a$ by its remainder after dividing by $m$ never changes the GCD with $m$ — which is exactly what lets the Euclidean Algorithm shrink its numbers step by step until it reaches the answer.
-/
TheoremDoc gcd_shift_invariant as "gcd_shift_invariant" in "GCD"


/--
**Antisymmetry of Divisibility (for non-negative integers)**

If $0 \le d_1$, $0 \le d_2$, $d_1 \mid d_2$, and $d_2 \mid d_1$, then $d_1 = d_2$.

**Why we need it:**
Divisibility on all of $\mathbb{Z}$ only forms a *pre-order*: two different numbers can divide each other, as long as one is the negative of the other. Restricted to non-negative integers, though, divisibility becomes a genuine **partial order**: "mutual divisibility" really does collapse to equality.

In this boss level, we will show two gcd-witnesses divide each other, and use exactly this theorem to conclude they must be the *same* number.
-/
TheoremDoc Int.dvd_antisymm as "dvd_antisymm" in "Divisibility"

NewTheorem Int.dvd_antisymm

/-- Shifting by a multiple of m does not change the gcd with m. -/
Statement gcd_shift_invariant (a k m d1 d2 : ℤ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (h1 : IsGCD(a + m * k, m) d1) (h2 : IsGCD(a, m) d2) : d1 = d2 := by

  Hint "Start by extracting the four divisibility facts from `{h1}` and `{h2}` using the dot notation explained in the introduction. Create new hypotheses for them using `have`."
  have hd1_amk : d1 ∣ a + m * k := h1.1.1
  have hd1_m : d1 ∣ m := h1.1.2
  have hd2_a : d2 ∣ a := h2.1.1
  have hd2_m : d2 ∣ m := h2.1.2

  Hint "First step: show that `{d1}` divides `{a}`. Think of `{a}` as `({a} + {m} * {k}) - {m} * {k}`."
  have hd1_a : d1 ∣ a := by
    obtain ⟨x, hx⟩ := hd1_amk
    obtain ⟨y, hy⟩ := hd1_m
    use x - y * k
    have h_eq1 : a = (a + m * k) - m * k := by ring
    rw [h_eq1, hx, hy]
    ring

  Hint "Now that you know `{d1} ∣ {a}` and `{d1} ∣ {m}`, use the theorem `gcd_is_greatest` (from Level 3) on `{h2}` to show that `{d1} ∣ {d2}`."
  have hd1_d2 : d1 ∣ d2 := gcd_is_greatest a m d1 d2 h2 hd1_a hd1_m

  Hint "Symmetrically, show `{d2} ∣ {a} + {m} * {k}` using the fact that `{d2} ∣ {a}` and `{d2} ∣ {m}`."
  have hd2_amk : d2 ∣ a + m * k := by
    obtain ⟨x, hx⟩ := hd2_a
    obtain ⟨y, hy⟩ := hd2_m
    use x + y * k
    rw [hx, hy]
    ring

  Hint "Almost there! Apply `gcd_is_greatest` on `{h1}` to show `{d2} ∣ {d1}`."
  have hd2_d1 : d2 ∣ d1 := gcd_is_greatest (a + m * k) m d2 d1 h1 hd2_amk hd2_m

  Hint "You have `{d1} ∣ {d2}` and `{d2} ∣ {d1}`. Finish the boss by applying `Int.dvd_antisymm`!"
  exact Int.dvd_antisymm hd1 hd2 hd1_d2 hd2_d1


Conclusion "
🎉 MAGNIFICENT! 🎉

You have conquered World 3! You built a working theory of the greatest common divisor from a single Bézout-style definition, proved it truly deserves the name \"greatest\", derived the coprime cancellation law — the central tool of the whole game — and finished by proving the very fact that powers the Euclidean Algorithm.

You've mastered nested `obtain`, chained `have`-based lemma reuse, and careful case-by-case algebra. To be continued in World 4, where all of this comes together to solve linear congruences and prove the Chinese Remainder Theorem!
"
