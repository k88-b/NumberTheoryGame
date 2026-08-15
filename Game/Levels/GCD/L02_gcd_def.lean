import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L01_dvd_mul

World "GCD"
Level 2
Title "Meeting the GCD"

/--
**The Greatest Common Divisor, Bézout-style**

In this game, we say $d$ **is a greatest common divisor** of $a$ and $b$ — written `IsGCD a b d` — if **two** conditions hold together:

1. $d$ is a **common divisor**: $d \mid a$ and $d \mid b$.
2. $d$ can be written as a **Bézout combination**: there exist integers $x, y$ such that $a \cdot x + b \cdot y = d$.

$$\text{IsGCD}(a, b, d) \iff (d \mid a \land d \mid b) \land \exists x, y \in \mathbb{Z},\ a x + b y = d$$

**Why this definition, and not simply "the largest common divisor"?**
Working with "largest" directly is awkward in Lean: comparing sizes doesn't play well with negative numbers, and proving something is *the* biggest usually means comparing it to every other common divisor one at a time.

The Bézout condition sidesteps all of that. It turns out (and you will prove it in the very next level!) that *any* $d$ satisfying condition 2, together with condition 1, is automatically bigger than every other common divisor — for free, with a short proof. So instead of taking "greatest" as the definition, we derive it as a theorem.

**A word of caution:** this definition alone does not force $d \geq 0$ or force $d$ to be unique. In this game we will always keep a specific, non-negative witness in mind (for example `gcd(2, 3) = 1`, never `gcd(2, 3) = (-1)`, even though $-1$ also happens to satisfy the Bézout condition for $2$ and $3$, up to sign).
-/
DefinitionDoc IsGCD as "gcd(a, b) = d"

NewDefinition IsGCD

Introduction "
Time to meet the star of this world: the **Greatest Common Divisor**.

Instead of defining $\\gcd(a,b)$ as \"the largest number that divides both\", we use an equivalent but far more Lean-friendly definition, based on **Bézout's identity**. Check the **Definitions** tab for the full explanation!

As a warm-up, let's confirm that $1$ is a greatest common divisor of $2$ and $3$: `gcd(2, 3) = 1`.

Start with `unfold IsGCD` to reveal the raw conjunction. Your goal is then an `∧` of an `∧` and an `∃`. You already know `constructor` splits an `∧` into two goals — you'll need it *twice*, since the first part (`d ∣ a ∧ d ∣ b`) is itself a conjunction.

For the two divisibility goals, `use` the right witness and close with `ring` (remember: `ring` happily proves concrete numeric equalities too, not just general algebraic ones!). For the Bézout goal, `use -1, 1` to supply $x = -1$ and $y = 1$ at once, then `ring` again to check $2 \\cdot (-1) + 3 \\cdot 1 = 1$.
"

/-- 1 is a greatest common divisor of 2 and 3. -/
TheoremDoc gcd_two_three as "gcd_two_three" in "GCD"

/-- A first, concrete example: gcd(2, 3) = 1. -/
Statement gcd_two_three : gcd(2,3)= 1 := by
  unfold IsGCD
  constructor
  · constructor
    · use 2
      ring
    · use 3
      ring
  · use -1, 1
    ring

Conclusion "
Well done! You built a proof of a conjunction-inside-a-conjunction by nesting `constructor`. Next, let's see why this definition really deserves the name \"greatest\" common divisor.
"
