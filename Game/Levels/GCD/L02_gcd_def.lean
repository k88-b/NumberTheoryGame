import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L01_dvd_mul

World "GCD"
Level 2
Title "Meeting the GCD"

NewDefinition IsGCD

Introduction "
Time to meet the star of this world: the **Greatest Common Divisor**.

Instead of defining $\\text{IsGCD}(a,b)$ as \"the largest number that divides both\", we use an equivalent but far more Lean-friendly definition, based on **Bézout's identity**. Check the **Definitions** tab for the full explanation!

As a warm-up, let's confirm that $1$ is a greatest common divisor of $2$ and $3$: `IsGCD(2, 3) 1`.

Start with `unfold IsGCD` to reveal the raw conjunction. Your goal is then an `∧` of an `∧` and an `∃`. You already know `constructor` splits an `∧` into two goals — you'll need it *twice*, since the first part (`d ∣ a ∧ d ∣ b`) is itself a conjunction.

For the two divisibility goals, `use` the right witness and close with `ring` (remember: `ring` happily proves concrete numeric equalities too, not just general algebraic ones!). For the Bézout goal, `use -1, 1` to supply $x = -1$ and $y = 1$ at once, then `ring` again to check $2 \\cdot (-1) + 3 \\cdot 1 = 1$.
"

/-- 1 is a greatest common divisor of 2 and 3. -/
TheoremDoc gcd_two_three as "gcd_two_three" in "GCD"

/-- A first, concrete example: IsGCD(2, 3) 1. -/
Statement gcd_two_three : IsGCD(2, 3) 1 := by
  unfold IsGCD
  Hint "Your goal is an `∧` (AND). Use the `constructor` tactic to split it into two separate goals."
  constructor
  · Hint "The first goal is *also* an `∧`. Use `constructor` again!"
    constructor
    · use 2
      ring
    · use 3
      ring
  · Hint (hidden := true) "To show `2 * x + 3 * y = 1`, try `x = -1` and `y = 1`. Type `use -1, 1`."
    use -1, 1
    ring

Conclusion "
Well done! You built a proof of a conjunction-inside-a-conjunction by nesting `constructor`. Next, let's see why this definition really deserves the name \"greatest\" common divisor.
"
