import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L02_negative_multiples

World "Divisibility"
Level 3
Title "Multiples of a"

Introduction "
Now let's move from concrete numbers to abstract integers $a$ and $b$.

We want to prove that $a$ divides $a \\cdot b$. By definition, this means finding some $k$ such that $a \\cdot b = a \\cdot k$.
Look closely at the equation — the witness $k$ is hiding in plain sight!
"

/-- Any integer a divides a * b. -/
Statement dvd_mul_right_int (a b : ℤ) : a ∣ a * b := by
  use b

Conclusion "
Easy! Since substituting $b$ for $k$ makes both sides of $a \\cdot b = a \\cdot b$ completely identical, `use b` closes the goal immediately.

**New Theorem Unlocked!** Whenever you prove a general statement like this, it is saved in your **Theorems** tab on the right (this one is called `dvd_mul_right_int`). Take a look at the **Theorems** tab now — you can click on any theorem there to read its documentation and see how to reuse it in future proofs!
"
