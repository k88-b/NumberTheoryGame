import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L10_multiples_of_6

World "Divisibility"
Level 11
Title "A Divisor of a Factor Divides the Product"

Introduction "
Let's generalize the trick from the previous level into a universal building block.

If $d$ divides $a$, does $d$ also divide $a \\cdot b$ for *any* integer $b$?
Yes! If $a$ is a multiple of $d$, then any multiple of $a$ is automatically a multiple of $d$ too.

You already have the exact four-step rhythm you need: `obtain` the witness from your hypothesis, `use` the right scaled witness for the new goal, `rw`, and finish with `ring`.
"

/-- If d divides a, then d divides a * b for any integer b. -/
Statement dvd_mul_of_dvd_left_int (a b d : ℤ) (h : d ∣ a) : d ∣ (a * b) := by
  obtain ⟨k, hk⟩ := h
  Hint (hidden := true) "Once you know `a = d * k`, substituting into `a * b` gives `d * (k * b)`. So the multiplier the goal is asking for is your existing `k`, scaled by `b`."
  use k * b
  rw [hk]
  ring

Conclusion "
Perfect! Keep `dvd_mul_of_dvd_left_int` close at hand — you'll use this theorem again and again in future worlds.
"
