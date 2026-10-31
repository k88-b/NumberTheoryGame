import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L07_rewriting

World "Divisibility"
Level 8
Title "Rewriting Backwards"

Introduction "
By default, `rw [h]` replaces the left-hand side of an equation `h` with its right-hand side.

Here, our hypothesis is `h : a * k = b`, and our goal is `a ∣ b`.
If we want to replace `b` in the goal with `a * k`, we need to rewrite **backwards** (from right to left).

You can do this by putting a left arrow before the hypothesis name: `rw [← h]`.

*(To type `←`, write `\\l` and press Space.)*
"

/-- If a * k = b, then a divides b. -/
Statement dvd_intro_int (a b k : ℤ) (h : a * k = b) : a ∣ b := by
  rw [← h]
  use k

Conclusion "
Nicely done! Rewriting backwards with `rw [← h]` turned the goal into `a ∣ a * k`, where `use k` could finish it in one step.
"
