import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L06_dvd_zero

World "Divisibility"
Level 7
Title "Rewriting"

NewTactic rw

Introduction "
That goal looks terrifying! Fortunately, you don't have to expand those fifth powers by hand.

Look at your hypotheses: `hx : x = 42` and `hy : y = 69`.
You can substitute these values into the goal using the **rewrite** tactic, written `rw`.

Type `rw [hx, hy]` to replace every `x` with `42` and every `y` with `69`. Look closely at what happens to `(x - 42)` and `(y - 69)` on the right-hand side!
"

/-- Substituting known values with rw simplifies a monstrous divisibility goal. -/
Statement (x y : ℤ) (hx : x = 42) (hy : y = 69) :
    (x^5 - y^4 + 17 * x^2 * y - 9999) ∣
      (x^3 * (x - 42) + y^2 * (y - 69)) := by
  rw [hx, hy]
  use 0
  ring

Conclusion "
Crisis averted! Once `rw [hx, hy]` substituted the numbers, the entire right-hand side collapsed into zero, turning a scary polynomial into the simple `a ∣ 0` pattern from the previous level.
"
