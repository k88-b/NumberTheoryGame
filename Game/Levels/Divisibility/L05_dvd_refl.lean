import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L04_one_dvd

World "Divisibility"
Level 5
Title "A Number Divides Itself"

Introduction "
Now let's practice what we just learned. Prove that any integer $a$ divides itself.
Think about what $k$ should be so that $a = a \\cdot k$.
"

/-- Every integer divides itself. -/
Statement dvd_refl_int (a : ℤ) : a ∣ a := by
  use 1
  ring

Conclusion "
Nice! You are starting to recognize patterns — we call this property **reflexivity** (`dvd_refl_int`).
"
