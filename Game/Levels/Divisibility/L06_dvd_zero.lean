import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L05_dvd_refl

World "Divisibility"
Level 6
Title "Everything Divides Zero"

Introduction "
A common misconception in standard school math is confusing \"dividing by zero\" (which is undefined) with \"dividing zero\".
Here, we want to prove that any number $a$ *divides* zero.
By our definition, this just means $0 = a \\cdot k$ for some $k$.
"

/-- Any integer divides zero. -/
Statement dvd_zero_int (a : ℤ) : a ∣ 0 := by
  use 0
  ring

Conclusion "
Perfect! Because $a \\cdot 0 = 0$, $a$ always divides $0$.
"
