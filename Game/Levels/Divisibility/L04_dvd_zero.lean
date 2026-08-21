import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 4
Title "Everything divides zero"

Introduction "
A common misconception in standard school math is confusing \"dividing by zero\" (which is undefined) with \"dividing zero\".
Here, we want to prove that any number $a$ *divides* zero.
By our definition, this just means $0 = a \\cdot k$ for some $k$.
"


/-- Any integer divides zero. -/
Statement dvd_zero (a : ℤ) : a ∣ 0 := by
  use 0
  ring

Conclusion "
Perfect! Because $a \\cdot 0 = 0$, $a$ always divides 0.
"
