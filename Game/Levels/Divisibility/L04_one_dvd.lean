import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L03_dvd_mul_right

World "Divisibility"
Level 4
Title "One Divides Everything"

Introduction "
Next, let's prove that $1$ divides any integer $a$.

Remember that $1 \\mid a$ means $a = 1 \\cdot k$ for some $k$. What should $k$ be?

Unlike the previous level, after you `use` your witness, the two sides of the equation ($a$ and $1 \\cdot a$) won't look syntactically identical to Lean. Close the algebra using `ring`!
"

/-- 1 divides every integer. -/
Statement one_dvd_int (a : ℤ) : 1 ∣ a := by
  use a
  ring

Conclusion "
Great job! Whenever `use` leaves you with an algebraic identity like $a = 1 \\cdot a$, `ring` cleans it right up. `one_dvd_int` is now added to your toolkit!
"
