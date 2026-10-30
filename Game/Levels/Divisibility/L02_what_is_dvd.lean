import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 2
Title "What exactly does 'divides' mean?"


NewTactic ring

Introduction "
Now let's prove something abstract. We want to prove that 1 divides any integer $a$.

Remember that $1 \\mid a$ means $a = 1 \\cdot k$ for some $k$. What should $k$ be?
Use the `use` tactic, and then close the algebra with our new super-tactic: `ring`.
"


/-- 1 divides every integer. -/
Statement one_dvd_int (a : ℤ) :  1 ∣ a := by
  use a
  ring

Conclusion "
Great job! Notice that this theorem is now saved in your inventory as `one_dvd`!
"
