import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 3
Title "A number divides itself"

Introduction "
Now let's practice what we just learned. Prove that any integer $a$ divides itself.
Think about what $k$ should be so that $a = a \\cdot k$.
"

/-- Divisibility is reflexive: `a ∣ a`. -/
TheoremDoc dvd_refl as "dvd_refl" in "Divisibility"

/-- Every integer divides itself. -/
Statement dvd_refl (a : ℤ) : a ∣ a := by
  use 1
  ring


Conclusion "
Easy, right? You are starting to recognize patterns. We call this property 'reflexivity'.
"
