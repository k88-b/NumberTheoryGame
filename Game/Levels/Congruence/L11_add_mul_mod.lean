import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L10_mul

World "Congruence"
Level 11
Title "Shifting by the Modulus"

Introduction "
In modular arithmetic, the modulus $m$ essentially acts like zero. That means adding or subtracting any multiple of $m$ to a number doesn't change its remainder at all:
$$a + k \\cdot m \\equiv a \\pmod m$$

It's a quick, refreshing lemma after the heavy lifting of multiplication, and one we will rely on later!
"


/-- Shifting a number by a multiple of m. -/
Statement mod_add_multiple (a k m : ℤ) : (a + k * m) ≡ a (mod m) := by
  unfold ModEq
  use k
  ring

Conclusion "
Short and sweet. This fact will be a lifesaver when we reach linear congruences in World 4!
"
