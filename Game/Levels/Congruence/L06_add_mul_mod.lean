import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L05_mod_trans

World "Congruence"
Level 6
Title "Shifting by the Modulus"

Introduction "
In modular arithmetic, the modulus $m$ essentially acts like zero. That means adding or subtracting any multiple of $m$ to a number doesn't change its remainder at all:
$$a + k \\cdot m \\equiv a \\pmod m$$

Let's prove this fundamental shifting rule!
"


/-- Shifting a number by a multiple of m. -/
Statement mod_add_multiple (a k m : ℤ) : (a + k * m) ≡ a (mod m) := by
  unfold ModEq
  use k
  ring

Conclusion "
Short and sweet. This fact (`mod_add_multiple`) will be a lifesaver when we prove divisibility rules and solve linear congruences!
"
