import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L06_mul

World "Congruence"
Level 7
Title "Shifting by the Modulus"

Introduction "
Here is a very simple but incredibly important rule.
If you add any multiple of the modulus $m$ to a number $a$, its remainder doesn't change!
$a + k \\cdot m \\equiv a \\pmod m$.

Try to prove this directly by unfolding the definition.
"


/-- Shifting a number by a multiple of m. -/
Statement mod_add_multiple (a k m : ℤ) : (a + k * m) ≡ a (mod m) := by
  unfold ModEq
  use k
  ring

Conclusion "
Short and sweet. This fact will be a lifesaver when we reach the Chinese Remainder Theorem in World 4!
"
