import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L13_mod_scale

World "Congruence"
Level 14
Title "Shrinking the Modulus"

Introduction "
Think of a 12-hour clock: if two events happen at the same hour on a 12-hour cycle, they also line up on a 6-hour or 4-hour cycle.

In general, if $a \\equiv b \\pmod m$, then $a$ and $b$ remain congruent modulo any divisor $d$ of $m$:
$$d \\mid m \\implies a \\equiv b \\pmod d$$
"


/-- Decreasing the modulus to a divisor. -/
Statement mod_shrink (a b m d : ℤ) (h1 : a ≡ b (mod m)) (h2 : d ∣ m) : a ≡ b (mod d) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k2 * k1
  rw [hk1, hk2]
  ring

Conclusion "
Beautiful. You can always step down from a modulus to any of its divisors.
"
