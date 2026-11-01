import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L06_add

World "Congruence"
Level 7
Title "Subtracting Congruences"

Introduction "
Where addition goes, subtraction follows. If $a \\equiv b \\pmod m$ and $c \\equiv d \\pmod m$, then:
$$a - c \\equiv b - d \\pmod m$$

This rule is what lets us move terms from one side of a congruence to the other, just like in standard equations.
"

/-- Subtracting congruences modulo m. -/
Statement mod_sub (a b c d m : ℤ) (h1 : a ≡ b (mod m)) (h2 : c ≡ d (mod m)) : (a - c) ≡ (b - d) (mod m) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k1 - k2

  have h_eq : (a - c) - (b - d) = (a - b) - (c - d)
  · ring

  rw [h_eq, hk1, hk2]
  ring

Conclusion "
Nicely done! Subtraction is just addition in disguise, and modular arithmetic handles it effortlessly.
"
