import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L06_add_mul_mod

World "Congruence"
Level 7
Title "Scaling the Modulus"

Introduction "
So far, the modulus $m$ has stayed fixed. What if we want to change the modulus $m$ itself?

If $a \\equiv b \\pmod m$, then multiplying everything (including the modulus) by $c$ preserves the congruence:
$$a \\cdot c \\equiv b \\cdot c \\pmod{m \\cdot c}$$

Unfold the definition and look closely at the algebra.
"


/-- Scaling the modulus. -/
Statement mod_scale (a b c m : ℤ) (h : a ≡ b (mod m)) : (a * c) ≡ (b * c) (mod (m * c)) := by
  unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use k

  have h_eq : a * c - b * c = (a - b) * c
  · ring

  rw [h_eq, hk]
  ring

Conclusion "
Nice! Notice how the witness $k$ didn't even need to change!
"
