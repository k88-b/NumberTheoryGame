import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L05_pow

World "Congruence"
Level 6
Title "Scaling the Modulus"

Introduction "
So far, we have only changed the numbers $a$ and $b$. But what if we want to change the modulus $m$ itself?

If $a \\equiv b \\pmod m$, then multiplying everything (including the modulus) by $c$ preserves the truth of the statement:
$a \\cdot c \\equiv b \\cdot c \\pmod{m \\cdot c}$.

Unfold the definition and look closely at the algebra.
"

/-- You can multiply the modulus and the values by a constant. -/
TheoremDoc mod_scale as "mod_scale" in "Congruence"

/-- Scaling the modulus. -/
Statement mod_scale (a b c m : ℤ) (h : a ≡ b (mod m)) : (a * c) ≡ (b * c) (mod (m * c)) := by
  unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use k
  have h_eq : a * c - b * c = (a - b) * c := by ring
  rw [h_eq]
  rw [hk]
  ring

Conclusion "
Nice! Notice how the witness $k$ didn't even need to change!
"
