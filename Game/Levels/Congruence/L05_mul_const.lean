import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L04_add

World "Congruence"
Level 5
Title "Multiplying by a Common Factor"

Introduction "
Next, let's prove that we can multiply both sides of a congruence by any integer $c$.
If $a \\equiv b \\pmod m$, then $a \\cdot c \\equiv b \\cdot c \\pmod m$.

This is a direct application of what you already know.
Rewrite $a \\cdot c - b \\cdot c$ as $(a - b) \\cdot c$ and close the goal!
"


/-- Multiplying a congruence by a constant. -/
Statement mod_mul_const (a b c m : ℤ) (h : a ≡ b (mod m)) : (a * c) ≡ (b * c) (mod m) := by
  unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use k * c

  have h_eq : a * c - b * c = (a - b) * c
  · ring

  rw [h_eq, hk]
  ring


Conclusion "
Very smooth. Keep this theorem (`mod_mul_const`) in mind, it will be very useful!
"
