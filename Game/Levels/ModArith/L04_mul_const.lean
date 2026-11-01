import GameServer
import Mathlib.Tactic
import Game.Levels.ModArith.L03_add_const

World "ModArith"
Level 4
Title "Multiplying by a Common Factor"

Introduction "
Now let's move from addition to multiplication. As a first step, let's show that we can scale both sides of a congruence by any integer $c$:
If $a \\equiv b \\pmod m$, then $a \\cdot c \\equiv b \\cdot c \\pmod m$.

This simple scaling rule will be our stepping stone to multiplying any two congruences together in the next level.
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
Very smooth. Keep `mod_mul_const` in mind — you're going to put it to work right now!
"
