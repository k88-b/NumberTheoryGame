import GameServer
import Mathlib.Tactic
import Game.Metadata
import Game.Levels.Definitions
import Game.Doc.Definitions
import Game.Doc.Tactics
import Game.Doc.Theorems.Congruence

import Game.Levels.Divisibility
import Game.Levels.Divisors
import Game.Levels.Congruence

World "ModArith"
Level 1
Title "Adding Congruences"

Introduction "
Knowing that $\\equiv$ is an equivalence relation is great, but the real magic of modular arithmetic is that it respects **algebraic operations**.

First up is addition: if $a \\equiv b \\pmod m$ and $c \\equiv d \\pmod m$, then we can add the two congruences side-by-side:
$$a + c \\equiv b + d \\pmod m$$
"


/-- If two pairs of numbers are congruent, their sums are congruent. -/
Statement mod_add (a b c d m : ℤ) (h1 : a ≡ b (mod m)) (h2 : c ≡ d (mod m)) : (a + c) ≡ (b + d) (mod m) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k1 + k2

  have h_eq : (a + c) - (b + d) = (a - b) + (c - d)
  · ring

  rw [h_eq, hk1, hk2]
  ring

Conclusion "
Excellent! You just proved your first arithmetic rule for congruences.
"
