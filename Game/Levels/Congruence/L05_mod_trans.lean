import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L04_mod_symm

World "Congruence"
Level 5
Title "Transitivity of Congruences"

Introduction "
The final pillar of an equivalence relation is **transitivity**:
If $a \\equiv b \\pmod m$ and $b \\equiv c \\pmod m$, then $a \\equiv c \\pmod m$.

This is the property that allows us to chain long sequences of congruences together, stepping from one expression to the next just like we do with standard equalities.
"


/-- Congruence modulo m is transitive. -/
Statement mod_trans (a b c m : ℤ) (h1 : a ≡ b (mod m)) (h2 : b ≡ c (mod m)) : a ≡ c (mod m) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  Hint (hidden := true) "You know a − b = m * {k1} and b − c = m * {k2}. Add those two equations: a − c = m * ({k1} + {k2}). So the multiplier you need combines {k1} and {k2} by addition."
  use k1 + k2

  have h_eq : a - c = (a - b) + (b - c)
  · ring

  rw [h_eq, hk1, hk2]
  ring

Conclusion "
Excellent! Reflexivity, symmetry, and transitivity are now complete — congruence modulo $m$ is officially an equivalence relation.
"
