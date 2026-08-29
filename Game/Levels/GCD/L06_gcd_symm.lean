import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L05_coprime_backward

World "GCD"
Level 6
Title "Symmetry of the GCD"

Introduction "
Before we move on to the cancellation laws, let's prove a very simple but handy property: symmetry.

If $d$ is a greatest common divisor of $a$ and $b$, then it is also a greatest common divisor of $b$ and $a$.
Formally: `IsGCD(a, b) d ⟹  IsGCD(b, a) d`.

You will need to unpack the definition, swap the two divisibility facts, and swap the order of the Bézout coefficients!
"

/-- The GCD is symmetric. -/
Statement gcd_symm (a b d : ℤ) (h : IsGCD(a, b) d) : IsGCD(b, a) d := by
  unfold IsGCD at *
  obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := h
  constructor
  · constructor
    · exact hdb
    · exact hda
  use y, x

  have h_eq : b * y + a * x = a * x + b * y
  · ring

  rw [h_eq, hxy]

Conclusion "
Nice and easy! This lemma will be saved as `gcd_symm`. It will save you from doing boring manual variable-swapping when you tackle the Chinese Remainder Theorem later on.
"
