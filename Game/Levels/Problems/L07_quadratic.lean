import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L06_shrink_shift

World "Problems"
Level 7
Title "Quadratic Congruence"

Introduction "
Let's evaluate a polynomial congruence based on multiple moduli.

If $x \\equiv 2 \\pmod 5$ and $x \\equiv 3 \\pmod 7$, can you prove that $x^2 - 5x + 6 \\equiv 0 \\pmod{35}$?
"

Statement (x : ℤ) (h1 : x ≡ 2 (mod 5)) (h2 : x ≡ 3 (mod 7)) : (x^2 - 5*x + 6) ≡ 0 (mod 35) := by
  Hint "There are two paths to solve this: a short one and a long one. It is worth thinking a bit about algebraic transformations."
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2

  have h : x^2 - 5*x + 6 = (x - 2) * (x - 3)
  · ring

  rw [h, hk1, hk2]
  use k1 * k2
  ring

Conclusion "
Brilliant!

Whether you used clever algebra to factor the polynomial, or applied the heavy machinery of the Chinese Remainder Theorem, you proved you can handle complex congruences. Both paths are perfectly valid!

Now, take a deep breath. Only one challenge remains...
"
