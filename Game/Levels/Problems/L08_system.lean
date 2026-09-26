import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L07_quadratic


World "Problems"
Level 8
Title "System of Congruences (Boss)"

Introduction "
Welcome to the final boss of World 6!

In this battle, you are given a system of congruences:
$3x + 4y \\equiv 0 \\pmod{11}$
$4x - 3y \\equiv 0 \\pmod{11}$

You must prove that $x \\equiv 0 \\pmod{11}$.

To win this battle, you only need two key ideas: figure out how to eliminate $y$, and think about what you need to apply `euclids_lemma`.
"

Statement (x y : ℤ) (h1 : (3 * x + 4 * y) ≡ 0 (mod 11)) (h2 : (4 * x - 3 * y) ≡ 0 (mod 11)) : x ≡ 0 (mod 11) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩:= h1
  obtain ⟨k2,hk2⟩ := h2

  have h4: 11 ∣ (x * 25)
  · use 3 * k1 + 4 * k2

    have h: 11 * (3 * k1 + 4 * k2) = (11 * k1) * 3 + (11 * k2) * 4
    · ring

    rw [h, ← hk1, ← hk2]
    ring

  have h_coprime : IsGCD 25 11 1
  · unfold IsGCD
    constructor
    · constructor
      · exact one_dvd 25
      · exact one_dvd 11

    · use 4, -9
      ring

  have h: x - 0 = x
  · ring

  rw [h]

  exact euclids_lemma x 25 11  h4 h_coprime


Conclusion "
🎉 CONGRATULATIONS ON COMPLETING THE NUMBER THEORY GAME! 🎉

You have defeated the final boss by elegantly solving a system of congruences and applying Euclid's Lemma!

You started from the simplest definition of divisibility and built a massive, formally verified mathematical theory. You conquered congruences, the greatest common divisor, and the Chinese Remainder Theorem — and then used your abstract tools to crush real numerical problems.

Thank you for playing!
"
