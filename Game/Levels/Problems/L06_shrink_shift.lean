import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L05_euclid


World "Problems"
Level 6
Title "Shrinking and Shifting (Boss)"

Introduction "
Welcome to the final boss of World 6!

Let's combine multiple theorems into one elegant deduction.
If you know that $x \\equiv 23 \\pmod{100}$, what is the remainder of $x$ when divided by 4?

Since 4 divides 100, we can safely shrink the modulus using `mod_shrink`. This will give us $x \\equiv 23 \\pmod 4$.
But 23 is not a standard remainder! We need to step from 23 down to 3 modulo 4, using `mod_trans`.

This level tests your ability to chain `have` statements and piece together different theorems.
"

Statement (x : ℤ) (h : x ≡ 23 (mod 100)) : x ≡ 3 (mod 4) := by
  have h_div : (4 : ℤ) ∣ 100 := by
    use 25
    ring

  have h_shrink := mod_shrink x 23 100 4 h h_div

  Hint "Prove that 23 is congruent to 3 modulo 4 manually: `have h_23 : 23 ≡ 3 (mod 4)`"
  have h_23 : 23 ≡ 3 (mod 4) := by
    unfold ModEq
    use 5
    ring

  exact mod_trans x 23 3 4 h_shrink h_23

Conclusion "
🎉 CONGRATULATIONS ON COMPLETING THE NUMBER THEORY GAME! 🎉

Masterfully done! You used divisibility to shrink the modulus, manually computed a small remainder, and used transitivity to glue it all together.

This is exactly how number theory problems are solved in practice.

You started from the simplest definition of divisibility and built a massive, formally verified mathematical theory. You conquered congruences, the greatest common divisor, and the Chinese Remainder Theorem — and then used your abstract tools to crush real numerical problems.

Thank you for playing!
"
