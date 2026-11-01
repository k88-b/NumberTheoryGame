import GameServer
import Mathlib.Tactic
import Game.Levels.ModArith.L06_pow

World "ModArith"
Level 7
Title "Polynomial Congruences (Boss)"

Introduction "
Welcome to the final boss of Modular Arithmetic!

All the tools you've built — reflexivity, addition, scaling, and powers of congruences — combine into one satisfying finishing move: if $a \\equiv b \\pmod m$, then **any** polynomial with integer coefficients evaluated at $a$ and $b$ stays congruent modulo $m$ too.

Let's prove it for a quadratic: $c_2 a^2 + c_1 a + c_0 \\equiv c_2 b^2 + c_1 b + c_0 \\pmod m$.

Nothing new to invent here — just snap together `mod_pow`, `mod_add`, `mod_mul_const`, and `mod_refl` piece by piece, and enjoy watching it all just... work.
"

/-- Polynomials preserve congruences. -/
Statement polynomial_cong (a b c0 c1 c2 m : ℤ) (h : a ≡ b (mod m)) : (c2 * a^2 + c1 * a + c0) ≡ (c2 * b^2 + c1 * b + c0) (mod m) := by
  have h_pow2 : (a^2) ≡ (b^2) (mod m)
  · exact mod_pow a b m 2 h

  have h_term2_swap : (a^2 * c2) ≡ (b^2 * c2) (mod m)
  · exact mod_mul_const (a^2) (b^2) c2 m h_pow2

  have h_term2 : (c2 * a^2) ≡ (c2 * b^2) (mod m)
  · have hrw1 : c2 * a^2 = a^2 * c2
    · ring
    have hrw2 : c2 * b^2 = b^2 * c2
    · ring
    rw [hrw1, hrw2]
    exact h_term2_swap

  have h_term1_swap : (a * c1) ≡ (b * c1) (mod m)
  · exact mod_mul_const a b c1 m h

  have h_term1 : (c1 * a) ≡ (c1 * b) (mod m)
  · have hrw1 : c1 * a = a * c1
    · ring
    have hrw2 : c1 * b = b * c1
    · ring
    rw [hrw1, hrw2]
    exact h_term1_swap

  have h_term0 : c0 ≡ c0 (mod m)
  · exact mod_refl c0 m

  have h_sum12 : ((c2 * a^2) + (c1 * a)) ≡ ((c2 * b^2) + (c1 * b)) (mod m)
  · exact mod_add (c2 * a^2) (c2 * b^2) (c1 * a) (c1 * b) m h_term2 h_term1

  exact mod_add (c2 * a^2 + c1 * a) (c2 * b^2 + c1 * b) c0 c0 m h_sum12 h_term0


Conclusion "
🎉 AMAZING! 🎉

You have conquered Modular Arithmetic! You've built a complete algebraic toolkit for congruences and proved `polynomial_cong`.

Next up in this branch is **Divisibility Rules**, where you will see how `polynomial_cong`, `mod_shrink`, and `mod_add_multiple` turn the famous school divisibility rules for 2, 3, 4, 5, 9, 10, and 11 into two-line proofs!
"
