import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L10_crt_glue

World "LinCong"
Level 11
Title "Polynomial Congruences (Victory Lap)"

Introduction "
You did it — the mountain of linear congruences is behind you. This last level of the world isn't here to test you; it's a victory lap.

All the tools you've built — reflexivity, addition, multiplication, scaling, and powers of congruences — combine into one satisfying finishing move: if $a \\equiv b \\pmod m$, then **any** polynomial with integer coefficients evaluated at $a$ and $b$ stays congruent modulo $m$ too.

Let's prove it for a quadratic: $c_2 a^2 + c_1 a + c_0 \\equiv c_2 b^2 + c_1 b + c_0 \\pmod m$.

Nothing new to invent here — just snap together `mod_pow`, `mod_add`, `mod_mul_const`, and `mod_refl` from World 2, piece by piece, and enjoy watching it all just... work.
"


Statement polynomial_cong (a b c0 c1 c2 m : ℤ) (h : a ≡ b (mod m)) : (c2 * a^2 + c1 * a + c0) ≡ (c2 * b^2 + c1 * b + c0) (mod m) := by
  have h_pow2 : (a^2) ≡ (b^2) (mod m) := mod_pow a b m 2 h
  have h_term2_swap : (a^2 * c2) ≡ (b^2 * c2) (mod m) := mod_mul_const (a^2) (b^2) c2 m h_pow2
  have h_term2 : (c2 * a^2) ≡ (c2 * b^2) (mod m) := by
    have hrw1 : c2 * a^2 = a^2 * c2 := by ring
    have hrw2 : c2 * b^2 = b^2 * c2 := by ring
    rw [hrw1, hrw2]
    exact h_term2_swap

  have h_term1_swap : (a * c1) ≡ (b * c1) (mod m) := mod_mul_const a b c1 m h
  have h_term1 : (c1 * a) ≡ (c1 * b) (mod m) := by
    have hrw1 : c1 * a = a * c1 := by ring
    have hrw2 : c1 * b = b * c1 := by ring
    rw [hrw1, hrw2]
    exact h_term1_swap

  have h_term0 : c0 ≡ c0 (mod m) := mod_refl c0 m

  have h_sum12 := mod_add (c2 * a^2) (c2 * b^2) (c1 * a) (c1 * b) m h_term2 h_term1
  exact mod_add (c2 * a^2 + c1 * a) (c2 * b^2 + c1 * b) c0 c0 m h_sum12 h_term0


Conclusion "
🎉 Congratulations on completing World 4! 🎉

And there it is — modular arithmetic behaving exactly like a ring should!

Next up is World 5 (Divisibility Rules). Think of it as a short breather after the heavy lifting of linear congruences, and a perfect preparation for the final practical challenges ahead. You get to sit back, relax, and watch how these high-level theorems effortlessly crush the classical math rules you learned in school.
"

