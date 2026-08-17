import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L10_crt_glue

World "LinCong"
Level 11
Title "Polynomial Congruences (Boss)"

Introduction "
Welcome to the Final Boss of the Number Theory Game!

All the tools you have built so far — reflexivity, addition, multiplication, scaling, and powers of congruences — can now be combined into one incredibly powerful result.

If two numbers are congruent modulo $m$ ($a \\equiv b \\pmod m$), then **any polynomial** with integer coefficients evaluated at those numbers will also be congruent modulo $m$.
Let's prove this for a quadratic polynomial: $c_2 a^2 + c_1 a + c_0 \\equiv c_2 b^2 + c_1 b + c_0 \\pmod m$.

Use your theorems from World 2 (`mod_pow`, `mod_add`, `mod_mul_const`, `mod_refl`) to build the polynomial piece by piece!
"

/--
**Polynomial Congruences**

If $a \equiv b \pmod m$, then $P(a) \equiv P(b) \pmod m$ for any integer polynomial $P$.
-/
TheoremDoc polynomial_cong as "polynomial_cong" in "LinCong"

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
🎉 YOU BEAT THE GAME! 🎉

You have masterfully synthesized the properties of modular arithmetic. This implies that integers modulo $m$ form a robust algebraic structure — a ring — where addition and multiplication work flawlessly without breaking the congruences.

Congratulations on completing the Number Theory Game!
"
