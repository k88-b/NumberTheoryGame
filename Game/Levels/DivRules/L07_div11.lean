import GameServer
import Mathlib.Tactic
import Game.Levels.DivRules.L06_div3

World "DivRules"
Level 7
Title "Divisibility by 11 (Boss)"

Introduction "
For our final trick: the alternating sum of digits rule for 11.
A number is divisible by 11 if $c_0 - c_1 + c_2 - c_3 \\dots$ is divisible by 11.

Why does this work? Because $10 \\equiv -1 \\pmod{11}$.
When we evaluate the \"polynomial\" of the digits ($c_2 \\cdot 10^2 + c_1 \\cdot 10 + c_0$) at -1 instead of 10, the powers of -1 naturally alternate: $(-1)^2 = 1$, but $(-1)^1 = -1$.
So the polynomial magically turns into $c_2 - c_1 + c_0$ (the alternating sum)!

Once again, `polynomial_cong` will do all the heavy lifting — and just like with 9, the same idea scales to numbers of any length.
"

/-- The alternating sum of digits rule for 11. -/
Statement div11_rule_3 (c0 c1 c2 : ℤ) : (c2 * 10^2 + c1 * 10 + c0) ≡ (c2 * (-1)^2 + c1 * (-1) + c0) (mod 11) := by
  have h10 : 10 ≡ -1 (mod 11) := by
    unfold ModEq
    use 1
    ring
  exact polynomial_cong 10 (-1) c0 c1 c2 11 h10

Conclusion "
🏆 AMAZING! 🏆

You have proven every major divisibility rule. What seemed like a list of random tricks in school is actually a beautiful, unified theory based on modular arithmetic and polynomials.

You are now fully prepared. Take a deep breath — it is time to enter the final world, \"Problems\", where you will apply everything you've learned to crack actual numerical challenges!
"
