import GameServer
import Mathlib.Tactic
import Game.Levels.DivRules.L04_div4

World "DivRules"
Level 5
Title "Divisibility by 9 (The Magic of Polynomials)"

Introduction "
Here is the famous rule: \"A number is divisible by 9 if the sum of its digits is divisible by 9\".

To prove this, we need a formal way to write a number digit by digit. Think about how our base-10 system works. A 3-digit number like **345** is literally **3 * 100 + 4 * 10 + 5**.
If we call the individual digits $c_2$, $c_1$, and $c_0$, the number is written exactly as $c_2 \\cdot 10^2 + c_1 \\cdot 10 + c_0$.

Notice anything? This is a polynomial evaluated at 10!
We want to show it is congruent to the sum of its digits: $c_2 \\cdot 1^2 + c_1 \\cdot 1 + c_0$, which is the exact same polynomial evaluated at 1.

Since $10 \\equiv 1 \\pmod 9$, your ultimate weapon `polynomial_cong` from World 4 will solve this instantly.

*(We prove this here for 3-digit numbers as a clean, concrete illustration — the exact same argument, with a longer polynomial, proves it for numbers of any length.)*
"

/-- The sum of digits rule for 9. -/
Statement div9_rule_3 (c0 c1 c2 : ℤ) : (c2 * 10^2 + c1 * 10 + c0) ≡ (c2 * 1^2 + c1 * 1 + c0) (mod 9) := by
  have h10 : 10 ≡ 1 (mod 9) := by
    unfold ModEq
    use 1
    ring
  exact polynomial_cong 10 1 c0 c1 c2 9 h10

Conclusion "
Beautiful! Two lines of code prove a rule that feels like magic in middle school. Because polynomials preserve congruences, substituting 10 for 1 works perfectly.
"
