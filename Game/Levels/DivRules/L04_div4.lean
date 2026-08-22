import GameServer
import Mathlib.Tactic
import Game.Levels.DivRules.L03_div5

World "DivRules"
Level 4
Title "Divisibility by 4"

Introduction "
A number is divisible by 4 if its last two digits form a number divisible by 4.

Instead of separating the last digit, we separate the last *two* digits! Just like in Level 1, where we wrote a number as $10 \\cdot k + d$ using the last digit, here we write it as $100 \\cdot k + d$ using the last *two* digits. For example, **3456 = 34 * 100 + 56**, where $d = 56$ is exactly the last two digits.

We want to show $100 \\cdot k + d \\equiv d \\pmod 4$.
Notice that $100 = 25 \\cdot 4$. Use `mod_add_multiple` just like in Level 1!
"

/-- The remainder modulo 4 depends only on the last two digits. -/
Statement div4_rule (k d : ℤ) : (100 * k + d) ≡ d (mod 4) := by
  Hint (hidden := true) "Since 100 = 25 * 4, the term 100 * k is already a multiple of 4. Restate the goal as d plus that multiple of 4, in the shape mod_add_multiple expects."
  have h_eq : 100 * k + d = d + (25 * k) * 4 := by ring
  rw [h_eq]
  exact mod_add_multiple d (25 * k) 4

Conclusion "
Exactly! Since 4 divides 100, everything above the tens place just vanishes modulo 4.
"
