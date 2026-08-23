import GameServer
import Mathlib.Tactic
import Game.Levels.DivRules.L05_div9

World "DivRules"
Level 6
Title "Divisibility by 3"

Introduction "
If the rule for 9 works, the rule for 3 must come for free, because $3 \\mid 9$.

Just like you shrank the modulus from 10 down to 2 and 5 earlier, shrink the modulus from 9 to 3 here using `mod_shrink`.

**Syntax Tip:** When writing your divisibility fact, make sure to specify the type so Lean doesn't default to natural numbers: `have h3 : (3 : ℤ) ∣ 9 := by ...`
"

/-- The sum of digits rule for 3. -/
Statement div3_rule_3 (c0 c1 c2 : ℤ) : (c2 * 10^2 + c1 * 10 + c0) ≡ (c2 * 1^2 + c1 * 1 + c0) (mod 3) := by
  have h9 := div9_rule_3 c0 c1 c2
  have h3 : (3 : ℤ) ∣ 9 := by
    use 3
    ring
  exact mod_shrink (c2 * 10^2 + c1 * 10 + c0) (c2 * 1^2 + c1 * 1 + c0) 9 3 h9 h3

Conclusion "
Beautiful. The structural similarity of mathematics really shines here.
"
