import GameServer
import Mathlib.Tactic
import Game.Levels.DivRules.L02_div2

World "DivRules"
Level 3
Title "Divisibility by 5"

Introduction "
As promised at the end of the last level, let's finish off the pair: since $5 \\mid 10$ too, the exact same trick that worked for 2 also nails the rule for 5.

If $10 \\cdot k + d \\equiv d \\pmod{10}$ (Level 1), and $5 \\mid 10$, then `mod_shrink` immediately gives us $10 \\cdot k + d \\equiv d \\pmod 5$ as well.

**Syntax Tip:** Same reminder as last time — write `have h5 : (5 : ℤ) ∣ 10 := by ...` so Lean doesn't default to natural numbers.
"

/-- The remainder modulo 5 depends only on the last digit. -/
Statement div5_rule (k d : ℤ) : (10 * k + d) ≡ d (mod 5) := by
  have h10 := div10_rule k d
  have h5 : (5 : ℤ) ∣ 10 := by
    use 2
    ring
  exact mod_shrink (10 * k + d) d 10 5 h10 h5

Conclusion "
Done! Together with the last two levels, you now have the full \"last digit\" family for free: 10, 2, and 5 all fall directly out of `mod_add_multiple` and `mod_shrink`.
"
