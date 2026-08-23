import GameServer
import Mathlib.Tactic
import Game.Levels.DivRules.L01_div10

World "DivRules"
Level 2
Title "Divisibility by 2"

Introduction "
What about divisibility by 2? Since $2 \\mid 10$, we can just shrink the modulus of the previous rule!
If $10 \\cdot k + d \\equiv d \\pmod{10}$, it must also be true modulo 2.

Use `mod_shrink` from World 2. You will need to explicitly prove that $2 \\mid 10$ first using a `have` block.

**Syntax Tip:** If you just write `have h2 : 2 ∣ 10 := by ...`, Lean will assume 2 and 10 are natural numbers (`ℕ`), but our theorems expect integers (`ℤ`). To fix this, you must explicitly tell Lean the type of at least one number.
Write your statement like this: `have h2 : (2 : ℤ) ∣ 10 := by ...` *(To type `ℤ`, write `\\Z` and press Space.)*
"

/-- The remainder modulo 2 depends only on the last digit. -/
Statement div2_rule (k d : ℤ) : (10 * k + d) ≡ d (mod 2) := by
  have h10 := div10_rule k d
  have h2 : (2 : ℤ) ∣ 10 := by
    use 5
    ring
  exact mod_shrink (10 * k + d) d 10 2 h10 h2

Conclusion "
Nice! Exactly the same logic applies to 5, since 5 ∣ 10 too — that's exactly what the next level does.
"
