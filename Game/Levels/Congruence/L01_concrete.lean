import GameServer
import Mathlib.Tactic
import Game.Metadata
import Game.Levels.Definitions
import Game.Doc.Definitions
import Game.Doc.Tactics
import Game.Doc.Theorems.Congruence

import Game.Levels.Divisibility

World "Congruence"
Level 1
Title "Your First Congruence"

NewDefinition ModEq
NewTactic unfold

Introduction "
Welcome to World 2! Here we introduce one of the most powerful ideas in number theory: **Congruences**.

Often, we don't care about a number itself, only about the remainder it leaves when divided by some modulus $m$ — just like reading a 12-hour clock. Formally, we say that $a \\equiv b \\pmod m$ if $m$ divides their difference $(a - b)$.

In Lean, this is written as `a ≡ b (mod m)` (to type `≡`, write `\\==` and press Space). Check your **Definitions** tab for more details!

Whenever you see this notation, type `unfold ModEq` to reveal the divisibility statement hiding underneath. Let's test it out on a concrete example: show that $17 \\equiv 5 \\pmod 6$.
"

/-- Concrete verification of modular congruence. -/
Statement : 17 ≡ 5 (mod 6) := by
  unfold ModEq
  use 2
  ring

Conclusion "
Congratulations on proving your first congruence!
Because $17 - 5 = 12 = 6 \\cdot 2$, 17 and 5 leave the exact same remainder when divided by 6.
Now let's leave specific numbers behind and build the general theory!
"
