import GameServer
import Mathlib.Tactic
import Game.Metadata
import Game.Levels.Definitions
import Game.Doc.Theorems.DivRules


import Game.Levels.GCD
import Game.Levels.Congruence
import Game.Levels.Divisibility
import Game.Levels.LinCong

World "DivRules"
Level 1
Title "Divisibility by 10"

Introduction "
Let's start with the easiest rule: a number is divisible by 10 if and only if its last digit is 0.

How do we write \"the last digit\" in math? Think about how numbers are built. You can split any number into its last digit and \"everything else\" multiplied by 10. For example, **347 = 34 * 10 + 7**.
So, any integer can mathematically be written as $10 \\cdot k + d$, where $d$ is the last digit and $k$ is the rest of the number.

We want to prove that $10 \\cdot k + d \\equiv d \\pmod{10}$.
This is a direct consequence of `mod_add_multiple` from World 2! You just need to massage the equation slightly.
"

/-- The remainder of a number modulo 10 is its last digit. -/
Statement div10_rule (k d : ℤ) : (10 * k + d) ≡ d (mod 10) := by
  have h_eq : 10 * k + d = d + k * 10
  · ring

  rw [h_eq]
  exact mod_add_multiple d k 10

Conclusion "
Perfect! The last digit is exactly the remainder modulo 10.
"
