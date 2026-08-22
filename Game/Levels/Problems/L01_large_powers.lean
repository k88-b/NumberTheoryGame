import GameServer
import Mathlib.Tactic
import Game.Levels.Definitions

import Game.Levels.GCD
import Game.Levels.Congruence
import Game.Levels.Divisibility
import Game.Levels.LinCong

World "Problems"
Level 1
Title "Huge Powers"

Introduction "
Let's start with a classic competition problem: what is the remainder of $17^{100} + 12^{100}$ when divided by 5?

If you try to compute $17^{100}$ directly, the universe will end before you finish. But you know that congruences preserve addition and powers! Since $17 \\equiv 2 \\pmod 5$ and $12 \\equiv 2 \\pmod 5$, you can use your abstract theorems to simplify the bases before applying the exponent.

**Strategy:**
Create intermediate facts using `have` for the base numbers, then raise them to the 100th power using `mod_pow`, and finally add them together using `mod_add`.
"

Statement : (17^100 + 12^100) ≡ (2^100 + 2^100) (mod 5) := by
  Hint "Start by proving the base congruences. Create a hypothesis `have h1 : 17 ≡ 2 (mod 5) := by ...`. Unfold `ModEq` and use a witness!"
  have h1 : 17 ≡ 2 (mod 5) := by
    unfold ModEq
    use 3
    ring

  Hint (hidden := true) "Now do the same for 12: `have h2 : 12 ≡ 2 (mod 5) := by ...`"
  have h2 : 12 ≡ 2 (mod 5) := by
    unfold ModEq
    use 2
    ring

  Hint "Now use your theorem from World 2! Apply `mod_pow` to your base congruences: `have h3 := mod_pow 17 2 5 100 h1`."
  have h3 := mod_pow 17 2 5 100 h1
  have h4 := mod_pow 12 2 5 100 h2

  Hint "You have congruences for the two parts. Combine them using `exact mod_add ...`!"
  exact mod_add (17^100) (2^100) (12^100) (2^100) 5 h3 h4

Conclusion "
Beautiful! By using theorems instead of brute force, you reduced a massive calculation to simple logic.
"
