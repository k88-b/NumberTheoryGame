import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L02_cancel

World "Problems"
Level 3
Title "The Oracle of CRT"

Introduction "
Is there a number that ends in 7 (modulo 10) but leaves a remainder of 2 when divided by 3?
In other words, does there exist an $x$ such that $x \\equiv 7 \\pmod{10}$ and $x \\equiv 2 \\pmod 3$?

Instead of guessing, we can use the `crt_exists` theorem you proved in World 4. It guarantees a solution exists as long as the moduli are coprime.

All you need to do is prove `IsGCD(10, 3) 1` and feed it to the theorem!
"

Statement : ∃ x : ℤ, x ≡ 7 (mod 10) ∧ x ≡ 2 (mod 3) := by
  Hint "Construct the coprimality proof: `have h_gcd : IsGCD(10, 3) 1 := by ...`"
  have h_gcd : IsGCD(10, 3) 1 := by
    unfold IsGCD
    constructor
    · constructor
      · exact one_dvd 10
      · exact one_dvd 3
    · Hint (hidden := true) "Find $10 \\cdot u + 3 \\cdot v = 1$. Try `use 1, -3`."
      use 1, -3
      ring

  Hint "Now let `crt_exists` do the heavy lifting! Look at its signature in the theorems list and apply it with `exact`."
  exact crt_exists 7 2 10 3 h_gcd

Conclusion "
Boom. You didn't even have to find the number yourself (though if you do the math, $x = 17$ works perfectly). Your abstract theorem did all the work.

This is the true power of mathematics!
"
