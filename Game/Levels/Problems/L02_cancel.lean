import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L01_large_powers

World "Problems"
Level 2
Title "Cancelling Constants"

Introduction "
Suppose we know that $14 \\cdot x \\equiv 14 \\cdot y \\pmod 9$. Can we conclude that $x \\equiv y \\pmod 9$?

In World 3, you proved `mod_cancel_coprime`, which says we can cancel a factor if it's coprime to the modulus.
To use it here, you first need to prove that 14 and 9 are coprime, meaning `IsGCD(14, 9) 1`.

**Lean Syntax Tip:** The notation `IsGCD(a, b) d` is just syntactic sugar to make the goals easier to read. When writing your own code (for example, when defining a new hypothesis with `have`), you need to use the standard Lean syntax without parentheses or commas: `IsGCD a b d`.
"

Statement (x y : ℤ) (h : (14 * x) ≡ (14 * y) (mod 9)) : x ≡ y (mod 9) := by
  have h_gcd : IsGCD 14 9 1
  unfold IsGCD
  constructor
  · constructor
    · exact one_dvd 14
    · exact one_dvd 9
  · use 2, -3
    ring

  Hint "The theorem `mod_cancel_coprime` expects the common factor on the *right* side of the multiplication. Create a new hypothesis to swap the order"

  have h_swap : (x * 14) ≡ (y * 14) (mod 9)

  · have hrw1 : x * 14 = 14 * x
    · ring

    have hrw2 : y * 14 = 14 * y
    · ring

    rw [hrw1, hrw2]

    exact h

  Hint "Now you can finish the proof using `mod_cancel_coprime` with your swapped hypothesis `{h_swap}` and `{h_gcd}`!"
  exact mod_cancel_coprime x y 14 9 h_swap h_gcd


Conclusion "
Excellent! You proved a concrete GCD on the fly to unlock the power of your cancellation theorem.
"
