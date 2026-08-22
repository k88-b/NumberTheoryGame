import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L03_crt

World "Problems"
Level 4
Title "Solving Linear Congruences"

Introduction "
Can we always find a solution to $5 \\cdot x \\equiv 3 \\pmod 7$?

In World 4, you proved `lin_cong_suff`, which states that $a \\cdot x \\equiv b \\pmod m$ has a solution as long as $\\gcd(a, m) \\mid b$.
Here $a = 5$, $b = 3$, and $m = 7$. Since 5 and 7 are coprime, their GCD is 1, and 1 certainly divides 3!

**Strategy:**
Build the GCD proof for `IsGCD(5, 7) 1`, and the divisibility proof for `1 ∣ 3`. Then hand them to `lin_cong_suff`.
"

Statement : ∃ x : ℤ, (5 * x) ≡ 3 (mod 7) := by
  Hint "Start by proving the GCD: `have h_gcd : IsGCD(5, 7) 1 := by ...`"
  have h_gcd : IsGCD(5, 7) 1 := by
    unfold IsGCD
    constructor
    · constructor
      · exact one_dvd 5
      · exact one_dvd 7
    · Hint (hidden := true) "Find $5 \\cdot u + 7 \\cdot v = 1$. Try `use 3, -2`."
      use 3, -2
      ring

  Hint "Now prove that 1 divides 3: `have h_div : 1 ∣ 3 := by ...`"
  have h_div : (1: ℤ) ∣ 3 := by
    use 3
    ring

  Hint "Apply your theorem! Look at the arguments for `lin_cong_suff` in your theorems tab."
  exact lin_cong_suff 5 3 7 1 h_gcd h_div

Conclusion "
Excellent! The theorem constructed the solution under the hood.

If you trace the algebra of `lin_cong_suff`, it gives $x = u \\cdot (b/d) = 3 \\cdot 3 = 9$, and indeed $5 \\cdot 9 = 45 \\equiv 3 \\pmod 7$. Abstract theory gives concrete results!
"
