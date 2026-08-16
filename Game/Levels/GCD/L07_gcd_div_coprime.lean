import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L06_cancel_coprime

World "GCD"
Level 7
Title "Dividing by the GCD Gives Coprime Numbers"

Introduction "
Here's a natural question: if $d$ is a gcd of $c$ and $m$, and we divide both $c$ and $m$ by $d$ (writing $c = c_1 \\cdot d$ and $m = m_1 \\cdot d$), are the quotients $c_1$ and $m_1$ coprime?

Yes — and this is exactly what will let us reduce a *general* cancellation problem to the coprime case you just solved.

We need $d \\neq 0$ for this level. (If $d = 0$ then $c = m = 0$ too, and \"dividing by $d$\" doesn't make sense — you'll see exactly where this hypothesis is used.)

**Strategy:** unfold `IsGCD c m d` to get the Bézout identity $c \\cdot x + m \\cdot y = d$. Substitute $c = c_1 \\cdot d$ and $m = m_1 \\cdot d$ to get $c_1 \\cdot d \\cdot x + m_1 \\cdot d \\cdot y = d$, i.e. $d \\cdot (c_1 \\cdot x + m_1 \\cdot y) = d \\cdot 1$. Since $d \\neq 0$, you can *cancel* it from both sides using the new theorem `mul_left_cancel₀`, leaving exactly the Bézout identity you need for $c_1, m_1$ — with the very same $x, y$!
"

/--
The `mul_left_cancel₀` theorem lets you cancel a common non-zero factor from an equation:
if `a ≠ 0` and `a * b = a * c`, then `b = c`.
This works because the integers have no "zero divisors": the only way a product can vanish is if one of its factors does, so a non-zero factor can always be safely divided out of an equation.
-/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "Algebra"

NewTheorem mul_left_cancel₀

/--
**Dividing by the GCD Gives Coprime Numbers**

If `IsGCD(c, m) d`, $d \neq 0$, $c = c_1 \cdot d$ and $m = m_1 \cdot d$, then `IsGCD(c_1, m_1) 1`.

**Intuition:**
This matches your intuition exactly: $\text{IsGCD}(12, 18) 6$, and dividing both by $6$ gives $2$ and $3$, which indeed satisfy $\text{IsGCD}(2, 3) 1$. Once you factor out everything two numbers have in common, whatever is left over shares nothing.
-/
TheoremDoc gcd_div_coprime as "gcd_div_coprime" in "GCD"

/-- Dividing by the gcd produces coprime numbers. -/
Statement gcd_div_coprime (c m d c1 m1 : ℤ) (hd : d ≠ 0) (h : IsGCD(c, m) d) (hc : c = c1 * d) (hm : m = m1 * d) : IsGCD(c1, m1) 1 := by
  unfold IsGCD at *
  obtain ⟨_, x, y, hxy⟩ := h
  constructor
  · constructor
    · exact one_dvd c1
    · exact one_dvd m1
  · use x, y
    have e : d * (c1 * x + m1 * y) = c1 * d * x + m1 * d * y := by ring
    have h_eq : d * (c1 * x + m1 * y) = d * 1 := by
      rw [e]
      rw [← hc] ; rw [← hm]
      rw [hxy]
      ring
    exact mul_left_cancel₀ hd h_eq


Conclusion "
Great! `gcd_div_coprime` is now saved — it's the missing piece that will let us cancel factors that aren't necessarily coprime to the modulus, in the very next level.
"
