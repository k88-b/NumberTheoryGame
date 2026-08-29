import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L07_cancel_coprime

World "GCD"
Level 8
Title "Dividing by the GCD Gives Coprime Numbers"

Introduction "
Here's a natural question: if $d$ is a gcd of $c$ and $m$, and we divide both $c$ and $m$ by $d$ (writing $c = c_1 \\cdot d$ and $m = m_1 \\cdot d$), are the quotients $c_1$ and $m_1$ coprime?

Yes — and this is exactly what will let us reduce a *general* cancellation problem to the coprime case you just solved.

We need $d \\neq 0$ for this level. (If $d = 0$ then $c = m = 0$ too, and \"dividing by $d$\" doesn't make sense — you'll see exactly where this hypothesis is used.)

**Strategy:** unfold `IsGCD c m d` to get the Bézout identity $c \\cdot x + m \\cdot y = d$. Substitute $c = c_1 \\cdot d$ and $m = m_1 \\cdot d$ to get $c_1 \\cdot d \\cdot x + m_1 \\cdot d \\cdot y = d$, i.e. $d \\cdot (c_1 \\cdot x + m_1 \\cdot y) = d \\cdot 1$. Since $d \\neq 0$, you can *cancel* it from both sides using the new theorem `mul_left_cancel₀`, leaving exactly the Bézout identity you need for $c_1, m_1$ — with the very same $x, y$!
"


NewTheorem mul_left_cancel₀


/-- Dividing by the gcd produces coprime numbers. -/
Statement gcd_div_coprime (c m d c1 m1 : ℤ) (hd : d ≠ 0) (h : IsGCD(c, m) d) (hc : c = c1 * d) (hm : m = m1 * d) : IsGCD(c1, m1) 1 := by
  unfold IsGCD at *
  obtain ⟨_, x, y, hxy⟩ := h
  constructor
  · constructor
    · exact one_dvd c1
    · exact one_dvd m1
  · use x, y

    have e : d * (c1 * x + m1 * y) = c1 * d * x + m1 * d * y
    · ring

    Hint (hidden := true) "To use `mul_left_cancel₀`, you need to set up an equation of the exact form `{d} * something = {d} * 1`."

    have h_eq : d * (c1 * x + m1 * y) = d * 1
    · rw [e, ← hc, ← hm, hxy]
      ring

    exact mul_left_cancel₀ hd h_eq


Conclusion "
Great! `gcd_div_coprime` is now saved — it's the missing piece that will let us cancel factors that aren't necessarily coprime to the modulus, in the very next level.
"
