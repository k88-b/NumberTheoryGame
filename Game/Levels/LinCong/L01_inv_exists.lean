import GameServer
import Mathlib.Tactic
import Game.Levels.Defs

World "LinCong"
Level 1
Title "Existence of the Inverse"

Introduction "
First, let's explore **modular inverses**. If $a$ and $m$ are coprime ($gcd(a, m) = 1$), does there exist an $x$ such that $a \\cdot x \\equiv 1 \\pmod m$?

Yes! And Bézout's identity gives us exactly the proof. Since $a$ and $m$ are coprime, we know $a \\cdot x + m \\cdot y = 1$. The $x$ from this identity is exactly the inverse we are looking for.

Use `unfold IsGCD` to extract Bézout's coefficients, and then use algebra!
"

/--
**Modular Inverse Existence**

If $\text{IsGCD}(a, m) 1$, then there exists an integer $x$ such that $a \cdot x \equiv 1 \pmod m$.
-/
TheoremDoc inv_exists as "inv_exists" in "LinCong"

Statement inv_exists (a m : ℤ) (h : IsGCD(a, m) 1) : ∃ x : ℤ, (a * x) ≡ 1 (mod m) := by
  unfold IsGCD at h
  obtain ⟨_, x, y, hxy⟩ := h
  use x
  unfold ModEq
  use -y
  have h_eq : a * x - 1 = (a * x + m * y) - 1 - m * y := by ring
  rw [h_eq]
  rw [hxy]
  have h_eq2 : 1 - 1 - m * y = m * (-y) := by ring
  rw [h_eq2]


Conclusion "
Perfect! You have proven that every number coprime to the modulus has a modular inverse.
"
