import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L03_inv_unique

World "LinCong"
Level 4
Title "Solvability: Necessary Condition"

Introduction "
We now move to general linear equations: $a \\cdot x \\equiv b \\pmod m$.
When does this have a solution?

Let $d = gcd(a, m)$. If a solution $x$ exists, it is strictly necessary that $d$ divides $b$.
Unfold the definitions, and apply `dvd_mul_of_dvd_left` from World 3!
"

/--
**Solvability (Necessary Condition)**

If $d = \text{gcd}(a, m)$ and $a \cdot x \equiv b \pmod m$ has a solution, then $d \mid b$.
-/
TheoremDoc lin_cong_nec as "lin_cong_nec" in "LinCong"

Statement lin_cong_nec (a b x m d : ℤ) (hd : IsGCD(a, m) d) (hx : (a * x) ≡ b (mod m)) : d ∣ b := by
  unfold IsGCD at hd
  obtain ⟨⟨hda, hdm⟩, _⟩ := hd
  unfold ModEq at hx
  obtain ⟨k, hk⟩ := hx
  have h1 : d ∣ (a * x) := dvd_mul_of_dvd_left hda x
  have h2 : d ∣ (m * k) := dvd_mul_of_dvd_left hdm k
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k1 - k2
  have h_eq : b = a * x - m * k := by
    rw [← hk]
    ring
  rw [h_eq]
  rw [hk1, hk2]
  ring

Conclusion "
Nice! You successfully extracted the divisibility parts of the GCD to prove $d \\mid b$.
"
