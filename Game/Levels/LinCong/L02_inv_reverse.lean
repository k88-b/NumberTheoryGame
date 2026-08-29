import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L01_inv_exists

World "LinCong"
Level 2
Title "Inverse Implies Coprimality"

Introduction "
Does it work the other way? If $a$ has a modular inverse modulo $m$, must $a$ and $m$ be coprime?

Absolutely. If $a \\cdot x \\equiv 1 \\pmod m$, it means $a \\cdot x - 1 = m \\cdot k$, which you can rearrange into a Bézout identity for $1$. You proved in World 3 (`bezout_imp_coprime`) that this forces the GCD to be 1!
"


Statement inv_implies_coprime (a m : ℤ) (h : ∃ x, (a * x) ≡ 1 (mod m)) : IsGCD(a, m) 1 := by
  obtain ⟨x, hx⟩ := h
  unfold ModEq at hx
  obtain ⟨k, hk⟩ := hx

  Hint "You know a * {x} − 1 = m * {k}. Rearranged, a * {x} + m * (−{k}) = 1 — exactly a Bézout identity for 1, using the same x and the negation of {k}."

  have h_bezout : ∃ u v : ℤ, a * u + m * v = 1
  · use x, -k
    Hint (hidden := true) "To verify a * {x} + m * (−{k}) = 1, rewrite it as (a * {x} − 1) − m * {k} + 1, then substitute a * {x} − 1 = m * {k}. What remains is pure arithmetic."

    have h_eq : a * x + m * (-k) = (a * x - 1) - m * k + 1
    · ring

    rw [h_eq, hk]
    ring

  exact bezout_imp_coprime a m h_bezout

Conclusion "
Great! Reversibility is confirmed. Having a modular inverse is *exactly equivalent* to being coprime to the modulus.
"
