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

/--
**Reverse Inverse**

If $a \cdot x \equiv 1 \pmod m$ for some $x$, then $\text{IsGCD}(a, m) 1$.
-/
TheoremDoc inv_implies_coprime as "inv_implies_coprime" in "LinCong"

Statement inv_implies_coprime (a m : ℤ) (h : ∃ x, (a * x) ≡ 1 (mod m)) : IsGCD(a, m) 1 := by
  obtain ⟨x, hx⟩ := h
  unfold ModEq at hx
  obtain ⟨k, hk⟩ := hx
  Hint "You have `{a} * {x} - 1 = {m} * {k}`. To get a Bézout identity `{a} * u + {m} * v = 1`, try `u = {x}` and `v = -{k}`."
  have h_bezout : ∃ u v : ℤ, a * u + m * v = 1 := by
    use x, -k
    Hint (hidden := true) "Build it with `have h_eq : {a} * {x} + {m} * (-{k}) = ({a} * {x} - 1) - {m} * {k} + 1 := by ring`, then `rw [h_eq, {hk}]` and finish with `ring`."
    have h_eq : a * x + m * (-k) = (a * x - 1) - m * k + 1 := by ring
    rw [h_eq]
    rw [hk]
    ring
  exact bezout_imp_coprime a m h_bezout

Conclusion "
Great! Reversibility is confirmed. Having a modular inverse is *exactly equivalent* to being coprime to the modulus.
"
