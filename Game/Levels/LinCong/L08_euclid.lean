import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L07_sol_shift

World "LinCong"
Level 8
Title "Euclid's Lemma"

Introduction "
We are about to build the Chinese Remainder Theorem, but first, we need a legendary stepping stone: **Euclid's Lemma**.

If $m \\mid (a \\cdot c)$ and $\\text{gcd}(c, m) = 1$, then $m \\mid a$.

Notice that $m \\mid (a \\cdot c)$ is exactly the same as saying $a \\cdot c \\equiv 0 \\cdot c \\pmod m$.
Since $c$ is coprime to $m$, can we just cancel $c$? Yes, you have `mod_cancel_coprime`!
"

/--
**Euclid's Lemma**

If $m \mid (a \cdot c)$ and $c$ is coprime to $m$, then $m \mid a$.
-/
TheoremDoc euclids_lemma as "euclids_lemma" in "LinCong"

Statement euclids_lemma (a c m : ℤ) (h_div : m ∣ a * c) (h_coprime : IsGCD(c, m) 1) : m ∣ a := by
  have h_cong_direct : (a * c) ≡ (0 * c) (mod m) := by
    unfold ModEq
    obtain ⟨k, hk⟩ := h_div
    use k
    have h_eq : a * c - 0 * c = a * c := by ring
    rw [h_eq]
    exact hk
  have h_cancel := mod_cancel_coprime a 0 c m h_cong_direct h_coprime
  unfold ModEq at h_cancel
  obtain ⟨k2, hk2⟩ := h_cancel
  use k2
  have h_eq2 : a = a - 0 := by ring
  rw [h_eq2, hk2]

Conclusion "
Incredible! A simple cancellation yields one of the oldest and most fundamental theorems in number theory.
"
