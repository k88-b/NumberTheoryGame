import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L09_mod_mul

World "Congruence"
Level 10
Title "Shrinking the Modulus"

Introduction "
If two numbers are congruent modulo $m$, they are also congruent modulo any divisor $d$ of $m$.

In other words, if $a \\equiv b \\pmod m$ and $d \\mid m$, then $a \\equiv b \\pmod d$.

*Hint:* You can solve this by unfolding `ModEq` entirely and manipulating the witnesses, OR you can remember `dvd_trans` from World 1, which states that if $x \\mid y$ and $y \\mid z$, then $x \\mid z$!
"


/-- Decreasing the modulus to a divisor. -/
Statement mod_shrink (a b m d : ℤ) (h1 : a ≡ b (mod m)) (h2 : d ∣ m) : a ≡ b (mod d) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k2 * k1
  rw [hk1, hk2]
  ring

Conclusion "
Beautiful. This shows the deep underlying connection between standard divisibility and modular congruences.
"
