import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L02_mod_refl

World "Congruence"
Level 3
Title "Divisible Means Congruent to Zero"

Introduction "
Before continuing with equivalence relations, let's build a direct bridge between World 1 and World 2.

What does it mean for a number $a$ to be divisible by $m$ in the language of congruences? It simply means that dividing $a$ by $m$ leaves a remainder of $0$ — or in other words, $a \\equiv 0 \\pmod m$.
"

/-- Divisibility implies congruence to zero modulo m. -/
Statement dvd_imp_mod_zero (a m : ℤ) (h : m ∣ a) : a ≡ 0 (mod m) := by
  unfold ModEq
  obtain ⟨k, hk⟩ := h
  rw [hk]
  use k
  ring

Conclusion "
Divisibility and congruence to zero are two sides of the same coin!
Whenever you see $a \\equiv 0 \\pmod m$, you can immediately translate it in your head as \"$m$ divides $a$\".
"
