import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L11_dvd_mul

World "Divisibility"
Level 12
Title "Sums of Multiples"

Introduction "
What happens when we add two multiples of $a$ together?
If $a \\mid b$ and $a \\mid c$, then $a$ must also divide their sum $b + c$.

This time you have **two** divisibility hypotheses: `h1 : a ∣ b` and `h2 : a ∣ c`.
Unpack both of them using `obtain`, making sure to give their witnesses different names:
- `obtain ⟨k1, hk1⟩ := h1`
- `obtain ⟨k2, hk2⟩ := h2`

Since $b + c = a \\cdot k_1 + a \\cdot k_2 = a \\cdot (k_1 + k_2)$, you can easily spot the witness for `a ∣ b + c`!
"

/-- If a divides b and a divides c, then a divides b + c. -/
Statement dvd_add_int (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  rw [hk1, hk2]
  use k1 + k2
  ring

Conclusion "
Awesome! You just proved that multiples of $a$ are closed under addition (`dvd_add_int`). Notice that it doesn't matter whether you `rw [hk1, hk2]` before or after `use k1 + k2` — both orders work cleanly!
"
