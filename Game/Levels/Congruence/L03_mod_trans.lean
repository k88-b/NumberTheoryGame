import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L02_mod_symm

World "Congruence"
Level 3
Title "Transitivity of Congruences"

Introduction "
To prove that $\\equiv$ is a true equivalence relation, we must prove **transitivity**:
If $a \\equiv b$ and $b \\equiv c$, then $a \\equiv c$.

You know the drill:
1. Use `unfold ModEq at *` to reveal the definitions in your goals and hypotheses.
2. `obtain` the witnesses $k_1$ and $k_2$ from your hypotheses.
3. Use algebra (`have`) to rewrite $a - c$ as $(a - b) + (b - c)$.
4. Apply your rewrites and let `ring` finish the job!
"

/--
**Transitivity of Modular Congruence**

If $a \equiv b \pmod m$ and $b \equiv c \pmod m$, then $a \equiv c \pmod m$.

**Meaning:** This theorem proves that modular arithmetic is a true *equivalence relation*. It means you can chain congruences together step-by-step to reach a conclusion, exactly like you can chain regular equations ($a = b$ and $b = c \implies a = c$).
-/
TheoremDoc mod_trans as "mod_trans" in "Congruence"

/-- Congruence modulo m is transitive. -/
Statement mod_trans (a b c m : ℤ) (h1 : a ≡ b (mod m)) (h2 : b ≡ c (mod m)) : a ≡ c (mod m) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  Hint (hidden := true) "try to `use {k1} + {k2}`"
  use k1 + k2
  have h_eq : a - c = (a - b) + (b - c) := by ring
  rw [h_eq]
  rw [hk1]
  rw [hk2]
  ring

Conclusion "
Excellent! You have successfully proved transitivity, completely confirming that congruences behave just like regular equality.
"
