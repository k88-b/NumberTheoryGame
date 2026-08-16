import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L07_mod_symm

World "Divisibility"
Level 8
Title "Transitivity of Congruences (Boss)"

Introduction "
Welcome to the final boss of the Divisibility Club!
To prove that $\\equiv$ is a true equivalence relation, we must prove **transitivity**:
If $a \\equiv b$ and $b \\equiv c$, then $a \\equiv c$.

You know the drill:
1. Use `unfold ModEq at *` to reveal the definitions in your goals and hypotheses.
2. `obtain` the witnesses $k_1$ and $k_2$ from your hypotheses.
3. Use algebra (`have`) to rewrite $a - c$ as $(a - b) + (b - c)$.
4. Apply your rewrites and let `ring` finish the job!

Good luck!
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
  use k1 + k2
  have h_eq : a - c = (a - b) + (b - c) := by ring
  rw [h_eq]
  rw [hk1]
  rw [hk2]
  ring

Conclusion "
🎉 INCREDIBLE! 🎉

You have conquered the first world! You successfully proved that modular congruence is reflexive, symmetric, and transitive. It is officially an equivalence relation.

You've mastered the foundational tactics `use`, `intro`, `obtain`, `rw`, `have`, and `ring`.
Get ready for World 2, where we will start doing actual arithmetic inside these modular equations!
"
