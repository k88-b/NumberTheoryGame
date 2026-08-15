import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L08_mod_trans

World "Congruence"
Level 1
Title "Adding Congruences"

Introduction "
If $a \\equiv b \\pmod m$ and $c \\equiv d \\pmod m$, is it true that $a + c \\equiv b + d \\pmod m$?

Yes! This means we can add two congruences together.
To prove this, you need to `unfold ModEq at *`, extract the witnesses from both hypotheses using `obtain`, and then use algebra.

*Hint:* You will need to rewrite $(a + c) - (b + d)$ into $(a - b) + (c - d)$. Use the `have` tactic!
"

/--
**Adding Congruences**

If $a \equiv b \pmod m$ and $c \equiv d \pmod m$, then $(a + c) \equiv (b + d) \pmod m$.

**Intuition:**
If two pairs of numbers have the same remainder when divided by $m$, their sums will also have the same remainder.
For example, modulo 10 (which just looks at the last digit):
If $12 \equiv 2 \pmod{10}$ and $25 \equiv 5 \pmod{10}$, then $12 + 25 = 37$, which is $\equiv 7 \pmod{10}$.
Notice that $2 + 5 = 7$. We just added the remainders safely!
-/
TheoremDoc mod_add as "mod_add" in "Congruence"

/-- If two pairs of numbers are congruent, their sums are congruent. -/
Statement mod_add (a b c d m : ℤ) (h1 : a ≡ b (mod m)) (h2 : c ≡ d (mod m)) : (a + c) ≡ (b + d) (mod m) := by
  unfold ModEq at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k1 + k2
  have h_eq : (a + c) - (b + d) = (a - b) + (c - d) := by ring
  rw [h_eq]
  rw [hk1]
  rw [hk2]
  ring

Conclusion "
Excellent! You combined two witnesses using `obtain` and proved your first arithmetic rule for congruences.
"
