
import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L06_mod_refl

World "Divisibility"
Level 7
Title "Symmetry of Congruences"

/--
The `have` tactic allows you to prove intermediate steps.
Typing `have h : X = Y := by ring` creates a new hypothesis `h` in your context.
-/
TacticDoc «have»

NewTactic «have»

Introduction "
If $a \\equiv b \\pmod m$, is it true that $b \\equiv a \\pmod m$?

Let's unpack this. We assume $m \\mid a - b$, so $a - b = m \\cdot k$.
We need to prove $m \\mid b - a$, which means $b - a = m \\cdot ?$.
Since $b - a = -(a - b)$, the multiplier should be $-k$.

You will need an intermediate mathematical step. You can create one using the `have` tactic.
If you type `have h_eq : b - a = -(a - b) := by ring`, Lean will add `h_eq` to your context.
You can then use `rw [h_eq]` to transform your goal!

**Rewriting backwards**
By default, `rw [h_eq]` looks for the *left* side of your equality (`b - a`) and replaces it with the *right* side (`-(a - b)`).
If you ever formulate your equality the other way around, for example `have h_eq : -(a - b) = b - a`, you will need to tell Lean to rewrite from right to left using a left arrow: `rw [← h_eq]`.
*(To type the left arrow `←`, simply type `\\l` and press Space)*
"

/--
**Symmetry of Congruences**

If $a \equiv b \pmod m$, then $b \equiv a \pmod m$.

**Intuition:**
If the difference between $a$ and $b$ is a multiple of $m$, the difference between $b$ and $a$ is just the same multiple with a negative sign.
For example, $17 \equiv 5 \pmod{12}$ because $17 - 5 = 12$.
Conversely, $5 \equiv 17 \pmod{12}$ because $5 - 17 = -12$, which is still a multiple of $12$ ($12 \cdot -1$).
-/
TheoremDoc mod_symm as "mod_symm" in "Congruence"

/-- Congruence modulo m is symmetric. -/
Statement mod_symm (a b m : ℤ) (h : a ≡ b (mod m)) : b ≡ a (mod m) := by
  unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use -k
  have h_eq : b - a = -(a - b) := by ring
  rw [h_eq]
  rw [hk]
  ring

Conclusion "
Beautiful! You used `have` to build a bridge between algebra you know and algebra you need.
Working with negative variables is a core skill in integer arithmetic.
"
