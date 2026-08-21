import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L01_mod_refl

World "Congruence"
Level 2
Title "Symmetry of Congruences"


NewTactic «have»

Introduction "
If $a \\equiv b \\pmod m$, is it true that $b \\equiv a \\pmod m$?

Before we dive into the math, let's learn a crucial syntactic trick: the **`at`** keyword.
By default, tactics like `unfold` or `rw` only apply to your *goal*. But often you need to modify your *hypotheses* (your assumptions).
* `unfold ModEq at h` will unfold the definition only inside the hypothesis `h`.
* `unfold ModEq at *` will unfold it *everywhere* (in all hypotheses and the goal at once).
* You can also do this with rewrites: `rw [h_eq] at h1` will rewrite using `h_eq` inside `h1`.

Start this proof by typing `unfold ModEq at *`. Then let's unpack the algebra:
We assume $m \\mid (a - b)$, so $a - b = m \\cdot k$.
We need to prove $m \\mid (b - a)$, which means $b - a = m \\cdot ?$.
Since $b - a = -(a - b)$, the multiplier should be $-k$.

You will need an intermediate mathematical step. You can create one using the `have` tactic.
If you type `have h_eq : b - a = -(a - b) := by ring`, Lean will add `h_eq` to your context.
You can then use `rw [h_eq]` to transform your goal!

**Rewriting backwards**
By default, `rw [h_eq]` looks for the *left* side of your equality (`b - a`) and replaces it with the *right* side (`-(a - b)`).
If you ever formulate your equality the other way around, for example `have h_eq : -(a - b) = b - a`, you will need to tell Lean to rewrite from right to left using a left arrow: `rw [← h_eq]`.
*(To type the left arrow `←`, simply type `\\l` and press Space)*
"


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
Beautiful! You used `have` to build a bridge between algebra you know and algebra you need, and successfully learned how to use `at *`.
Working with negative variables is a core skill in integer arithmetic.
"
