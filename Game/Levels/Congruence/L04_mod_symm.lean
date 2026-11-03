import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L03_dvd_imp_mod_zero

World "Congruence"
Level 4
Title "Symmetry of Congruences"


NewTactic «have»

Introduction "
The second property of an equivalence relation is **symmetry**: if $a \\equiv b \\pmod m$, then $b \\equiv a \\pmod m$.

Before we dive into the proof, let's learn two crucial Lean features:

1. **The `at` keyword:** By default, tactics like `unfold` or `rw` only affect your *goal*. To modify hypotheses, use `at`:
* `unfold ModEq at h` unfolds the definition inside hypothesis `h`.
* `unfold ModEq at *` unfolds it *everywhere* (in all hypotheses and the goal at once).

2. **The `have` tactic:** Often, you need an intermediate algebraic fact before you can rewrite your goal. For example, here you know $a - b = m \\cdot k$, but your goal contains $b - a$.
If you type `have h_eq : b - a = -(a - b)`, Lean will pause and ask you to prove this equation first (using `ring`). Once proved, `h_eq` is added to your assumptions so you can `rw [h_eq]` to change the main goal!

*(Tip: Remember that `rw` replaces the left side of an equation with the right side, unless you use a left arrow `rw [← h_eq]` via `\\l`.)*
"


/-- Congruence modulo m is symmetric. -/
Statement mod_symm (a b m : ℤ) (h : a ≡ b (mod m)) : b ≡ a (mod m) := by
  unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use -k

  have h_eq : b - a = -(a - b)
  · ring

  rw [h_eq, hk]
  ring

Conclusion "
Beautiful! You used `have` to build a bridge between the algebra you had and the algebra you needed, and learned how to modify everything at once with `at *`.
"
