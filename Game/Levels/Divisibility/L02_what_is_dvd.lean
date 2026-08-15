import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 2
Title "What exactly does 'divides' mean?"

/--
The `intro` tactic is used to introduce variables from a \"For all\" ($\\forall$) statement
or to assume the premise of an implication ($\\implies$).
For example, if the goal is `∀ a, P a`, typing `intro a` moves `a` into your context.
-/
TacticDoc intro

/--
The `ring` tactic automatically proves algebraic equalities like `x + y = y + x`
or `x * 1 = x`. It is a powerful tool so you don't have to manually apply axioms.
-/
TacticDoc ring

NewTactic intro ring

Introduction "
Now let's prove something abstract. We want to prove that 1 divides any integer $a$.
The statement starts with `∀ a : ℤ` (For all integers $a$).

When your goal starts with a \"For all\" ($\\forall$), your first step is usually to pick an arbitrary element.
You can do this using the `intro` tactic. Type `intro a` to bring $a$ into your context.

After that, remember that $1 \\mid a$ means $a = 1 \\cdot k$ for some $k$. What should $k$ be?
Use the `use` tactic, and then close the algebra with our new super-tactic: `ring`.
"

/-- 1 divides any integer. -/
TheoremDoc one_dvd as "one_dvd" in "Divisibility"

/-- 1 divides every integer. -/
Statement one_dvd : ∀ a : ℤ, 1 ∣ a := by
  intro a
  use a
  ring

Conclusion "
Great job! `intro a` is a tactic you will use constantly whenever you need to prove a statement for *any* element. Notice that this theorem is now saved in your inventory as `one_dvd`!
"
