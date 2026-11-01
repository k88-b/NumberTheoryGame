import GameServer
import Mathlib.Tactic
import Game.Levels.ModArith.L02_sub

World "ModArith"
Level 3
Title "Adding a Constant"

Introduction "
If $a \\equiv b \\pmod m$, adding the same integer $c$ to both sides preserves the congruence:
$$a + c \\equiv b + c \\pmod m$$

We *could* unfold definitions and do the algebra again, but real mathematicians don't reinvent the wheel — they reuse what they've already proved!

Notice that:
- We know $a \\equiv b \\pmod m$ by hypothesis `h`.
- We know $c \\equiv c \\pmod m$ by `mod_refl` (from the Congruence world).
- We can combine these two facts using `mod_add` (from Level 1)!

You can combine `have` and `exact` to build proofs step by step:
1. First, state the intermediate fact you need: `have h_refl : c ≡ c (mod m)`.
2. Prove this new subgoal right away using `exact mod_refl c m`.
3. Finally, close the main goal by feeding both congruences into `mod_add` with `exact`!
"

/-- Adding a constant to both sides of a congruence. -/
Statement mod_add_const (a b c m : ℤ) (h : a ≡ b (mod m)) : (a + c) ≡ (b + c) (mod m) := by
  have h_refl : c ≡ c (mod m)
  · exact mod_refl c m

  exact mod_add a b c c m h h_refl

Conclusion "
You have mastered combining `have` and `exact` to chain existing theorems together! This is how large mathematical libraries are constructed.
"
