import GameServer
import Mathlib.Tactic
import Game.Levels.Defs
import Game.Doc.Tactics
import Game.Doc.Theorems.Congruence

World "Congruence"
Level 1
Title "Modular Arithmetic: Reflexivity"


NewDefinition ModEq
NewTactic unfold

Introduction "
We are now introducing a massive concept in number theory: **Congruences**.
We say that $a \\equiv b \\pmod m$ if $m$ divides $(a - b)$.

In Lean, we have defined a custom property for this and created a notation `a ≡ b (mod m)`.
Check your **Definitions** tab to read a detailed explanation and see some examples!

When you see this notation in the goal, you should type `unfold ModEq` to reveal what it actually means under the hood.

Let's prove that modular arithmetic is reflexive: $a \\equiv a \\pmod m$.
"

/-- Every integer is congruent to itself. -/
Statement mod_refl (a m : ℤ) : a ≡ a (mod m) := by
  unfold ModEq
  use 0
  ring

Conclusion "
Great! Because $a - a = 0$, and $m \\mid 0$, it immediately follows that $a \\equiv a \\pmod m$.
"
