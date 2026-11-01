import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L01_concrete

World "Congruence"
Level 2
Title "Modular Arithmetic: Reflexivity"

Introduction "
Why did mathematicians invent the $\\equiv$ symbol to look so much like $=$? Because congruences obey almost all the same laws as standard equality!

Over the next few levels, we will prove that congruence modulo $m$ is an **equivalence relation**. The first requirement is **reflexivity**: every integer is congruent to itself modulo $m$:
$$a \\equiv a \\pmod m$$
"

/-- Every integer is congruent to itself. -/
Statement mod_refl (a m : ℤ) : a ≡ a (mod m) := by
  unfold ModEq
  use 0
  ring

Conclusion "
Great! Because $a - a = 0$, and $m \\mid 0$, it immediately follows that $a \\equiv a \\pmod m$.
One property down, two to go.
"
