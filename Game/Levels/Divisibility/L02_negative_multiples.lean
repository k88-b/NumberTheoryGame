import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L01_first_proof

World "Divisibility"
Level 2
Title "Negative Multiples"

NewTactic ring

Introduction "
Divisibility isn't limited to positive numbers — it works across all integers ($\\mathbb{Z}$), including negative ones!

Here we want to prove `5 ∣ -15`, which means finding an integer $k$ such that $-15 = 5 \\cdot k$.
Once you provide the witness with `use`, finish off the arithmetic using a powerful new tactic: `ring`.

**Tip:** Every time you unlock a new tactic (like `use` or `ring`), it is added to the **Tactics** tab on the right. Check that tab anytime you want to read what a tactic does or see examples of how to use it!
"

/-- 5 divides -15. -/
Statement : 5 ∣ -15 := by
  use -3
  ring

Conclusion "
Spot on! Negative witnesses work just like positive ones, and `ring` will soon become your best friend once variables enter the picture.
"
