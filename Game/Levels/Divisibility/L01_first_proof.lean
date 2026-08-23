import GameServer
import Mathlib.Tactic
import Game.Levels.Definitions
import Game.Doc.Definitions
import Game.Doc.Tactics
import Game.Doc.Theorems.Divisibility

World "Divisibility"
Level 1
Title "Your First Proof"


NewTactic use
NewDefinition Dvd.dvd

Introduction "
Welcome to your first level! In Lean, you write proofs by using **tactics**. Tactics are commands that manipulate the goal until it is solved.

Our first statement is `3 ∣ 12`, which is read as \"3 divides 12\".
Check your **Definitions** tab on the right to read exactly what this means mathematically!

*(To type `∣`, write `\\mid` and press Space.)*

Lean sees `3 ∣ 12` as `∃ k, 12 = 3 * k`.
To prove this, you need to provide the number $k$. You can do this using the `use` tactic.
Type `use 4`. Lean will automatically substitute $k$ with 4 and close the goal since 12 equals 3 * 4!
"

/-- The exercise statement: 3 divides 12. -/
Statement : 3 ∣ 12 := by
  use 4

Conclusion "
Congratulations! You have just written your first proof in Lean 4!
You used `use` to provide a witness, and Lean automatically closed the obvious equality.
"

