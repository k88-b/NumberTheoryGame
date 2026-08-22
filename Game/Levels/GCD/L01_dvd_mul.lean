import GameServer
import Mathlib.Tactic
import Game.Levels.Definitions
import Game.Doc.Definitions
import Game.Doc.Tactics
import Game.Doc.Theorems.GCD


World "GCD"
Level 1
Title "A Divisor of a Factor Divides the Product"

Introduction "
Before we dive into the Greatest Common Divisor itself, we need one small but very useful building block.

If $d$ divides $a$, does $d$ also divide $a \\cdot b$ for *any* integer $b$?
Yes! If $a$ is a multiple of $d$, then any multiple of $a$ is automatically a multiple of $d$ too.

You already have every tool you need for this one: `obtain` the witness from your hypothesis, `use` the right witness for the new goal, `rw`, and finish with `ring` — similar to the witness-gluing pattern you used in World 1."


/-- If d divides a, then d divides a * b for any integer b. -/
Statement dvd_mul_of_dvd_left (a b d : ℤ) (h : d ∣ a) : d ∣ (a * b) := by
  Hint "Start by extracting the witness from your hypothesis using `obtain ⟨k, hk⟩ := {h}`."
  obtain ⟨k, hk⟩ := h
  Hint (hidden := true) "Since `{a} = {d} * {k}`, you want to show `{a} * {b} = {d} * ({k} * {b})`. Try to `use {k} * {b}`."
  use k * b
  rw [hk]
  ring

Conclusion "
Perfect! Keep `dvd_mul_of_dvd_left` close at hand — you'll use it again and again in this world.
"
