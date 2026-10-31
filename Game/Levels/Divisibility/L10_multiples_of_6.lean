import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L09_eq_zero_of_zero_dvd

World "Divisibility"
Level 10
Title "Multiples of 6"

Introduction "
Now let's combine unpacking a hypothesis with proving a new divisibility goal!

Suppose $6$ divides $x$ (`h : 6 ∣ x`). Does $3$ also divide $x$?
Yes! Unpack `h` using `obtain ⟨k, hk⟩ := h` to get `hk : x = 6 * k`.

Since $6 \\cdot k = 3 \\cdot (2 \\cdot k)$, what witness should you `use` to prove `3 ∣ x`?
"

/-- Every multiple of 6 is also a multiple of 3. -/
Statement (x : ℤ) (h : 6 ∣ x) : 3 ∣ x := by
  obtain ⟨k, hk⟩ := h
  use 2 * k
  rw [hk]
  ring

Conclusion "
Spot on! This four-step rhythm — `obtain`, `rw`, `use`, `ring` — is the bread and butter of divisibility proofs.
"
