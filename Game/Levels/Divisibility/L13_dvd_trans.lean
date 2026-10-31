import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L12_dvd_add

World "Divisibility"
Level 13
Title "Chain of Divisors"

Introduction "
If $x$ divides $y$, and $y$ divides $z$, does $x$ divide $z$?
Yes! This fundamental property is called **transitivity**.

Just like in the previous level, start by unpacking both hypotheses `h1` and `h2` with `obtain`:
- `obtain ⟨k1, hk1⟩ := h1` gives `hk1 : y = x * k1`
- `obtain ⟨k2, hk2⟩ := h2` gives `hk2 : z = y * k2`

Now chain the two equations together: if you replace $y$ inside $z = y \\cdot k_2$ with $x \\cdot k_1$, what multiplier is sitting next to $x$?
"

/-- Divisibility is transitive. -/
Statement dvd_trans_int (x y z : ℤ) (h1 : x ∣ y) (h2 : y ∣ z) : x ∣ z := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2

  Branch
    rw [hk2, hk1]
    Hint "The goal now expresses z purely in terms of x, k1, and k2 — nothing else is left. Look at what's multiplying x; that's the single witness the goal is asking you to supply."

  Hint (hidden := true) "Think it through: z = y·k2, and y = x·k1, so z = (x·k1)·k2 = x·(k1·k2). A single number built from k1 and k2 already turns x into z — that's the witness this goal wants."
  use k1 * k2

  rw [hk2, hk1]
  ring

Conclusion "
Brilliant! By multiplying the two witnesses $k_1$ and $k_2$, you proved that divisibility chains together seamlessly (`dvd_trans_int`).

Now, one last challenge stands between you and the end of World 1!
"
