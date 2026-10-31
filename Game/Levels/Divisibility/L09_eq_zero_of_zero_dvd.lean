import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L08_rewriting_backwards

World "Divisibility"
Level 9
Title "Only Zero Is Divisible by Zero"

NewTactic obtain

Introduction "
In Level 6, we proved that everything divides $0$ (`a ∣ 0`). What if we flip it around and ask what $0$ can divide (`0 ∣ a`)?
Only $0$ itself!

Notice a crucial difference here: `h : 0 ∣ a` is now a **hypothesis**, not the goal.
Since `0 ∣ a` means there exists some $k$ such that $a = 0 \\cdot k$, how do we unpack that $k$ from `h`?

We use the `obtain` tactic! Type `obtain ⟨k, hk⟩ := h`.

*(To type `⟨` and `⟩`, write `\\<` and `\\>`, then press Space.)*

Lean will extract the witness `k` along with the equation `hk : a = 0 * k`. From there, `rw [hk]` and `ring` will finish the proof!
"

/-- If 0 divides a, then a = 0. -/
Statement eq_zero_of_zero_dvd_int (a : ℤ) (h : 0 ∣ a) : a = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  ring

Conclusion "
Great work! Here is the golden rule of divisibility in Lean:
- When `a ∣ b` is in the **goal**, you build it with `use`.
- When `a ∣ b` is in a **hypothesis**, you unpack it with `obtain`.
"
