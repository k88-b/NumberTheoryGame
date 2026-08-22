import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 5
Title "Chain of Divisors (Boss)"


NewTactic obtain rw

Introduction "
Welcome to the final boss of the Divisibility Club!

If $x$ divides $y$, and $y$ divides $z$, does $x$ divide $z$? Yes! This is called **transitivity**, and proving it will require you to combine everything you've learned.

Since `x ∣ y` means there is some multiplier, we want to extract it. Type `obtain ⟨k1, hk1⟩ := h1`.

*(Lean uses special mathematical brackets: to type `⟨`, write `\\<` and press Space. To type `⟩`, write `\\>` and press Space).*

Lean will give you a number `k1` and the fact `hk1 : y = x * k1`.
Do the same for `h2` to get `k2` and `hk2`.

Next, figure out what you need to `use` to prove $x \\mid z$.
Finally, use the `rw` (rewrite) tactic. `rw [hk2]` will replace `y` in your goal based on your hypothesis!

Good luck!
"


/-- Divisibility is transitive. -/
Statement dvd_trans (x y z : ℤ) (h1 : x ∣ y) (h2 : y ∣ z) : x ∣ z := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2

  Branch
    rw [hk2, hk1]
    Hint "The goal now expresses z purely in terms of x, k1 and k2 — nothing else is left. Look at what's multiplying x; that's exactly the single number the goal is asking you to supply."

  Hint (hidden := true) "Think it through: z = y·k2, and y = x·k1, so z = (x·k1)·k2 = x·(k1·k2). A single number built from k1 and k2 already turns x into z — that's the witness this goal wants."
  use k1 * k2

  rw [hk2, hk1]
  ring

Conclusion "
🎉 INCREDIBLE! 🎉

You have conquered the first world! You successfully proved that divisibility chains perfectly, completing your first multi-step abstract proof. By combining the two witnesses $k_1$ and $k_2$, you found the exact witness for $x \\mid z$.

You've mastered the foundational tactics `use`, `obtain`, `rw`, and `ring`.
Get ready for World 2, where we will introduce a massive new concept based on this: Modular Arithmetic (Congruences)!
"
