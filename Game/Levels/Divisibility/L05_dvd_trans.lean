import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 5
Title "Chain of Divisors (Boss)"

/--
The `obtain` tactic extracts a witness from a hypothesis that contains an \"exists\" ($\exists$).
If you have a hypothesis `h : x ∣ y` (which means `∃ k, y = x * k`), you can type
`obtain ⟨k, hk⟩ := h` to get the variable `k` and the equation `hk : y = x * k`.
-/
TacticDoc obtain

/--
The `rw` (rewrite) tactic replaces a term with an equivalent term based on an equality you have.
If you have `h : A = B`, typing `rw [h]` will replace `A` with `B` in your goal.
-/
TacticDoc rw

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

/--
**Transitivity of Divisibility**

If $a$ divides $b$, and $b$ divides $c$, then $a$ divides $c$.

**Intuition:**
Think of it as building blocks. If a stick $b$ is made of exactly 3 blocks of $a$,
and a stick $c$ is made of exactly 4 sticks of $b$, then $c$ is made of $3 \cdot 4 = 12$ blocks of $a$.
Divisibility chains perfectly!

**In Lean:**
If you have `h1 : a ∣ b` and `h2 : b ∣ c`, applying this theorem proves `a ∣ c`.
-/
TheoremDoc dvd_trans as "dvd_trans" in "Divisibility"


/-- Divisibility is transitive. -/
Statement dvd_trans (x y z : ℤ) (h1 : x ∣ y) (h2 : y ∣ z) : x ∣ z := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2

  Branch
    rw [hk2]
    rw [hk1]
    Hint "You have successfully rewritten the goal! Now try to `use {k1} * {k2}` as your witness."

  Hint (hidden := true) "To prove `{x} ∣ {z}`, you need to find a multiplier. Since `{y} = {x} * {k1}` and `{z} = {y} * {k2}`, try to `use {k1} * {k2}` as your witness."
  use k1 * k2

  rw [hk2]
  rw [hk1]

  ring

Conclusion "
🎉 INCREDIBLE! 🎉

You have conquered the first world! You successfully proved that divisibility chains perfectly, completing your first multi-step abstract proof. By combining the two witnesses $k_1$ and $k_2$, you found the exact witness for $x \\mid z$.

You've mastered the foundational tactics `use`, `obtain`, `rw`, and `ring`.
Get ready for World 2, where we will introduce a massive new concept based on this: Modular Arithmetic (Congruences)!
"
