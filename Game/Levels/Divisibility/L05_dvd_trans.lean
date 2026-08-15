import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 5
Title "Chain of Divisors (Transitivity)"

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
If $x$ divides $y$, and $y$ divides $z$, does $x$ divide $z$? Yes! This is called **transitivity**.

To prove an implication `P → Q`, you use `intro`. If you type `intro x y z h1 h2`, Lean will give you the variables and the hypotheses `h1 : x ∣ y` and `h2 : y ∣ z`.

Since `x ∣ y` means there is some multiplier, we want to extract it. Type `obtain ⟨k1, hk1⟩ := h1`.

Lean uses special mathematical brackets:
* To type `⟨`, write `\\<` and press Space.
* To type `⟩`, write `\\>` and press Space.

Lean will give you a number `k1` and the fact `hk1 : y = x * k1`.
Do the same for `h2` to get `k2` and `hk2`.

Next, figure out what you need to `use` to prove $x \\mid z$.
Finally, use the `rw` tactic. `rw [hk2]` will replace `y` in your goal based on your hypothesis!
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
  use k1 * k2
  rw [hk2]
  rw [hk1]
  ring

Conclusion "
Incredible work! You just completed a multi-step abstract proof.
By combining the two witnesses $k_1$ and $k_2$, you found the witness for $x \\mid z$.
"
