import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L08_cancel_general

World "GCD"
Level 9
Title "Antisymmetry of Divisibility"

Introduction "
One last small tool before the final boss.

If $d_1$ and $d_2$ are both **non-negative** integers, and $d_1 \\mid d_2$ while also $d_2 \\mid d_1$, then $d_1 = d_2$.

*(Non-negativity really is needed: on all of $\\mathbb{Z}$ this can fail — for instance $3 \\mid (-3)$ and $(-3) \\mid 3$, yet $3 \\neq -3$. Once both numbers are required to be $\\geq 0$, this kind of \"mirrored pair\" becomes impossible, and mutual divisibility forces equality.)*

The Mathlib theorem `Int.dvd_antisymm` packages up exactly this reasoning for us. We simply invoke it with `exact`.
"

/--
**Antisymmetry of Divisibility (for non-negative integers)**

If $0 \le d_1$, $0 \le d_2$, $d_1 \mid d_2$, and $d_2 \mid d_1$, then $d_1 = d_2$.

**Why we need it:**
Divisibility on all of $\mathbb{Z}$ only forms a *pre-order*: two different numbers can divide each other, as long as one is the negative of the other. Restricted to non-negative integers, though, divisibility becomes a genuine **partial order**: "mutual divisibility" really does collapse to equality.

In the very next level, we will show two gcd-witnesses divide each other, and use exactly this fact to conclude they must be the *same* number.
-/
TheoremDoc dvd_antisymm as "dvd_antisymm" in "GCD"

NewTheorem Int.dvd_antisymm

/-- On non-negative integers, mutual divisibility implies equality. -/
Statement dvd_antisymm (d1 d2 : ℤ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (h1 : d1 ∣ d2) (h2 : d2 ∣ d1) : d1 = d2 := by
  exact Int.dvd_antisymm hd1 hd2 h1 h2

Conclusion "
Short and sweet. `Int.dvd_antisymm` (saved here as `dvd_antisymm`) is now in your inventory — you'll use it immediately in the final challenge of this world.
"
