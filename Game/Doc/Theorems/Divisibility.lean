import GameServer


/-- 1 divides any integer. -/
TheoremDoc one_dvd as "one_dvd" in "Divisibility"


/-- Divisibility is reflexive: `a ∣ a`. -/
TheoremDoc dvd_refl as "dvd_refl" in "Divisibility"


/-- Any integer divides zero. -/
TheoremDoc dvd_zero as "dvd_zero" in "Divisibility"


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



