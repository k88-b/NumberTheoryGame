import GameServer


/--
**One Divides Everything**

For any integer $a$: $1 \mid a$.
-/
TheoremDoc one_dvd as "one_dvd" in "Divisibility"


/--
**Reflexivity of Divisibility**

Every integer divides itself: $a \mid a$.
-/
TheoremDoc dvd_refl as "dvd_refl" in "Divisibility"


/--
**Every Integer Divides Zero**

For any integer $a$: $a \mid 0$.
-/
TheoremDoc dvd_zero as "dvd_zero" in "Divisibility"


/--
**Transitivity of Divisibility**

If $a$ divides $b$, and $b$ divides $c$, then $a$ divides $c$.

**Intuition:**
Think of it as building blocks. If a stick $b$ is made of exactly 3 blocks of $a$,
and a stick $c$ is made of exactly 4 sticks of $b$, then $c$ is made of $3 \cdot 4 = 12$ blocks of $a$.
Divisibility chains perfectly! In Lean, if you have `h1 : a ∣ b` and `h2 : b ∣ c`, applying this theorem proves `a ∣ c`.
-/
TheoremDoc dvd_trans as "dvd_trans" in "Divisibility"
