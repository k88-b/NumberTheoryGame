import GameServer


/--
**One Divides Everything**

For any integer $a$: $1 \mid a$.
-/
TheoremDoc one_dvd_int as "one_dvd_int" in "Divisibility"


/--
**Reflexivity of Divisibility**

Every integer divides itself: $a \mid a$.
-/
TheoremDoc dvd_refl_int as "dvd_refl_int" in "Divisibility"


/--
**Every Integer Divides Zero**

For any integer $a$: $a \mid 0$.
-/
TheoremDoc dvd_zero_int as "dvd_zero_int" in "Divisibility"


/--
**Transitivity of Divisibility**

If $a$ divides $b$, and $b$ divides $c$, then $a$ divides $c$.

**Intuition:**
Think of it as building blocks. If a stick $b$ is made of exactly 3 blocks of $a$,
and a stick $c$ is made of exactly 4 sticks of $b$, then $c$ is made of $3 \cdot 4 = 12$ blocks of $a$.
Divisibility chains perfectly! In Lean, if you have `h1 : a ∣ b` and `h2 : b ∣ c`, applying this theorem proves `a ∣ c`.
-/
TheoremDoc dvd_trans_int as "dvd_trans_int" in "Divisibility"
