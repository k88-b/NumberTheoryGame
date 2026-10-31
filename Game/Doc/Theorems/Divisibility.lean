import GameServer


/--
**Multiples of $a$**

For any integers $a$ and $b$: $a \mid a \cdot b$.

**Intuition:**
Any product containing $a$ as a factor is immediately a multiple of $a$ (with $b$ itself acting as the witness). In Lean, `dvd_mul_right_int a b` directly proves `a ∣ a * b`.
-/
TheoremDoc dvd_mul_right_int as "dvd_mul_right_int" in "Divisibility"


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
**Divisibility from Equality**

If $a \cdot k = b$, then $a \mid b$.

**Intuition:**
If you already have an explicit equation `h : a * k = b` in your hypotheses, applying `dvd_intro_int a b k h` proves `a ∣ b` directly without needing to rewrite and supply the witness $k$ manually.
-/
TheoremDoc dvd_intro_int as "dvd_intro_int" in "Divisibility"


/--
**Only Zero Is Divisible by Zero**

If $0 \mid a$, then $a = 0$.

**Intuition:**
While every integer divides $0$ ($a \mid 0$), the reverse is much stricter: since $0 \cdot k = 0$ for any $k$, the only number that $0$ can divide is $0$ itself. In Lean, given `h : 0 ∣ a`, applying `eq_zero_of_zero_dvd_int a h` yields `a = 0`.
-/
TheoremDoc eq_zero_of_zero_dvd_int as "eq_zero_of_zero_dvd_int" in "Divisibility"


/--
**A Divisor of a Factor Divides the Product**

If $d \mid a$, then $d \mid (a \cdot b)$ for any integer $b$.

**Intuition:**
If $a$ is built out of $k$ copies of $d$ (i.e. $a = d \cdot k$), then $a \cdot b$ is built out of $k \cdot b$ copies of $d$.
For example, $3 \mid 6$, so $3 \mid (6 \cdot 5) = 30$ as well.

This little lemma is a "brick" you will reuse constantly throughout the game: whenever you have a Bézout-style identity $a \cdot x + b \cdot y = d$ and you know some $c$ divides $a$ or $b$, this lemma lets you conclude $c$ divides the whole term $a \cdot x$ or $b \cdot y$.
-/
TheoremDoc dvd_mul_of_dvd_left_int as "dvd_mul_of_dvd_left_int" in "Divisibility"


/--
**Sums of Multiples**

If $a \mid b$ and $a \mid c$, then $a \mid (b + c)$.

**Intuition:**
Multiples of $a$ are closed under addition. If $b$ is made of $k_1$ blocks of $a$ and $c$ is made of $k_2$ blocks of $a$, then their sum $b + c$ is made of $k_1 + k_2$ blocks of $a$. In Lean, given `h1 : a ∣ b` and `h2 : a ∣ c`, `dvd_add_int a b c h1 h2` proves `a ∣ b + c`.
-/
TheoremDoc dvd_add_int as "dvd_add_int" in "Divisibility"


/--
**Transitivity of Divisibility**

If $x$ divides $y$, and $y$ divides $z$, then $x$ divides $z$.

**Intuition:**
Think of it as building blocks. If a stick $y$ is made of exactly 3 blocks of $x$,
and a stick $z$ is made of exactly 4 sticks of $y$, then $z$ is made of $3 \cdot 4 = 12$ blocks of $x$.
Divisibility chains perfectly! In Lean, if you have `h1 : x ∣ y` and `h2 : y ∣ z`, applying `dvd_trans_int x y z h1 h2` proves `x ∣ z`.
-/
TheoremDoc dvd_trans_int as "dvd_trans_int" in "Divisibility"


/--
**Divisibility of Linear Combinations**

If $d \mid a$ and $d \mid b$, then $d \mid (a \cdot x + b \cdot y)$ for any integers $x$ and $y$.

**Intuition:**
This combines `dvd_mul_of_dvd_left_int` (scaling) and `dvd_add_int` (addition) into one powerful rule: any common divisor of $a$ and $b$ automatically divides any linear combination $a \cdot x + b \cdot y$. You will rely on this heavily when working with Greatest Common Divisors and Bézout's identity!
-/
TheoremDoc dvd_lin_comb_int as "dvd_lin_comb_int" in "Divisibility"
