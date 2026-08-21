import GameServer


/--
**A Divisor of a Factor Divides the Product**

If $d \mid a$, then $d \mid (a \cdot b)$ for any integer $b$.

**Intuition:**
If $a$ is built out of $k$ copies of $d$ (i.e. $a = d \cdot k$), then $a \cdot b$ is built out of $k \cdot b$ copies of $d$.
For example, $3 \mid 6$, so $3 \mid (6 \cdot 5) = 30$ as well.

This little lemma is a "brick" you will reuse constantly in this world: whenever you have a Bézout-style identity $a \cdot x + b \cdot y = d$ and you know some $c$ divides $a$ or $b$, this lemma lets you conclude $c$ divides the whole term $a \cdot x$ or $b \cdot y$.
-/
TheoremDoc dvd_mul_of_dvd_left as "dvd_mul_of_dvd_left" in "Divisibility"


/--
**The Bézout Definition Really Gives the Greatest Common Divisor**

If `IsGCD(a, b) d`, and $c$ is *any* common divisor of $a$ and $b$ (i.e. $c \mid a$ and $c \mid b$), then $c \mid d$.

**Intuition:**
This is what actually justifies the name "IsGCD": our Bézout-style definition doesn't just hand you *a* common divisor, it hands you the *greatest* one — every other common divisor is forced to divide it too. For example, $2$ and $3$ both divide $12$ and $18$, and indeed $2 \mid 6$ and $3 \mid 6$, where $6 = \text{IsGCD}(12, 18)$'s witness.

The proof works because $d$ is built from $a$ and $b$ via $a \cdot x + b \cdot y = d$: anything that divides both $a$ and $b$ automatically divides this whole combination, and hence divides $d$.
-/
TheoremDoc gcd_is_greatest as "gcd_is_greatest" in "GCD"


/--
**Coprimality Implies a Bézout Identity**

If `IsGCD(c, m) 1`, then there exist integers $x, y$ with $c \cdot x + m \cdot y = 1$.
-/
TheoremDoc coprime_imp_bezout as "coprime_imp_bezout" in "GCD"


/--
**A Bézout Identity with 1 Implies Coprimality**

If there exist integers $x, y$ with $c \cdot x + m \cdot y = 1$, then `IsGCD(c, m) 1`.
-/
TheoremDoc bezout_imp_coprime as "bezout_imp_coprime" in "GCD"


/--
**Cancellation Law for Coprime Factors**

If $a \cdot c \equiv b \cdot c \pmod m$ and `IsGCD(c, m) 1`, then $a \equiv b \pmod m$.

**Intuition:**
Multiplying both sides of a congruence by the same number is always safe (World 2!). This theorem shows the *reverse* direction — cancelling out a common factor — is *also* safe, but only when that factor shares no common divisor with the modulus. Coprimality is precisely the condition under which "dividing" makes sense in modular arithmetic.
-/
TheoremDoc mod_cancel_coprime as "mod_cancel_coprime" in "Congruence"


/--
The `mul_left_cancel₀` theorem lets you cancel a common non-zero factor from an equation:
if `a ≠ 0` and `a * b = a * c`, then `b = c`.
This works because the integers have no "zero divisors": the only way a product can vanish is if one of its factors does, so a non-zero factor can always be safely divided out of an equation.
-/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "Algebra"


/--
**Dividing by the GCD Gives Coprime Numbers**

If `IsGCD(c, m) d`, $d \neq 0$, $c = c_1 \cdot d$ and $m = m_1 \cdot d$, then `IsGCD(c_1, m_1) 1`.

**Intuition:**
This matches your intuition exactly: $\text{IsGCD}(12, 18) 6$, and dividing both by $6$ gives $2$ and $3$, which indeed satisfy $\text{IsGCD}(2, 3) 1$. Once you factor out everything two numbers have in common, whatever is left over shares nothing.
-/
TheoremDoc gcd_div_coprime as "gcd_div_coprime" in "GCD"


/--
**The General Cancellation Law**

If $a \cdot c \equiv b \cdot c \pmod m$, `IsGCD(c, m) d` with $d \neq 0$, $c = c_1 \cdot d$ and $m = m_1 \cdot d$, then $a \equiv b \pmod{m_1}$.

**Intuition:**
This is the fully general version of "dividing" a congruence: you can always cancel a factor $c$ out of a congruence, as long as you also divide the modulus by whatever $c$ and $m$ have in common (`such that IsGCD(c, m) d)`. The coprime case (Level 6) is just the special case $d = 1$, where the modulus doesn't need to shrink at all.
-/
TheoremDoc mod_cancel_general as "mod_cancel_general" in "Congruence"


/--
**Antisymmetry of Divisibility (for non-negative integers)**

If $0 \le d_1$, $0 \le d_2$, $d_1 \mid d_2$, and $d_2 \mid d_1$, then $d_1 = d_2$.

**Why we need it:**
Divisibility on all of $\mathbb{Z}$ only forms a *pre-order*: two different numbers can divide each other, as long as one is the negative of the other. Restricted to non-negative integers, though, divisibility becomes a genuine **partial order**: "mutual divisibility" really does collapse to equality.

In this boss level, we will show two gcd-witnesses divide each other, and use exactly this theorem to conclude they must be the *same* number.
-/
TheoremDoc Int.dvd_antisymm as "dvd_antisymm" in "Divisibility"


/--
**Shift Invariance of the GCD**

For any integers $a, k, m$, and non-negative gcd-witnesses $d_1, d_2$:
if `IsGCD(a + m * k, m) d1` and `IsGCD(a, m) d2`, then $d_1 = d_2$.

**Why this matters:**
This is the *engine* of the Euclidean Algorithm for computing GCDs: $\gcd(a + mk, m) = \gcd(a, m)$ for any integer $k$. In particular, replacing $a$ by its remainder after dividing by $m$ never changes the GCD with $m$ — which is exactly what lets the Euclidean Algorithm shrink its numbers step by step until it reaches the answer.
-/
TheoremDoc gcd_shift_invariant as "gcd_shift_invariant" in "GCD"




