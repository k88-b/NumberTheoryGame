import GameServer


/--
**Modular Inverse Existence**

If $\text{IsGCD}(a, m) 1$, then there exists an integer $x$ such that $a \cdot x \equiv 1 \pmod m$.

**Intuition:**
Coprimality gives $a \cdot x + m \cdot y = 1$, i.e. $a \cdot x = 1 - m \cdot y$ — meaning $a \cdot x$ is exactly $1$ *shifted by a multiple of $m$*. That's precisely what "$\equiv 1 \pmod m$" means.

For example: $\gcd(3, 7) = 1$, and $3 \cdot (-2) + 7 \cdot 1 = 1$. So $x = -2$ works: $3 \cdot (-2) = -6$, and indeed $-6 \equiv 1 \pmod 7$ (since $-6 - 1 = -7 = 7 \cdot (-1)$).
-/
TheoremDoc inv_exists as "inv_exists" in "LinCong"


/--
**Reverse Inverse**

If $a \cdot x \equiv 1 \pmod m$ for some $x$, then $\text{IsGCD}(a, m) 1$.
-/
TheoremDoc inv_implies_coprime as "inv_implies_coprime" in "LinCong"


/--
**Uniqueness of Inverse**

If $a \cdot x \equiv 1 \pmod m$ and $a \cdot y \equiv 1 \pmod m$, then $x \equiv y \pmod m$.
-/
TheoremDoc inv_unique as "inv_unique" in "LinCong"


/--
**Solvability (Necessary Condition)**

If $d = \gcd(a, m)$ and $a \cdot x \equiv b \pmod m$ has a solution, then $d \mid b$.
-/
TheoremDoc lin_cong_nec as "lin_cong_nec" in "LinCong"


/--
**Solvability (Sufficient Condition)**

If $d = \gcd(a, m)$ and $d \mid b$, then $\exists x, a \cdot x \equiv b \pmod m$.
-/
TheoremDoc lin_cong_suff as "lin_cong_suff" in "LinCong"


/--
**Congruent Solutions modulo $m/d$**

All solutions to $a \cdot x \equiv b \pmod m$ are congruent modulo $m/d$.
-/
TheoremDoc lin_cong_sol_equiv as "lin_cong_sol_equiv" in "LinCong"


/--
**Shifting the Solution**

Any shift of a solution by a multiple of $m/d$ yields another valid solution.
-/
TheoremDoc lin_cong_sol_shift as "lin_cong_sol_shift" in "LinCong"


/--
**Euclid's Lemma**

If $m \mid (a \cdot c)$ and $c$ is coprime to $m$, then $m \mid a$.
-/
TheoremDoc euclids_lemma as "euclids_lemma" in "LinCong"


/--
**CRT Existence**

If $\gcd(m, n) = 1$, then there exists an $x$ solving both congruences.

**Intuition:**
Build $x$ from two pieces using Bézout witnesses $u, v$ with $m \cdot u + n \cdot v = 1$. The term $n \cdot v$ behaves like "$1$" modulo $m$ (and vanishes modulo $n$), while $m \cdot u$ behaves like "$1$" modulo $n$ (and vanishes modulo $m$). So $x = a \cdot n \cdot v + b \cdot m \cdot u$ picks up $a$'s value mod $m$ and $b$'s value mod $n$ simultaneously.

**Example:** solving $x \equiv 2 \pmod 3$ and $x \equiv 3 \pmod 5$: here $3 \cdot 2 + 5 \cdot (-1) = 1$, so $u = 2, v = -1$. This gives $x = 2 \cdot 5 \cdot (-1) + 3 \cdot 3 \cdot 2 = -10 + 18 = 8$. Check: $8 \equiv 2 \pmod 3$ ✓ and $8 \equiv 3 \pmod 5$ ✓.
-/
TheoremDoc crt_exists as "crt_exists" in "LinCong"


/--
**Glued Modulus**

If $x \equiv a \pmod m$ and $x \equiv a \pmod n$ with coprime moduli, then $x \equiv a \pmod{m \cdot n}$.

**Intuition:**
$x - a$ is a multiple of both $m$ and $n$ separately. If $m$ and $n$ share no common factor, the only way a number can be built from both is by being a multiple of their product $m \cdot n$ — nothing is double-counted. This is exactly why coprimality matters: if $m = n = 2$, a number could be a multiple of both without being a multiple of $m \cdot n = 4$ (e.g. $x - a = 2$).

**Example:** $12$ is a multiple of both $3$ and $4$ (coprime!), and indeed $12$ is a multiple of $3 \cdot 4 = 12$.
-/
TheoremDoc crt_glue as "crt_glue" in "LinCong"


/--
**Polynomial Congruences**

If $a \equiv b \pmod m$, then $P(a) \equiv P(b) \pmod m$ for any integer polynomial $P$.

**Intuition:**
This is the reason modular arithmetic is genuinely useful and not just a curiosity: congruence mod $m$ is compatible with *every* polynomial operation, so you can reduce numbers mod $m$ at any point in a calculation without changing the final remainder. It's what makes "clock arithmetic" behave like real arithmetic.
-/
TheoremDoc polynomial_cong as "polynomial_cong" in "LinCong"
