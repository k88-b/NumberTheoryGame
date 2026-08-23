import GameServer


/--
**Reflexivity of Congruences**

Every integer is congruent to itself: $a \equiv a \pmod m$.
-/
TheoremDoc mod_refl as "mod_refl" in "Congruence"


/--
**Symmetry of Congruences**

If $a \equiv b \pmod m$, then $b \equiv a \pmod m$.

**Intuition:**
If the difference between $a$ and $b$ is a multiple of $m$, the difference between $b$ and $a$ is just the same multiple with a negative sign.
For example, $17 \equiv 5 \pmod{12}$ because $17 - 5 = 12$.
Conversely, $5 \equiv 17 \pmod{12}$ because $5 - 17 = -12$, which is still a multiple of $12$ ($12 \cdot -1$).
-/
TheoremDoc mod_symm as "mod_symm" in "Congruence"


/--
**Transitivity of Modular Congruence**

If $a \equiv b \pmod m$ and $b \equiv c \pmod m$, then $a \equiv c \pmod m$.

**Meaning:** This theorem proves that modular arithmetic is a true *equivalence relation*. It means you can chain congruences together step-by-step to reach a conclusion, exactly like you can chain regular equations ($a = b$ and $b = c \implies a = c$).
-/
TheoremDoc mod_trans as "mod_trans" in "Congruence"


/--
**Adding Congruences**

If $a \equiv b \pmod m$ and $c \equiv d \pmod m$, then $(a + c) \equiv (b + d) \pmod m$.

**Intuition:**
If two pairs of numbers have the same remainder when divided by $m$, their sums will also have the same remainder.
For example, modulo 10 (which just looks at the last digit):
If $12 \equiv 2 \pmod{10}$ and $25 \equiv 5 \pmod{10}$, then $12 + 25 = 37$, which is $\equiv 7 \pmod{10}$.
Notice that $2 + 5 = 7$. We just added the remainders safely!
-/
TheoremDoc mod_add as "mod_add" in "Congruence"


/--
**Multiplying by a Constant**

If $a \equiv b \pmod m$, then $a \cdot c \equiv b \cdot c \pmod m$.
-/
TheoremDoc mod_mul_const as "mod_mul_const" in "Congruence"


/--
**Multiplying Congruences**

If $a \equiv b \pmod m$ and $c \equiv d \pmod m$, then $(a \cdot c) \equiv (b \cdot d) \pmod m$.

**Intuition:**
Just like addition, you can multiply remainders directly!
Modulo 10: $12 \equiv 2$ and $13 \equiv 3$.
If we multiply them: $12 \cdot 13 = 156$.
And $156 \equiv 6 \pmod{10}$. Notice that $2 \cdot 3$ is exactly $6$.
-/
TheoremDoc mod_mul as "mod_mul" in "Congruence"


/--
**Shifting by a Multiple of the Modulus**

For any integer $k$: $a + k \cdot m \equiv a \pmod m$.
-/
TheoremDoc mod_add_multiple as "mod_add_multiple" in "Congruence"


/--
`pow_succ` is a theorem from Mathlib that states $a^{n+1} = a^n \cdot a$.
Use `rw [pow_succ]` when dealing with powers in induction.
-/
TheoremDoc pow_succ as "pow_succ" in "Algebra"


/--
**Powers of Congruences**

If $a \equiv b \pmod m$, then $a^n \equiv b^n \pmod m$ for any natural number $n$.
-/
TheoremDoc mod_pow as "mod_pow" in "Congruence"


/--
**Scaling the Modulus**

If $a \equiv b \pmod m$, then $a \cdot c \equiv b \cdot c \pmod{m \cdot c}$.
-/
TheoremDoc mod_scale as "mod_scale" in "Congruence"


/--
**Shrinking the Modulus**

If $a \equiv b \pmod m$ and $d \mid m$, then $a \equiv b \pmod d$.
-/
TheoremDoc mod_shrink as "mod_shrink" in "Congruence"


/--
**Splitting the Modulus**

If $a \equiv b \pmod{m \cdot n}$, then $a \equiv b \pmod m$ and $a \equiv b \pmod n$.

**Intuition:**
If a difference $(a - b)$ is a multiple of $15$ ($3 \cdot 5$), it must logically be a multiple of $3$ and a multiple of $5$.
So if two numbers are congruent modulo 15, they are automatically congruent modulo 3 and modulo 5.
This is a crucial stepping stone towards the Chinese Remainder Theorem!
-/
TheoremDoc mod_split as "mod_split" in "Congruence"
