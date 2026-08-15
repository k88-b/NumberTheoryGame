import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L02_mul_const

World "Congruence"
Level 3
Title "Multiplying Congruences"

/--
The `exact` tactic closes a goal if you provide a theorem that perfectly matches the goal.
-/
TacticDoc exact

NewTactic exact

Introduction "
We know we can add congruences, but can we multiply them?
If $a \\equiv b \\pmod m$ and $c \\equiv d \\pmod m$, is $a \\cdot c \\equiv b \\cdot d \\pmod m$?

Instead of doing algebra from scratch, we can **reuse** our previous theorems!
Think about transitivity (`mod_trans` from World 1). We can step from $a \\cdot c$ to $b \\cdot c$, and then from $b \\cdot c$ to $b \\cdot d$.

You can explicitly apply a theorem to variables to create a new hypothesis:
`have h3 := mod_mul_const a b c m h1` will prove that $a \\cdot c \\equiv b \\cdot c \\pmod m$.

Use `have` to build your intermediate steps, and then use the `exact` tactic to finish the proof by providing `mod_trans`!
"

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


/-- If two pairs of numbers are congruent, their products are congruent. -/
Statement mod_mul (a b c d m : ℤ) (h1 : a ≡ b (mod m)) (h2 : c ≡ d (mod m)) : (a * c) ≡ (b * d) (mod m) := by
  have step1 := mod_mul_const a b c m h1
  have step2 := mod_mul_const c d b m h2
  have step2_symm : (b * c) ≡ (b * d) (mod m) := by
    -- We know c*b ≡ d*b, so we rewrite it.
    have hrw1 : b * c = c * b := by ring
    have hrw2 : b * d = d * b := by ring
    rw [hrw1, hrw2]
    exact step2
  exact mod_trans (a * c) (b * c) (b * d) m step1 step2_symm

Conclusion "
Masterful! You just constructed a proof entirely by gluing together previous theorems. This is how real mathematics is built!
"
