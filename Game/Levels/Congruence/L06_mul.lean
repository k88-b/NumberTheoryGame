import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L05_mul_const

World "Congruence"
Level 6
Title "Multiplying Congruences"


NewTactic exact

Introduction "
We know we can add congruences, but can we multiply them?
If $a \\equiv b \\pmod m$ and $c \\equiv d \\pmod m$, is $a \\cdot c \\equiv b \\cdot d \\pmod m$?

Instead of doing algebra from scratch, we can **reuse** our previous theorems!
Think about transitivity (`mod_trans` from World 1). We can step from $a \\cdot c$ to $b \\cdot c$, and then from $b \\cdot c$ to $b \\cdot d$.

You can explicitly apply a theorem to variables to create a new hypothesis:
`have h3 := mod_mul_const a b c m h1` will prove that $a \\cdot c \\equiv b \\cdot c \\pmod m$.

**Watch out for the order of multiplication!**
Applying `mod_mul_const` to $c \\equiv d$ with multiplier $b$ will give you $c \\cdot b \\equiv d \\cdot b$. You will need to manually flip the order to $b \\cdot c \\equiv b \\cdot d$ using a `have` block and `rw` before you can chain them together!

*(Reminder: to type the `≡` symbol in your `have` statement, type `\\==` and press Space)*

Use `have` to build your intermediate steps, and then use the `exact` tactic to finish the proof by providing `mod_trans`!
"


/-- If two pairs of numbers are congruent, their products are congruent. -/
Statement mod_mul (a b c d m : ℤ) (h1 : a ≡ b (mod m)) (h2 : c ≡ d (mod m)) : (a * c) ≡ (b * d) (mod m) := by
  have step1 := mod_mul_const a b c m h1
  have step2 := mod_mul_const c d b m h2

  Hint (hidden := true) "You know that `{c} * {b} ≡ {d} * {b}`. Because multiplication is commutative, this is equivalent to `{b} * {c} ≡ {b} * {d}`. Try proving this flipped version first, so you can smoothly chain everything together with transitivity."
  have step2_symm : (b * c) ≡ (b * d) (mod m) := by
    have hrw1 : b * c = c * b := by ring
    have hrw2 : b * d = d * b := by ring
    rw [hrw1, hrw2]
    exact step2

  exact mod_trans (a * c) (b * c) (b * d) m step1 step2_symm

Conclusion "
Masterful! You just constructed a proof entirely by gluing together previous theorems. This is how real mathematics is built!
"
