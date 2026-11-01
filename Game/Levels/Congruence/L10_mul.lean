import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L09_mul_const

World "Congruence"
Level 10
Title "Multiplying Congruences"

Introduction "
We know we can add and subtract congruences, but can we multiply them?
If $a \\equiv b \\pmod m$ and $c \\equiv d \\pmod m$, is $a \\cdot c \\equiv b \\cdot d \\pmod m$?

Just like in Level 8, instead of doing algebra from scratch, we can glue together our previous theorems using `have` and `exact`!
Think about transitivity (`mod_trans` from Level 5). We can step from $a \\cdot c$ to $b \\cdot c$, and then from $b \\cdot c$ to $b \\cdot d$, using `mod_mul_const` (from Level 9) for each step.

**Syntax Tip: Parentheses!**
When passing compound expressions like $a \\cdot c$ as arguments to a theorem, you **must** wrap them in parentheses so Lean knows they are a single argument:
`exact mod_trans (a * c) (b * c) (b * d) m step1 step2_symm`

**Watch out for the order of multiplication!**
Applying `mod_mul_const` to $c \\equiv d$ with multiplier $b$ gives $c \\cdot b \\equiv d \\cdot b$. You will need to manually flip the order to $b \\cdot c \\equiv b \\cdot d$ using a `have` block and `rw` before chaining everything together with `mod_trans`.
"

/-- If two pairs of numbers are congruent, their products are congruent. -/
Statement mod_mul (a b c d m : ℤ) (h1 : a ≡ b (mod m)) (h2 : c ≡ d (mod m)) : (a * c) ≡ (b * d) (mod m) := by
  have step1 : (a * c) ≡ (b * c) (mod m)
  · exact mod_mul_const a b c m h1

  have step2 : (c * b) ≡ (d * b) (mod m)
  · exact mod_mul_const c d b m h2

  Hint (hidden := true) "You know that `{c} * {b} ≡ {d} * {b}`. Because multiplication is commutative, this is equivalent to `{b} * {c} ≡ {b} * {d}`. Try proving this flipped version first, so you can smoothly chain everything together with transitivity."
  have step2_symm : (b * c) ≡ (b * d) (mod m)
  · have hrw1 : b * c = c * b
    · ring

    have hrw2 : b * d = d * b
    · ring

    rw [hrw1, hrw2]
    exact step2

  exact mod_trans (a * c) (b * c) (b * d) m step1 step2_symm

Conclusion "
Masterful! You just constructed a multi-step proof entirely by gluing together previous theorems. This is how real mathematics is built!
"
