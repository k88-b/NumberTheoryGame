import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L03_gcd_greatest

World "GCD"
Level 4
Title "Coprimality Gives You Bézout (⟹)"

Introduction "
Two integers $c$ and $m$ are called **coprime** (or *relatively prime*) exactly when their greatest common divisor is $1$: `IsGCD(c, m) 1`.

By our definition, this immediately gives us a Bézout identity: there exist integers $x, y$ with $c \\cdot x + m \\cdot y = 1$.

**Note:** an \"if and only if\" statement like this one is always split into two separate levels in this game — one per direction of the arrow. This level is the \"$\\implies$\" direction; the next one is \"$\\impliedby$\".

This direction is really just unpacking the definition: `unfold IsGCD at h` to get access to the pieces, `obtain` to peel them apart, and hand the pieces straight back with `use`.

**Note:** Since we only need $x$ and $y$ and don't care about the divisibility facts, we can use an underscore `_` to discard that part of the pattern: `obtain ⟨_, x, y, hxy⟩ := h`.
"


/-- Coprimality gives a Bézout identity. -/
Statement coprime_imp_bezout (c m : ℤ) (h :  IsGCD(c, m) 1) : ∃ x y : ℤ, c * x + m * y = 1 := by
  unfold IsGCD at h
  obtain ⟨_, x, y, hxy⟩ := h

  use x, y

Conclusion "
Straightforward! You've now confirmed one half of the equivalence: coprimality *implies* a Bézout identity.
"
