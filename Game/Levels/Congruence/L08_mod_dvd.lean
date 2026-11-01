import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L07_mod_scale

World "Congruence"
Level 8
Title "Shrinking the Modulus"

NewTactic exact

Introduction "
Think of a 12-hour clock: if two events happen at the same hour on a 12-hour cycle, they also line up on a 6-hour or 4-hour cycle.
In general, if $a \\equiv b \\pmod m$, then $a$ and $b$ remain congruent modulo any divisor $d$ of $m$:
$$d \\mid m \\implies a \\equiv b \\pmod d$$

Once you run `unfold ModEq at *`, look at what you have:
- `h2 : d ∣ m`
- `h1 : m ∣ a - b`
- Goal: `d ∣ a - b`

We *could* unpack `h1` and `h2` with `obtain`, or we can reuse `dvd_trans_int` from World 2!

**How to apply theorems (`exact`):**
Check the **Theorems** tab on the right. A theorem's signature tells you what inputs it expects and in what order:
`dvd_trans_int (x y z : ℤ) (h1 : x ∣ y) (h2 : y ∣ z) : x ∣ z`
Whenever a theorem directly matches your goal, you can close the goal in one step using **`exact`**, followed by the theorem's name and its arguments separated by spaces.

**Syntax Tip: Parentheses!**
When passing a compound expression like `a - b` as a single argument, you **must** wrap it in parentheses:
`exact dvd_trans_int d m (a - b) h2 h1`
"


/-- Decreasing the modulus to a divisor. -/
Statement mod_shrink (a b m d : ℤ) (h1 : a ≡ b (mod m)) (h2 : d ∣ m) : a ≡ b (mod d) := by
  unfold ModEq at *
  exact dvd_trans_int d m (a - b) h2 h1

Conclusion "
Beautiful! You have unlocked the power of theorem reuse with `exact`, and proved that you can always step down from a modulus to any of its divisors (`mod_shrink`).
"
