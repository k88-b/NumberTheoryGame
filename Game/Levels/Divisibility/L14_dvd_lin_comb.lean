import GameServer
import Mathlib.Tactic
import Game.Levels.Divisibility.L13_dvd_trans

World "Divisibility"
Level 14
Title "Linear Combinations (Boss)"

Introduction "
Welcome to the final boss of World 1!

An expression of the form $a \\cdot x + b \\cdot y$ is called a **linear combination** of $a$ and $b$.
Here you will prove one of the most important facts in all of number theory: if $d$ divides both $a$ and $b$, then $d$ divides **any** linear combination $a \\cdot x + b \\cdot y$!

This combines the scaling principle from Level 11 ($d \\mid a \\implies d \\mid a \\cdot x$) with the addition principle from Level 12 ($d \\mid u$ and $d \\mid v \\implies d \\mid u + v$) into a single proof.

Unpack both `ha` and `hb` with `obtain`, substitute them into the goal, and construct the combined witness!
"

/-- If d divides a and b, then d divides any linear combination a * x + b * y. -/
Statement dvd_lin_comb_int (d a b x y : ℤ) (ha : d ∣ a) (hb : d ∣ b) : d ∣ a * x + b * y := by
  obtain ⟨k1, hk1⟩ := ha
  obtain ⟨k2, hk2⟩ := hb
  Hint (hidden := true) "Once you substitute `a = d * k1` and `b = d * k2`, the sum `a * x + b * y` becomes `(d * k1) * x + (d * k2) * y`. Factor out `d` to see what witness to `use`!"
  rw [hk1, hk2]
  use k1 * x + k2 * y
  ring

Conclusion "
🎉 INCREDIBLE! 🎉

You have conquered the first world! By combining scaling and addition of witnesses into $k_1 \\cdot x + k_2 \\cdot y$, you proved that common divisors always divide linear combinations (`dvd_lin_comb_int`) — a theorem that will later power Bézout's Identity and the Greatest Common Divisor.

You've mastered the foundational tactics `use`, `obtain`, `rw`, and `ring`.
Get ready for World 2, where we will introduce a massive new concept built directly on divisibility: **Modular Arithmetic (Congruences)**!
"
