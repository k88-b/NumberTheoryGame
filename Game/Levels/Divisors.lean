import Game.Levels.Divisors.L01_eq_zero_of_zero_dvd
import Game.Levels.Divisors.L02_multiples_of_6
import Game.Levels.Divisors.L03_dvd_mul
import Game.Levels.Divisors.L04_dvd_add
import Game.Levels.Divisors.L05_dvd_trans
import Game.Levels.Divisors.L06_dvd_lin_comb

World "Divisors"
Title "Algebra of Divisors"

Introduction "
Welcome to World 2: Algebra of Divisors!

In World 1, you learned how to prove a divisibility goal `a ∣ b` by supplying a witness with `use`.
Now we flip the perspective: what if `a ∣ b` is given to you as a **hypothesis**?

In this world, you will unlock the `obtain` tactic to extract witnesses from your hypotheses. Using it, you will build a toolkit of algebraic rules showing how divisibility behaves across products, sums, chains (transitivity), and finally **linear combinations** ($d \\mid a \\cdot x + b \\cdot y$) — the cornerstone for Bézout's identity and the GCD!
"
