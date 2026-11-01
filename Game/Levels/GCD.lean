import Game.Levels.GCD.L01_gcd_def
import Game.Levels.GCD.L02_gcd_greatest
import Game.Levels.GCD.L03_coprime_forward
import Game.Levels.GCD.L04_coprime_backward
import Game.Levels.GCD.L05_gcd_symm
import Game.Levels.GCD.L06_cancel_coprime
import Game.Levels.GCD.L07_gcd_div_coprime
import Game.Levels.GCD.L08_cancel_general
import Game.Levels.GCD.L09_gcd_shift

World "GCD"
Title "In Search of the GCD"

Introduction
"
Welcome to In Search of the GCD!

Can we cancel a common factor $c$ from both sides of a congruence $a \\cdot c \\equiv b \\cdot c \\pmod m$? Not always! To safely cancel factors in modular arithmetic, we need to deeply understand the Greatest Common Divisor (GCD).

In this world, we will define the GCD using Bézout's identity, prove its properties, unlock the ultimate tool for number theory — the General Cancellation Law — and finish by proving the shift invariance that powers the Euclidean Algorithm. Let's find that GCD!
"
