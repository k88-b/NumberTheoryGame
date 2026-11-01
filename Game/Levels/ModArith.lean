import Game.Levels.ModArith.L01_add
import Game.Levels.ModArith.L02_sub
import Game.Levels.ModArith.L03_add_const
import Game.Levels.ModArith.L04_mul_const
import Game.Levels.ModArith.L05_mul
import Game.Levels.ModArith.L06_pow
import Game.Levels.ModArith.L07_poly

World "ModArith"
Title "Modular Arithmetic"

Introduction "
Welcome to Modular Arithmetic!

In the Congruence world, you proved that $\\equiv \\pmod m$ is an equivalence relation. Now we unlock its real algebraic power: you can safely add, subtract, multiply, and raise congruences to powers, just like regular equations!

By the end of this world, you will combine all of these operations to prove that **polynomials preserve congruences** ($P(a) \\equiv P(b) \\pmod m$) — the master key to proving the classic divisibility rules!
"
