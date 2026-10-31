import Game.Metadata
import GameServer

import Game.Levels.Divisibility.L01_first_proof
import Game.Levels.Divisibility.L02_negative_multiples
import Game.Levels.Divisibility.L03_dvd_mul_right
import Game.Levels.Divisibility.L04_one_dvd
import Game.Levels.Divisibility.L05_dvd_refl
import Game.Levels.Divisibility.L06_dvd_zero
import Game.Levels.Divisibility.L07_rewriting
import Game.Levels.Divisibility.L08_rewriting_backwards
import Game.Levels.Divisibility.L09_eq_zero_of_zero_dvd
import Game.Levels.Divisibility.L10_multiples_of_6
import Game.Levels.Divisibility.L11_dvd_mul
import Game.Levels.Divisibility.L12_dvd_add
import Game.Levels.Divisibility.L13_dvd_trans
import Game.Levels.Divisibility.L14_dvd_lin_comb

World "Divisibility"
Title "Divisibility Club"

Introduction "
Welcome to World 1: The Divisibility Club!

In this first world, you will learn the basics of Lean 4, how to interact with the system, and how to write your very first formal proofs. Together, we will explore the fundamental concept of number theory: divisibility ($a \\mid b$).

Starting from simple numerical examples, you will master essential proof tactics (`use`, `ring`, `rw`, and `obtain`) and build up a toolkit of general algebraic rules. By the end of this world, you will prove that divisibility chains together (transitivity) and that common divisors always divide linear combinations ($d \\mid a \\cdot x + b \\cdot y$) — a cornerstone for everything to come.

Take your time, read the explanations carefully, and have fun!
"
