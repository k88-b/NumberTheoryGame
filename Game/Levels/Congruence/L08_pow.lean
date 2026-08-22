import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L07_add_mul_mod

World "Congruence"
Level 8
Title "Powers of Congruences"


NewTactic induction'
NewTheorem pow_succ

Introduction "
If $a \\equiv b \\pmod m$, is $a^n \\equiv b^n \\pmod m$?
Since $n$ is a natural number ($n \\in \\mathbb{N}$), we must prove this using **mathematical induction**.

Type `induction' n with d ih`. Lean will generate two goals for you:
1. The base case ($n = 0$): $a^0 \\equiv b^0 \\pmod m$.
2. The inductive step: Assuming the statement holds for $d$ (your hypothesis `ih`), prove it for $d + 1$.

*Hint:* In the inductive step, you will need to break $a^{d+1}$ into $a^d \\cdot a$. You can do this by typing `rw [pow_succ]`. You will need to do this twice (once for $a$ and once for $b$). After that, remember that you already know how to multiply congruences!
"


/-- Powers of congruences. -/
Statement mod_pow (a b m : ℤ) (n : ℕ) (h : a ≡ b (mod m)) : (a^n) ≡ (b^n) (mod m) := by
  induction' n with d ih
  unfold ModEq
  use 0
  ring
  rw [pow_succ, pow_succ]
  exact mod_mul (a^d) (b^d) a b m ih h

Conclusion "
Fantastic! You just performed your first proof by induction. The multi-layered nature of mathematics is starting to reveal itself: you used `mod_mul` inside an inductive step!
"
