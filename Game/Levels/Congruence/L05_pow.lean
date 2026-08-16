import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L04_add_mul_mod

World "Congruence"
Level 5
Title "Powers of Congruences"

/--
The `induction'` tactic is used to prove statements for all natural numbers `n`.
Typing `induction' n with d ih` splits your goal into two cases: the base case (`n = 0`) and the inductive step (`n = d + 1`), giving you the induction hypothesis `ih`.
-/
TacticDoc induction'

/--
`pow_succ` is a theorem from Mathlib that states $a^{n+1} = a^n \cdot a$.
Use `rw [pow_succ]` when dealing with powers in induction.
-/
TheoremDoc pow_succ as "pow_succ" in "Algebra"

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

/-- Congruences can be raised to a natural power. -/
TheoremDoc mod_pow as "mod_pow" in "Congruence"

/-- Powers of congruences. -/
Statement mod_pow (a b m : ℤ) (n : ℕ) (h : a ≡ b (mod m)) : (a^n) ≡ (b^n) (mod m) := by
  induction' n with d ih
  unfold ModEq
  use 0
  ring
  rw [pow_succ]
  rw [pow_succ]
  exact mod_mul (a^d) (b^d) a b m ih h

Conclusion "
Fantastic! You just performed your first proof by induction. The multi-layered nature of mathematics is starting to reveal itself: you used `mod_mul` inside an inductive step![cite: 2]
"
