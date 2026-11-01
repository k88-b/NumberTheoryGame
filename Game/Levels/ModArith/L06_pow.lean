import GameServer
import Mathlib.Tactic
import Game.Levels.ModArith.L05_mul

World "ModArith"
Level 6
Title "Powers of Congruences"


NewTactic induction'
NewTheorem pow_succ

Introduction "
Since we can multiply congruences, what happens if we multiply a congruence $a \\equiv b \\pmod m$ by itself $n$ times? We get powers:
$$a^n \\equiv b^n \\pmod m$$

Because the exponent $n$ is an arbitrary natural number ($n \\in \\mathbb{N}$), we must prove this using **mathematical induction**.

Type `induction' n with d ih` to split the proof into two goals:
1. **Base case ($n = 0$):** Prove $a^0 \\equiv b^0 \\pmod m$.
2. **Inductive step:** Assuming the statement holds for $d$ (hypothesis `ih`), prove it for $d + 1$.

*Tip:* In the inductive step, use `rw [pow_succ]` (twice!) to rewrite $a^{d+1}$ as $a^d \\cdot a$ and $b^{d+1}$ as $b^d \\cdot b$, then finish with `mod_mul`!
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
Fantastic! You just performed your first proof by induction, effortlessly reducing powers to multiplication with `mod_mul`.

Now, one last challenge stands between you and the end of Modular Arithmetic!
"
