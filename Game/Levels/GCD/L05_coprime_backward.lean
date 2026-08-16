import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L04_coprime_forward
import Game.Levels.Divisibility.L02_what_is_dvd

World "GCD"
Level 5
Title "Bézout Gives You Coprimality (⟸)"

Introduction "
Now the other direction: if there exist integers $x, y$ with $c \\cdot x + m \\cdot y = 1$, does that mean `gcd(c, m) = 1`?

Yes — and to prove it, remember `one_dvd` from World 1: *every* integer is divisible by $1$. So the \"common divisor\" half of the definition (`1 ∣ c` and `1 ∣ m`) comes completely for free! All that's left is to hand back the Bézout identity you were already given.
"

/--
**A Bézout Identity with 1 Implies Coprimality**

If there exist integers $x, y$ with $c \cdot x + m \cdot y = 1$, then `gcd(c, m) = 1`.
-/
TheoremDoc bezout_imp_coprime as "bezout_imp_coprime" in "GCD"

/-- A Bézout identity implies coprimality. -/
Statement bezout_imp_coprime (c m : ℤ) (h : ∃ x y : ℤ, c * x + m * y = 1) :  gcd(c, m)= 1 := by
  unfold IsGCD
  constructor
  · constructor
    · exact one_dvd c
    · exact one_dvd m
  · exact h

Conclusion "
Beautiful! Together, the last two levels show that `gcd(c, m) = 1` and \"a Bézout identity with 1 exists\" are two ways of saying exactly the same thing. From now on, feel free to think of *coprime* simply as \"Bézout equals 1\".
"
