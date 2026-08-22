import GameServer
import Mathlib.Tactic
import Game.Levels.Problems.L04_lincong

World "Problems"
Level 5
Title "Euclid in Practice"

Introduction "
If a number is a multiple of 10, and we know it's written as $x \\cdot 3$, does 10 divide $x$?
Yes! Because 3 and 10 share no common factors, the 10 must entirely divide the $x$.

This is exactly `euclids_lemma` from World 4: if $m \\mid (a \\cdot c)$ and $\\gcd(c, m) = 1$, then $m \\mid a$.

Let's prove this explicitly for $m = 10$, $a = x$, and $c = 3$.
"

Statement (x : ℤ) (h : 10 ∣ x * 3) : 10 ∣ x := by
  Hint "You need to show that 3 and 10 are coprime. `have h_gcd : IsGCD(3, 10) 1 := by ...`"
  have h_gcd : IsGCD(3, 10) 1 := by
    unfold IsGCD
    constructor
    · constructor
      · exact one_dvd 3
      · exact one_dvd 10
    · Hint (hidden := true) "Find $3 \\cdot u + 10 \\cdot v = 1$. Try `use -3, 1`."
      use -3, 1
      ring

  Hint "Use `euclids_lemma`. Look closely at its arguments: `euclids_lemma a c m h_div h_coprime`. Here, it's `euclids_lemma x 3 10 h h_gcd`."
  exact euclids_lemma x 3 10 h h_gcd

Conclusion "
Spot on! Euclid's Lemma is an incredibly powerful tool for analyzing equations with integers, and now you know how to apply it to concrete numbers.
"
