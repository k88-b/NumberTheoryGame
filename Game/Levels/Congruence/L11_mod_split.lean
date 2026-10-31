import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L10_mod_dvd

World "Congruence"
Level 11
Title "Splitting the Modulus (Boss)"


NewTactic constructor

Introduction "
Welcome to the final boss of World 2!

If $a \\equiv b \\pmod{m \\cdot n}$, then it must be true that $a \\equiv b \\pmod m$ AND $a \\equiv b \\pmod n$.

Your goal contains a logical AND (`∧`). To prove it, use the `constructor` tactic.
This will split your goal into two separate cases:
- In the first case, you need to show $m \\mid (a - b)$ knowing $(m \\cdot n) \\mid (a - b)$.
- In the second case, you need to show $n \\mid (a - b)$ from the same fact.

For each case, unfold `ModEq`, extract the witness $k$ with `obtain`, supply the scaled witness with `use`, and finish with `rw` and `ring` — just like you did in World 1!
"


/-- Splitting the modulus into a product. -/
Statement mod_split (a b m n : ℤ) (h : a ≡ b (mod (m * n))) : (a ≡ b (mod m)) ∧ (a ≡ b (mod n)) := by
  constructor
  · unfold ModEq at *
    obtain ⟨k, hk⟩ := h
    use n * k
    rw [hk]
    ring
  · unfold ModEq at *
    obtain ⟨k, hk⟩ := h
    use m * k
    rw [hk]
    ring

Conclusion "
🎉 AMAZING! 🎉

You have conquered World 2! You've successfully built an entire algebraic toolkit for congruences.
You learned how to use `have` to build intermediate steps, `exact` to reuse theorems, `induction'` for powers, and `constructor` to break down logical conjunctions!

Next up is World 3, where we will dive into the Greatest Common Divisor (GCD) and learn how to *cancel* numbers out of congruences.
"
