import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L10_mod_dvd

World "Congruence"
Level 11
Title "Splitting the Modulus (Boss)"


NewTactic constructor

Introduction "
Welcome to the Boss Level of World 2!

If $a \\equiv b \\pmod{m \\cdot n}$, then it must be true that $a \\equiv b \\pmod m$ AND $a \\equiv b \\pmod n$.

Your goal contains a logical AND (`∧`). To prove it, use the `constructor` tactic.
This will split your goal into two separate cases.

**Reminder: Rewriting backwards!**
To close the goals here, you will use `have` to state that $m \\cdot n \\cdot k = m \\cdot (n \\cdot k)$.
Because you want to replace $m \\cdot (n \\cdot k)$ in your goal with the left side, remember to rewrite backwards using the left arrow: `rw [← h_eq]`.
(Type `\\l` and Space for the `←` arrow).

For each case, unfold the definition, construct the witness, use `have` for algebra, and rewrite backwards to close the goal!
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
You learned how to use `induction'`, how to break down logical conjunctions with `constructor`, and how to confidently rewrite backwards using `←` (`\\l`)!

Next up is World 3, where we will dive into the Greatest Common Divisor (GCD) and learn how to *cancel* numbers out of congruences.
"
