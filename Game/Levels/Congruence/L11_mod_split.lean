import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L10_mod_dvd

World "Congruence"
Level 11
Title "Splitting the Modulus (Boss)"

/--
The `constructor` tactic is used to prove goals consisting of a logical AND ($\wedge$).
It splits the goal `P ∧ Q` into two separate goals: `P` and `Q`.
-/
TacticDoc constructor

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

/--
**Splitting the Modulus**

If $a \equiv b \pmod{m \cdot n}$, then $a \equiv b \pmod m$ and $a \equiv b \pmod n$.

**Intuition:**
If a difference $(a - b)$ is a multiple of $15$ ($3 \cdot 5$), it must logically be a multiple of $3$ and a multiple of $5$.
So if two numbers are congruent modulo 15, they are automatically congruent modulo 3 and modulo 5.
This is a crucial stepping stone towards the Chinese Remainder Theorem!
-/
TheoremDoc mod_split as "mod_split" in "Congruence"

/-- Splitting the modulus into a product. -/
Statement mod_split (a b m n : ℤ) (h : a ≡ b (mod (m * n))) : (a ≡ b (mod m)) ∧ (a ≡ b (mod n)) := by
  constructor
  · unfold ModEq at *
    obtain ⟨k, hk⟩ := h
    use n * k
    have h_eq : m * n * k = m * (n * k) := by ring
    rw [← h_eq]
    exact hk
  · unfold ModEq at *
    obtain ⟨k, hk⟩ := h
    use m * k
    have h_eq : m * n * k = n * (m * k) := by ring
    rw [← h_eq]
    exact hk

Conclusion "
🎉 AMAZING! 🎉

You have conquered World 2! You've successfully built an entire algebraic toolkit for congruences.
You learned how to use `induction`, how to break down logical conjunctions with `constructor`, and how to confidently rewrite backwards using `←` (`\\l`)!

Next up is World 3, where we will dive into the Greatest Common Divisor (GCD) and learn how to *cancel* numbers out of congruences.
"
