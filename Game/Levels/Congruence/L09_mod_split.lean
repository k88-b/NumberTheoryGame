import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L08_mod_dvd

World "Congruence"
Level 9
Title "Splitting the Modulus (Boss)"

NewTactic constructor

Introduction "
Welcome to the final boss of World 3!

If $a \\equiv b \\pmod{m \\cdot n}$, then the congruence holds modulo each factor individually:
$$a \\equiv b \\pmod m \\quad \\text{AND} \\quad a \\equiv b \\pmod n$$

Notice that your goal is a logical conjunction (`∧`). In Lean, whenever you need to prove `P ∧ Q`, use the **`constructor`** tactic to split the goal into two separate subgoals: first prove `P`, then prove `Q`.

How you prove each half — whether by unfolding definitions directly or by reusing theorems you've already built — is entirely up to you!
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

You have conquered World 3! You now know how to work with congruences, reuse theorems with `exact`, split conjunctions with `constructor`, and break apart a product modulus.

The map now splits into **two parallel paths** — you can tackle them in whichever order you prefer:
- **In Search of the GCD** → **Linear Congruences and CRT**: discover Bézout's identity, cancellation laws, Euclid's Lemma, and the Chinese Remainder Theorem.
- **Modular Arithmetic** → **Divisibility Rules**: add, multiply, and raise congruences to powers, prove polynomial congruences, and unlock all classic divisibility rules!
"
