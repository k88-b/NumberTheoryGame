import GameServer
import Mathlib.Tactic
import Game.Levels.Congruence.L14_mod_dvd

World "Congruence"
Level 15
Title "Splitting the Modulus"

NewTactic constructor

Introduction "
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
Great job! You now know how to split logical conjunctions with `constructor` and break apart a product modulus.

Now, one last challenge stands between you and the end of World 2!
"
