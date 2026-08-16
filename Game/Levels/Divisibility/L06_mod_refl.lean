import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 6
Title "Modular Arithmetic: Reflexivity"

/--
**Modular Congruence ($a \equiv b \pmod m$)**

We say that $a$ is **congruent** to $b$ modulo $m$ if their difference $(a - b)$ is a multiple of $m$.
Formally, it means $m$ divides $(a - b)$:
$$m \mid (a - b)$$

**Intuition:**
This is a mathematical way of saying that $a$ and $b$ leave the *same remainder* when divided by $m$. Think of a clock: 15:00 and 3:00 point to the same place because $15 \equiv 3 \pmod{12}$.

**Examples:**
* $17 \equiv 5 \pmod{12}$ because $12 \mid (17 - 5)$, which simplifies to $12 \mid 12$.
* $23 \equiv 2 \pmod 7$ because $7 \mid (23 - 2)$, which is $7 \mid 21$.
* $10 \equiv 0 \pmod 5$ because $5 \mid (10 - 0)$, which is $5 \mid 10$.

**How it works in Lean:**
We created a custom notation $a \equiv b \pmod m$ to represent a function called `ModEq`. When you see this notation in your goal or hypotheses, you can use the `unfold ModEq` tactic. This will strip away the formatting and reveal the underlying divisibility statement: `m ∣ a - b`.
-/
DefinitionDoc ModEq as "a ≡ b (mod m)"

/--
The `unfold` tactic replaces a definition with its underlying meaning.
If your goal contains `a ≡ b (mod m)`, typing `unfold ModEq` will change it to `m ∣ a - b`.
-/
TacticDoc unfold

NewDefinition ModEq
NewTactic unfold

Introduction "
We are now introducing a massive concept in number theory: **Congruences**.
We say that $a \\equiv b \\pmod m$ if $m$ divides $(a - b)$.

In Lean, we have defined a custom property for this and created a notation `a ≡ b (mod m)`.
Check your **Definitions** tab to read a detailed explanation and see some examples!

When you see this notation in the goal, you should type `unfold ModEq` to reveal what it actually means under the hood.

Let's prove that modular arithmetic is reflexive: $a \\equiv a \\pmod m$.
"

def ModEq (m a b : ℤ) : Prop := m ∣ (a - b)

notation a " ≡ " b " (mod " m ")" => ModEq m a b

/-- Modular arithmetic is reflexive. -/
TheoremDoc mod_refl as "mod_refl" in "Congruence"

/-- Every integer is congruent to itself. -/
Statement mod_refl (a m : ℤ) : a ≡ a (mod m) := by
  unfold ModEq
  use 0
  ring

Conclusion "
Great! Because $a - a = 0$, and $m \\mid 0$, it immediately follows that $a \\equiv a \\pmod m$.
"
