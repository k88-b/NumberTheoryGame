import GameServer
import Mathlib.Tactic

World "GCD"
Level 1
Title "A Divisor of a Factor Divides the Product"



def IsGCD (a b d : ℤ) : Prop :=
  (d ∣ a ∧ d ∣ b) ∧ ∃ x y : ℤ, a * x + b * y = d

-- syntax "IsGCD(" term "," term ")" term : term

-- macro_rules
--   | `(IsGCD($a, $b) $d) => `(IsGCD $a $b $d)

-- @[app_unexpander IsGCD]
-- def unexpandIsGCD : Lean.PrettyPrinter.Unexpander
--   | `($(_) $a $b $d) => `(IsGCD($a, $b) $d)
--   | _ => throw ()


notation "IsGCD(" a ", " b ") " d => IsGCD a b d

Introduction "
Welcome to World 3: In Search of the GCD!

Before we dive into the Greatest Common Divisor itself, we need one small but very useful building block.

If $d$ divides $a$, does $d$ also divide $a \\cdot b$ for *any* integer $b$?
Yes! If $a$ is a multiple of $d$, then any multiple of $a$ is automatically a multiple of $d$ too.

You already have every tool you need for this one: `obtain` the witness from your hypothesis, `use` the right witness for the new goal, `rw`, and finish with `ring` — exactly like you did for `dvd_trans` back in World 1.
"

/--
**A Divisor of a Factor Divides the Product**

If $d \mid a$, then $d \mid (a \cdot b)$ for any integer $b$.

**Intuition:**
If $a$ is built out of $k$ copies of $d$ (i.e. $a = d \cdot k$), then $a \cdot b$ is built out of $k \cdot b$ copies of $d$.
For example, $3 \mid 6$, so $3 \mid (6 \cdot 5) = 30$ as well.

This little lemma is a "brick" you will reuse constantly in this world: whenever you have a Bézout-style identity $a \cdot x + b \cdot y = d$ and you know some $c$ divides $a$ or $b$, this lemma lets you conclude $c$ divides the whole term $a \cdot x$ or $b \cdot y$.
-/
TheoremDoc dvd_mul_of_dvd_left as "dvd_mul_of_dvd_left" in "GCD"

/-- If d divides a, then d divides a * b for any integer b. -/
Statement dvd_mul_of_dvd_left (a b d : ℤ) (h : d ∣ a) : d ∣ (a * b) := by
  obtain ⟨k, hk⟩ := h
  use k * b
  rw [hk]
  ring

Conclusion "
Perfect! Keep `dvd_mul_of_dvd_left` close at hand — you'll use it again and again in this world.
"
