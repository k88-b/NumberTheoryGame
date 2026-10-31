import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L01_gcd_def

World "GCD"
Level 2
Title "The GCD Really Is the Greatest"

Introduction "
Now for the payoff of our definition: let's show that any $d$ satisfying `IsGCD(a, b) d` is truly a *greatest* common divisor — meaning every other common divisor of $a$ and $b$ also divides $d$.

Formulation: if `IsGCD(a, b) d` holds, and $c$ is *any* common divisor of $a$ and $b$ ($c \\mid a$ and $c \\mid b$), then $c \\mid d$.

Why is this so easy with our Bézout-style definition? Because $d = a \\cdot x + b \\cdot y$ is a **linear combination** of $a$ and $b$ — and in the final boss of World 1 (`dvd_lin_comb_int`), you already proved that any common divisor of $a$ and $b$ divides *every* linear combination $a \\cdot x + b \\cdot y$!

**Strategy:**
1. `unfold IsGCD at h` to reveal the two divisibility facts and the Bézout witnesses $x, y$ with $a \\cdot x + b \\cdot y = d$. Since this is a nested conjunction-with-an-existential, `obtain` can peel apart all the layers at once with a pattern like `⟨⟨hda, hdb⟩, x, y, hxy⟩`.
2. Rewrite the goal $c \\mid d$ backwards using `rw [← hxy]` to turn it into $c \\mid a \\cdot x + b \\cdot y$.
3. Close the goal in one line using `dvd_lin_comb_int` from World 1!
"


/-- Any gcd witness dominates every common divisor. -/
Statement gcd_is_greatest (a b c d : ℤ) (h : IsGCD(a, b) d) (hca : c ∣ a) (hcb : c ∣ b) : c ∣ d := by
  unfold IsGCD at h
  obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := h
  rw [← hxy]
  exact dvd_lin_comb_int c a b x y hca hcb

Conclusion "
Excellent! Because you already conquered linear combinations in World 1 (`dvd_lin_comb_int`), proving that our Bézout-style GCD dominates every other common divisor took just four lines!
"
