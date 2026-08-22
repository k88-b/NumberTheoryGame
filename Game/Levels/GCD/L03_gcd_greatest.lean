import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L02_gcd_def

World "GCD"
Level 3
Title "The GCD Really Is the Greatest"

Introduction "
Now for the payoff of our definition: let's show that any $d$ satisfying `IsGCD(a, b) d` is truly a *greatest* common divisor — meaning every other common divisor of $a$ and $b$ also divides $d$.

Formulation: if `IsGCD(a, b) d` holds, and $c$ is *any* common divisor of $a$ and $b$ ($c \\mid a$ and $c \\mid b$), then $c \\mid d$.

Strategy:
1. `unfold IsGCD at h` to extract the two divisibility facts and the Bézout witnesses $x, y$ with $a \\cdot x + b \\cdot y = d$. Since this is a nested conjunction-with-an-existential, `obtain` can peel apart all the layers at once with a pattern like `⟨⟨hda, hdb⟩, x, y, hxy⟩`.
2. Apply `dvd_mul_of_dvd_left` (from the previous level!) to $c \\mid a$ to get $c \\mid (a \\cdot x)$, and similarly to get $c \\mid (b \\cdot y)$. Use `have` to store each as an intermediate fact.
3. `obtain` witnesses from both new facts, `use` their sum, then `rw` and `ring` to finish — exactly the witness-gluing pattern you used for `dvd_trans` in World 1.
"


/-- Any greatest-common-divisor witness dominates every common divisor. -/
Statement gcd_is_greatest (a b c d : ℤ) (h : IsGCD(a, b) d) (hca : c ∣ a) (hcb : c ∣ b) : c ∣ d := by
  unfold IsGCD at h
  Hint "Your hypothesis `{h}` is now a nested conjunction with an existential. Extract everything at once using `obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := {h}`."
  obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := h
  Hint (hidden := true) "Use the theorem from Level 1!"
  have h1 : c ∣ (a * x) := dvd_mul_of_dvd_left hca x
  have h2 : c ∣ (b * y) := dvd_mul_of_dvd_left hcb y
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use k1 + k2
  rw [← hxy]
  rw [hk1]
  rw [hk2]
  ring

Conclusion "
Excellent! You combined a deeply nested `obtain`, two applications of a previous lemma via `have`, and the familiar witness-gluing pattern. This is the deepest proof so far — and you built it entirely from pieces you already had.
"
