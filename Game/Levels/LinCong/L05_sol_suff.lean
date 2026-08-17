import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L04_sol_nec

World "LinCong"
Level 5
Title "Solvability: Sufficient Condition"

Introduction "
Now the exciting part: if $d \\mid b$, there **must** exist a solution $x$ to $a \\cdot x \\equiv b \\pmod m$!

This is a constructive proof. Since $d \\mid b$, we know $b = d \\cdot k$.
From Bézout, $d = a \\cdot u + m \\cdot v$.
Substituting $d$, we get $b = a \\cdot (u \\cdot k) + m \\cdot (v \\cdot k)$.

Can you figure out what the solution $x$ should be?
"

/--
**Solvability (Sufficient Condition)**

If $d = \text{gcd}(a, m)$ and $d \mid b$, then $\exists x, a \cdot x \equiv b \pmod m$.
-/
TheoremDoc lin_cong_suff as "lin_cong_suff" in "LinCong"

Statement lin_cong_suff (a b m d : ℤ) (hd : IsGCD(a, m) d) (hb : d ∣ b) : ∃ x, (a * x) ≡ b (mod m) := by
  unfold IsGCD at hd
  obtain ⟨_, u, v, huv⟩ := hd
  obtain ⟨k, hk⟩ := hb
  Hint "As the introduction says, try `x = {u} * {k}`. `use {u} * {k}`, then `unfold ModEq` to see the actual goal."
  use u * k
  unfold ModEq
  Hint (hidden := true) "Your goal is `{m} ∣ ({a} * ({u} * {k}) - {b})`. Since `{b} = {d} * {k}`, try `use -{v} * {k}`, then rewrite `{b}` via `{hk}`."
  use -v * k
  rw [hk]
  Hint (hidden := true) "Build the shift identity: `have h_eq : {a} * ({u} * {k}) - {d} * {k} = {m} * (-{v} * {k}) + {k} * ({a} * {u} + {m} * {v} - {d}) := by ring`. The last term vanishes once you plug in `{huv}`."
  have h_eq : a * (u * k) - d * k = m * (-v * k) + k * (a * u + m * v - d) := by ring
  rw [h_eq]
  rw [huv]
  have h_eq2 : m * (-v * k) + k * (d - d) = m * (-v * k) := by ring
  rw [h_eq2]

Conclusion "
Beautiful! You multiplied the Bézout coefficients by $b/d$ to constructively find the solution $x$.
"
