import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L06_sol_equiv

World "LinCong"
Level 7
Title "Shifting the Solution"

Introduction "
Conversely, if we shift a valid solution $x_0$ by any multiple of $m_1 = m / d$, we get another valid solution.
$a(x_0 + t \\cdot m_1) \\equiv b \\pmod m$.

Use $a = a_1 \\cdot d$ (from `IsGCD`) and the property of shifting modulo $m$ (`mod_add_multiple`) to finish the job!
"


Statement lin_cong_sol_shift (a b m d m1 x0 t : ℤ) (hd : IsGCD(a, m) d) (hm : m = m1 * d) (h0 : (a * x0) ≡ b (mod m)) : (a * (x0 + t * m1)) ≡ b (mod m) := by
  unfold IsGCD at hd
  obtain ⟨⟨hda, _⟩, _⟩ := hd
  obtain ⟨a1, ha1⟩ := hda

  Hint (hidden := true) "You want to show `{a} * ({x0} + {t} * {m1}) = {a} * {x0} + ({a1} * {t}) * {m}`, so that `mod_add_multiple` applies directly. Substitute `{a} = {a1} * {d}` and `{m} = {m1} * {d}`"

  have h_shift : (a * (x0 + t * m1)) = a * x0 + (a1 * t) * m
  · rw [ha1, hm]
    ring

  have h_cong : (a * (x0 + t * m1)) ≡ (a * x0) (mod m)
  · rw [h_shift]
    exact mod_add_multiple (a * x0) (a1 * t) m

  exact mod_trans (a * (x0 + t * m1)) (a * x0) b m h_cong h0

Conclusion "
Great work! Together, Levels 6 and 7 give us the complete description of the set of solutions: an arithmetic progression with step $m/d$.
"
