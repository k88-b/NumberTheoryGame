import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L05_sol_suff

World "LinCong"
Level 6
Title "Congruent Solutions"

Introduction "
If $x_1$ and $x_2$ are both solutions to $a \\cdot x \\equiv b \\pmod m$, how are they related?

They are not necessarily congruent modulo $m$, but they **are** congruent modulo $m_1 = m / d$.
This perfectly mirrors `mod_cancel_general` from World 3. You can reuse it directly!
"

/--
**Congruent Solutions modulo $m/d$**

All solutions to $a \cdot x \equiv b \pmod m$ are congruent modulo $m/d$.
-/
TheoremDoc lin_cong_sol_equiv as "lin_cong_sol_equiv" in "LinCong"

Statement lin_cong_sol_equiv (a b m d a1 m1 x1 x2 : ℤ) (hd_not_zero : d ≠ 0) (hd : IsGCD(a, m) d) (ha : a = a1 * d) (hm : m = m1 * d) (h1 : (a * x1) ≡ b (mod m)) (h2 : (a * x2) ≡ b (mod m)) : x1 ≡ x2 (mod m1) := by
  have h_trans : (a * x1) ≡ (a * x2) (mod m) := by
    have h2_symm := mod_symm (a * x2) b m h2
    exact mod_trans (a * x1) b (a * x2) m h1 h2_symm
  have h_eq : (x1 * a) ≡ (x2 * a) (mod m) := by
    have hrw1 : x1 * a = a * x1 := by ring
    have hrw2 : x2 * a = a * x2 := by ring
    rw [hrw1, hrw2]
    exact h_trans
  exact mod_cancel_general x1 x2 a m d a1 m1 hd_not_zero h_eq hd ha hm

Conclusion "
Excellent! You have shown that any two solutions only differ by multiples of $m/d$.
"
