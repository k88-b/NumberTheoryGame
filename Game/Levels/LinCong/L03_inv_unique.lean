import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L02_inv_reverse

World "LinCong"
Level 3
Title "The Inverse is Unique"

Introduction "
If $x$ and $y$ are both inverses of $a$ modulo $m$, are they the same?

We know $a \\cdot x \\equiv 1 \\pmod m$ and $a \\cdot y \\equiv 1 \\pmod m$. This implies $a \\cdot x \\equiv a \\cdot y \\pmod m$. Since $a$ has an inverse, $a$ and $m$ are coprime. You can now use your ultimate weapon from World 3: `mod_cancel_coprime`!
"

/--
**Uniqueness of Inverse**

If $a \cdot x \equiv 1 \pmod m$ and $a \cdot y \equiv 1 \pmod m$, then $x \equiv y \pmod m$.
-/
TheoremDoc inv_unique as "inv_unique" in "LinCong"

Statement inv_unique (a x y m : ℤ) (hx : (a * x) ≡ 1 (mod m)) (hy : (a * y) ≡ 1 (mod m)) : x ≡ y (mod m) := by
  have h_coprime : IsGCD(a, m) 1 := by
    apply inv_implies_coprime a m
    use x
  have h_trans : (a * x) ≡ (a * y) (mod m) := by
    have hy_symm := mod_symm (a * y) 1 m hy
    exact mod_trans (a * x) 1 (a * y) m hx hy_symm
  have h_eq : (x * a) ≡ (y * a) (mod m) := by
    have hrw1 : x * a = a * x := by ring
    have hrw2 : y * a = a * y := by ring
    rw [hrw1, hrw2]
    exact h_trans
  exact mod_cancel_coprime x y a m h_eq h_coprime

Conclusion "
Exactly! Using the cancellation law on congruences works wonderfully here.
"
