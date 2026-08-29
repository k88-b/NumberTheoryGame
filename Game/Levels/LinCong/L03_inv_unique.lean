import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L02_inv_reverse

World "LinCong"
Level 3
Title "The Inverse is Unique"

Introduction "
If $x$ and $y$ are both inverses of $a$ modulo $m$, are they the same?

We know $a \\cdot x \\equiv 1 \\pmod m$ and $a \\cdot y \\equiv 1 \\pmod m$. This implies $a \\cdot x \\equiv a \\cdot y \\pmod m$. Since $a$ has an inverse, $a$ and $m$ are coprime. You can now use your ultimate weapon from World 3: `mod_cancel_coprime`!

**Strategy:**
1. **Prove coprimality:** The theorem `inv_implies_coprime` (from the previous level) requires a proof that *some* inverse exists (`∃ k, a * k ≡ 1`). You can provide $x$ as the witness to build this existence proof, and then extract the coprimality fact.
2. **Equate the terms:** Use symmetry and transitivity to link your two main hypotheses into $a \\cdot x \\equiv a \\cdot y \\pmod m$.
3. **Cancel the factor:** Prepare your congruence for `mod_cancel_coprime`. The theorem expects the common factor to be on the *right* side ($x \\cdot a \\equiv y \\cdot a$), so you will need to swap the multiplication order before applying the cancellation law.
"


Statement inv_unique_mod (a x y m : ℤ) (hx : (a * x) ≡ 1 (mod m)) (hy : (a * y) ≡ 1 (mod m)) : x ≡ y (mod m) := by
  Hint "Following step 1 of the strategy, create a proof that *some* inverse exists using {x} as the witness: `have h_exists : ∃ k, ({a} * k) ≡ 1 (mod {m})`."

  have h_exists : ∃ k, (a * k) ≡ 1 (mod m)
  · use x

  have h_coprime : IsGCD a m 1
  · exact inv_implies_coprime a m h_exists

  have h_trans : (a * x) ≡ (a * y) (mod m)
  · have hy_symm : 1 ≡ (a * y) (mod m)
    · exact mod_symm (a * y) 1 m hy

    exact mod_trans (a * x) 1 (a * y) m hx hy_symm

  have h_eq : (x * a) ≡ (y * a) (mod m)
  · have hrw1 : x * a = a * x
    · ring

    have hrw2 : y * a = a * y
    · ring

    rw [hrw1, hrw2]
    exact h_trans

  exact mod_cancel_coprime x y a m h_eq h_coprime

Conclusion "
Exactly! Using the cancellation law on congruences works wonderfully here.
"
