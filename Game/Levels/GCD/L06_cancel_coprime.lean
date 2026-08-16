import GameServer
import Mathlib.Tactic
import Game.Levels.GCD.L05_coprime_backward
import Game.Levels.Divisibility.L06_mod_refl

World "GCD"
Level 6
Title "The Cancellation Law (Coprime Case)"

Introduction "
Here is the central theorem of this world — and one of the most useful facts in all of number theory.

If $a \\cdot c \\equiv b \\cdot c \\pmod m$, and $c$ is coprime to $m$ (`IsGCD(c, m) 1`), can we conclude $a \\equiv b \\pmod m$? In other words: can we *cancel* the common factor $c$ from both sides of a congruence?

**Yes** — but only because $c$ and $m$ are coprime! Without that assumption this would be false: take $c = 2$, $m = 4$. Then $2 \\cdot 1 \\equiv 2 \\cdot 3 \\pmod 4$ (since $6 - 2 = 4$), yet $1 \\equiv 3 \\pmod 4$ is false ($3 - 1 = 2$ is not a multiple of $4$). Coprimality is essential.

**The key idea:** since $c$ and $m$ are coprime, we have $c \\cdot x + m \\cdot y = 1$ for some $x, y$ (that's exactly what you proved in Level 4!). Multiplying our congruence's underlying equation by $x$ makes the extra factor $c$ effectively disappear, leaving exactly what we want.

This proof is long, but every single step is either a `have` (a pure algebra identity, closed by `ring`) or an `rw` that plugs in a hypothesis. Take it one line at a time.
"

/--
**Cancellation Law for Coprime Factors**

If $a \cdot c \equiv b \cdot c \pmod m$ and `IsGCD(c, m) 1`, then $a \equiv b \pmod m$.

**Intuition:**
Multiplying both sides of a congruence by the same number is always safe (World 2!). This theorem shows the *reverse* direction — cancelling out a common factor — is *also* safe, but only when that factor shares no common divisor with the modulus. Coprimality is precisely the condition under which "dividing" makes sense in modular arithmetic.
-/
TheoremDoc mod_cancel_coprime as "mod_cancel_coprime" in "Congruence"

/-- Cancelling a factor coprime to the modulus. -/
Statement mod_cancel_coprime (a b c m : ℤ) (h1 : (a * c) ≡ (b * c) (mod m)) (h2 : IsGCD(c, m) 1) : a ≡ b (mod m) := by
  unfold ModEq at *
  unfold IsGCD at h2
  obtain ⟨k, hk⟩ := h1
  obtain ⟨_, x, y, hxy⟩ := h2
  use k * x + (a - b) * y
  have h_eq1 : m * (k * x + (a - b) * y) = (m * k) * x + (a - b) * (m * y) := by ring
  rw [h_eq1]
  rw [← hk]
  have h_eq2 : (a * c - b * c) * x + (a - b) * (m * y) = (a - b) * (c * x + m * y) := by ring
  rw [h_eq2]
  rw [hxy]
  ring

Conclusion "
🎉 That's the heart of this world, conquered! `mod_cancel_coprime` is now yours — it is the single most important tool you will use going forward.
"
