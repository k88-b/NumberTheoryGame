import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L08_euclid

World "LinCong"
Level 9
Title "Chinese Remainder Theorem: Existence"

Introduction "
If we want a number $x$ to satisfy two separate congruences simultaneously:
$x \\equiv a \\pmod m$ and $x \\equiv b \\pmod n$
When does such an $x$ exist?

The **Chinese Remainder Theorem (CRT)** guarantees a solution whenever $m$ and $n$ are coprime!
If $m \\cdot u + n \\cdot v = 1$, we can explicitly construct the solution:
$x = a \\cdot n \\cdot v + b \\cdot m \\cdot u$.

Try it! Use your algebra skills and the Bézout identity to prove this explicitly.
"

/--
**CRT Existence**

If $\text{gcd}(m, n) = 1$, then there exists an $x$ solving both congruences.

**Intuition:**
Build $x$ from two pieces using Bézout witnesses $u, v$ with $m \cdot u + n \cdot v = 1$. The term $n \cdot v$ behaves like "$1$" modulo $m$ (and vanishes modulo $n$), while $m \cdot u$ behaves like "$1$" modulo $n$ (and vanishes modulo $m$). So $x = a \cdot n \cdot v + b \cdot m \cdot u$ picks up $a$'s value mod $m$ and $b$'s value mod $n$ simultaneously.

**Example:** solving $x \equiv 2 \pmod 3$ and $x \equiv 3 \pmod 5$: here $3 \cdot 2 + 5 \cdot (-1) = 1$, so $u = 2, v = -1$. This gives $x = 2 \cdot 5 \cdot (-1) + 3 \cdot 3 \cdot 2 = -10 + 18 = 8$. Check: $8 \equiv 2 \pmod 3$ ✓ and $8 \equiv 3 \pmod 5$ ✓.
-/
TheoremDoc crt_exists as "crt_exists" in "LinCong"

Statement crt_exists (a b m n : ℤ) (h_coprime : IsGCD(m, n) 1) : ∃ x, (x ≡ a (mod m)) ∧ (x ≡ b (mod n)) := by
  unfold IsGCD at h_coprime
  obtain ⟨_, u, v, huv⟩ := h_coprime
  Hint "As explained in the introduction, the witness is `x = {a} * {n} * {v} + {b} * {m} * {u}`. `use` it, then `constructor` to split into the two congruences."
  use a * n * v + b * m * u
  constructor
  · unfold ModEq
    Hint (hidden := true) "Your goal is `{m} ∣ (({a} * {n} * {v} + {b} * {m} * {u}) - {a})`. Try `use {b} * {u} - {a} * {u}`, then `have h_eq : ({a} * {n} * {v} + {b} * {m} * {u}) - {a} = {m} * ({b} * {u} - {a} * {u}) + {a} * ({m} * {u} + {n} * {v} - 1) := by ring`, and `rw [h_eq, {huv}]` to make the last term vanish."
    use b * u - a * u
    have h_eq : (a * n * v + b * m * u) - a = m * (b * u - a * u) + a * (m * u + n * v - 1) := by ring
    rw [h_eq]
    rw [huv]
    have h_eq2 : m * (b * u - a * u) + a * (1 - 1) = m * (b * u - a * u) := by ring
    rw [h_eq2]
  · unfold ModEq
    Hint (hidden := true) "Same trick, mirrored for `{n}`: `use {a} * {v} - {b} * {v}`, then `have h_eq : ({a} * {n} * {v} + {b} * {m} * {u}) - {b} = {n} * ({a} * {v} - {b} * {v}) + {b} * ({m} * {u} + {n} * {v} - 1) := by ring`."
    use a * v - b * v
    have h_eq : (a * n * v + b * m * u) - b = n * (a * v - b * v) + b * (m * u + n * v - 1) := by ring
    rw [h_eq]
    rw [huv]
    have h_eq2 : n * (a * v - b * v) + b * (1 - 1) = n * (a * v - b * v) := by ring
    rw [h_eq2]

Conclusion "
Magnificent! This explicit witness construction sits at the core of CRT.
"
