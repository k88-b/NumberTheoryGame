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


Statement crt_exists (a b m n : ℤ) (h_coprime : IsGCD(m, n) 1) : ∃ x, (x ≡ a (mod m)) ∧ (x ≡ b (mod n)) := by
  unfold IsGCD at h_coprime
  obtain ⟨_, u, v, huv⟩ := h_coprime

  Hint "As explained in the introduction, the witness is `x = {a} * {n} * {v} + {b} * {m} * {u}`. `use` it"
  use a * n * v + b * m * u

  constructor
  · unfold ModEq

    Hint (hidden := true) "To prove this divisibility, you need to factor out `{m}`. Notice that `({a} * {n} * {v} + {b} * {m} * {u}) - {a}` can be algebraically rearranged into `{m} * ({b} * {u} - {a} * {u}) + {a} * ({m} * {u} + {n} * {v} - 1)`. If you introduce this equality, you can use `{huv}` to replace `{m} * {u} + {n} * {v}` with `1`, effectively cancelling out the second part."
    use b * u - a * u

    have h_eq : (a * n * v + b * m * u) - a = m * (b * u - a * u) + a * (m * u + n * v - 1)
    · ring

    rw [h_eq, huv]
    ring

  · unfold ModEq

    Hint (hidden := true) "Same trick, mirrored for `{n}`."
    use a * v - b * v

    have h_eq : (a * n * v + b * m * u) - b = n * (a * v - b * v) + b * (m * u + n * v - 1)
    · ring

    rw [h_eq, huv]

    ring


Conclusion "
Magnificent! This explicit witness construction sits at the core of CRT.
"
