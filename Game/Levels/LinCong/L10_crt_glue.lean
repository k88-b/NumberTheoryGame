import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L09_crt_exists

World "LinCong"
Level 10
Title "Chinese Remainder Theorem: Glued (Boss)"

Introduction "
This is it — the final boss of the Number Theory Game!

Everything you've built across four worlds — Bézout's identity, the cancellation laws, Euclid's Lemma, and CRT existence from the last level — comes together right here.

The second half of CRT: if two numbers share the same remainder modulo $m$ and modulo $n$ separately, they share the same remainder modulo $m \\cdot n$ — provided $m$ and $n$ are coprime.

Formally: $x \\equiv a \\pmod m$ and $x \\equiv a \\pmod n$ means $m \\mid (x - a)$ and $n \\mid (x - a)$. Extract the witnesses, equate them, and reach for **Euclid's Lemma**.

**One trap to watch for:** `euclids_lemma` expects coprimality as `IsGCD(n, m) 1`, but your hypothesis is `IsGCD(m, n) 1` — arguments swapped! You'll need to prove the symmetric version yourself first (a short unfold-and-swap, just like `bezout_imp_coprime` back in World 3).

Take it one `have` at a time — you already have every tool you need.
"

/--
**Glued Modulus**

If $x \equiv a \pmod m$ and $x \equiv a \pmod n$ with coprime moduli, then $x \equiv a \pmod{m \cdot n}$.

**Intuition:**
$x - a$ is a multiple of both $m$ and $n$ separately. If $m$ and $n$ share no common factor, the only way a number can be built from both is by being a multiple of their product $m \cdot n$ — nothing is double-counted. This is exactly why coprimality matters: if $m = n = 2$, a number could be a multiple of both without being a multiple of $m \cdot n = 4$ (e.g. $x - a = 2$).

**Example:** $12$ is a multiple of both $3$ and $4$ (coprime!), and indeed $12$ is a multiple of $3 \cdot 4 = 12$.
-/
TheoremDoc crt_glue as "crt_glue" in "LinCong"

Statement crt_glue (x a m n : ℤ) (hm : x ≡ a (mod m)) (hn : x ≡ a (mod n)) (h_coprime : IsGCD(m, n) 1) : x ≡ a (mod m * n) := by
  unfold ModEq at hm hn ⊢
  obtain ⟨k1, hk1⟩ := hm
  obtain ⟨k2, hk2⟩ := hn
  Hint "From `{hk1}` and `{hk2}` you have two expressions for `{x} - {a}`. Set them equal with `have h_eq : {m} * {k1} = {n} * {k2}`."
  have h_eq : m * k1 = n * k2 := by
    calc m * k1
      _ = x - a := hk1.symm
      _ = n * k2 := hk2
  Hint (hidden := true) "From `{h_eq}`, `{m}` divides `{k2} * {n}` (same product, reordered). Build `have h_div : {m} ∣ ({k2} * {n})` by `use {k1}` and rewriting with `{h_eq}`."
  have h_div : m ∣ (k2 * n) := by
    use k1
    have h_eq2 : k2 * n = m * k1 := by
      have h_comm : k2 * n = n * k2 := by ring
      rw [h_comm, ← h_eq]
    exact h_eq2
  Hint "`euclids_lemma` needs coprimality as `IsGCD({n}, {m}) 1`, but `{h_coprime}` is `IsGCD({m}, {n}) 1` — swapped! Prove `have h_coprime_symm : IsGCD({n}, {m}) 1 := by ...` first, unfolding and swapping the Bézout witnesses."
  have h_coprime_symm : IsGCD(n, m) 1 := by
    unfold IsGCD at h_coprime ⊢
    obtain ⟨_, u, v, huv⟩ := h_coprime
    constructor
    · constructor
      · exact one_dvd n
      · exact one_dvd m
    · use v, u
      have h_eq3 : n * v + m * u = m * u + n * v := by ring
      rw [h_eq3, huv]
  Hint (hidden := true) "Now apply `euclids_lemma {k2} {n} {m} {h_div} h_coprime_symm` to get `{m} ∣ {k2}`, then finish by rewriting `{hk2}` with that witness."
  have h_m_div_k2 := euclids_lemma k2 n m h_div h_coprime_symm
  obtain ⟨k3, hk3⟩ := h_m_div_k2
  use k3
  rw [hk2, hk3]
  ring

Conclusion "
🎉 YOU BEAT THE GAME! 🎉

Together, `crt_exists` and `crt_glue` give you the full Chinese Remainder Theorem: a system of coprime congruences always has a solution, and that solution is unique modulo the product.

Starting from a single Bézout-style definition of the GCD, you built cancellation laws, modular inverses, Euclid's Lemma, and now the CRT itself — one of the oldest and most celebrated theorems in number theory, formally verified, entirely by you.

One more level awaits — not to test you further, but to let you enjoy the view.
"
