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

**Strategy:**
1. **Equate the witnesses:** Extract the witnesses for $x - a$, set them equal, and deduce that $m \\mid (k_2 \\cdot n)$.
2. **Swap the GCD:** Prove the symmetric version of your coprimality hypothesis (since `euclids_lemma` expects `IsGCD(n, m) 1` instead of `m, n`).
3. **Apply Euclid's Lemma:** Use the lemma to conclude that $m$ must entirely divide $k_2$.
4. **Finish the algebra:** Substitute this new divisibility witness back into your original equation.

Take it one `have` at a time — you already have every tool you need.
"


Statement crt_glue (x a m n : ℤ) (hm : x ≡ a (mod m)) (hn : x ≡ a (mod n)) (h_coprime : IsGCD(m, n) 1) : x ≡ a (mod m * n) := by
  unfold ModEq at hm hn
  unfold ModEq
  obtain ⟨k1, hk1⟩ := hm
  obtain ⟨k2, hk2⟩ := hn

  Hint "Following the strategy, start by creating an equation that sets your two expressions for `x - a` equal to each other: `have h_eq : {m} * {k1} = {n} * {k2}`"
  have h_eq : m * k1 = n * k2 := by rw [← hk1, hk2]

  Hint "Now prove that `{m}` divides `{k2} * {n}`."
  have h_div : m ∣ (k2 * n) := by
    use k1
    have h_eq2 : k2 * n = n * k2 := by ring
    rw [h_eq2, ← h_eq]

  Hint "Before applying Euclid's Lemma, you need coprimality in the correct order. Prove `have h_coprime_symm : IsGCD({n}, {m}) 1`."
  have h_coprime_symm : IsGCD(n, m) 1 := by
    unfold IsGCD at h_coprime
    unfold IsGCD
    obtain ⟨_, u, v, huv⟩ := h_coprime
    constructor
    · constructor
      · exact one_dvd n
      · exact one_dvd m
    · use v, u
      have h_eq3 : n * v + m * u = m * u + n * v := by ring
      rw [h_eq3, huv]

  Hint (hidden := true) "Now apply `euclids_lemma` to extract a new witness showing that `{m} ∣ {k2}`."
  obtain ⟨k3, hk3⟩ := euclids_lemma k2 n m h_div h_coprime_symm
  use k3
  rw [hk2, hk3]
  ring

Conclusion "
🎉 YOU DEFEATED THE FINAL BOSS! 🎉

Together, `crt_exists` and `crt_glue` give you the full Chinese Remainder Theorem: a system of coprime congruences always has a solution, and that solution is unique modulo the product.

Starting from a single Bézout-style definition of the GCD, you built cancellation laws, modular inverses, Euclid's Lemma, and now the CRT itself — one of the oldest and most celebrated theorems in number theory, formally verified, entirely by you.

One more level awaits — not to test you further, but to let you enjoy the view.
"
