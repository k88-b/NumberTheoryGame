import GameServer
import Mathlib.Tactic
import Game.Levels.LinCong.L09_crt_exists

World "LinCong"
Level 10
Title "Chinese Remainder Theorem: Glued"

Introduction "
The second half of CRT states that if two numbers have the same remainder modulo $m$ and modulo $n$, they must have the same remainder modulo $m \\cdot n$ (provided $m, n$ are coprime).

If $x \\equiv a \\pmod m$ and $x \\equiv a \\pmod n$, it means $m \\mid (x - a)$ and $n \\mid (x - a)$.
Extract the witnesses, equate them, and use **Euclid's Lemma** (`euclids_lemma`)!
"

/--
**Glued Modulus**

If $x \equiv a \pmod m$ and $x \equiv a \pmod n$ with coprime moduli, then $x \equiv a \pmod{m \cdot n}$.
-/
TheoremDoc crt_glue as "crt_glue" in "LinCong"

Statement crt_glue (x a m n : ℤ) (hm : x ≡ a (mod m)) (hn : x ≡ a (mod n)) (h_coprime : IsGCD(m, n) 1) : x ≡ a (mod m * n) := by
  unfold ModEq at hm hn ⊢
  obtain ⟨k1, hk1⟩ := hm
  obtain ⟨k2, hk2⟩ := hn
  have h_eq : m * k1 = n * k2 := by
    calc m * k1
      _ = x - a := hk1.symm
      _ = n * k2 := hk2
  have h_div : m ∣ (k2 * n) := by
    use k1
    have h_eq2 : k2 * n = m * k1 := by
      have h_comm : k2 * n = n * k2 := by ring
      rw [h_comm, ← h_eq]
    exact h_eq2
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
  have h_m_div_k2 := euclids_lemma k2 n m h_div h_coprime_symm
  obtain ⟨k3, hk3⟩ := h_m_div_k2
  use k3
  rw [hk2, hk3]
  ring

Conclusion "
Incredible logic chaining! You have successfully established the uniqueness (gluing) part of the Chinese Remainder Theorem.
"
