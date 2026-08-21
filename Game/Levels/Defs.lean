import GameServer
import Mathlib.Tactic


def ModEq (m a b : ℤ) : Prop := m ∣ (a - b)

notation a " ≡ " b " (mod " m ")" => ModEq m a b

/--
**Modular Congruence ($a \equiv b \pmod m$)**

We say that $a$ is **congruent** to $b$ modulo $m$ if their difference $(a - b)$ is a multiple of $m$.
Formally, it means $m$ divides $(a - b)$:
$$m \mid (a - b)$$

**Intuition:**
This is a mathematical way of saying that $a$ and $b$ leave the *same remainder* when divided by $m$. Think of a clock: 15:00 and 3:00 point to the same place because $15 \equiv 3 \pmod{12}$.

**Examples:**
* $17 \equiv 5 \pmod{12}$ because $12 \mid (17 - 5)$, which simplifies to $12 \mid 12$.
* $23 \equiv 2 \pmod 7$ because $7 \mid (23 - 2)$, which is $7 \mid 21$.
* $10 \equiv 0 \pmod 5$ because $5 \mid (10 - 0)$, which is $5 \mid 10$.

**How it works in Lean:**
We created a custom notation $a \equiv b \pmod m$ to represent a function called `ModEq`. When you see this notation in your goal or hypotheses, you can use the `unfold ModEq` tactic. This will strip away the formatting and reveal the underlying divisibility statement: `m ∣ a - b`.
-/
DefinitionDoc ModEq as "a ≡ b (mod m)"


def IsGCD (a b d : ℤ) : Prop :=
  (d ∣ a ∧ d ∣ b) ∧ ∃ x y : ℤ, a * x + b * y = d

notation "IsGCD(" a ", " b ") " d => IsGCD a b d

/--
**The Greatest Common Divisor, Bézout-style**

In this game, we say $d$ **is a greatest common divisor** of $a$ and $b$ — written `IsGCD(a, b) d` — if **two** conditions hold together:

1. $d$ is a **common divisor**: $d \mid a$ and $d \mid b$.
2. $d$ can be written as a **Bézout combination**: there exist integers $x, y$ such that $a \cdot x + b \cdot y = d$.

$$\text{IsGCD}(a, b) d \iff (d \mid a \land d \mid b) \land \exists x, y \in \mathbb{Z},\ a x + b y = d$$

**Why this definition, and not simply "the largest common divisor"?**
Working with "largest" directly is awkward in Lean: comparing sizes doesn't play well with negative numbers, and proving something is *the* biggest usually means comparing it to every other common divisor one at a time.

The Bézout condition sidesteps all of that. It turns out (and you will prove it in the very next level!) that *any* $d$ satisfying condition 2, together with condition 1, is automatically bigger than every other common divisor — for free, with a short proof. So instead of taking "greatest" as the definition, we derive it as a theorem.

**A word of caution:** this definition alone does not force $d \geq 0$ or force $d$ to be unique. In this game we will always keep a specific, non-negative witness in mind (for example `IsGCD(2, 3) 1`, never `IsGCD(2, 3) (-1)`, even though $-1$ also happens to satisfy the Bézout condition for $2$ and $3$, up to sign).
-/
DefinitionDoc IsGCD as "IsGCD(a, b) d"


/--
**Divisibility ($a \mid b$)**

We say that an integer $a$ **divides** an integer $b$ (written as $a \mid b$) if $b$ is a multiple of $a$.
Formally, this means there exists some integer $k$ such that:
$$b = a \cdot k$$

**Examples:**
* $3 \mid 12$ is true because $12 = 3 \cdot 4$ (here our witness is $k = 4$).
* $5 \mid -15$ is true because $-15 = 5 \cdot (-3)$ (here $k = -3$).
* $7 \mid 0$ is true because $0 = 7 \cdot 0$ (here $k = 0$).
* $4 \mid 14$ is **false**, because there is no integer $k$ that makes $14 = 4 \cdot k$.

**How it works in Lean:**
When you see $a \mid b$ in your goal, Lean translates this under the hood to an \"exists\" statement: `∃ k, b = a * k`.
To prove it, you must provide the exact value of $k$ using the `use` tactic (for example, `use 4`).
-/
DefinitionDoc Dvd.dvd as "a ∣ b"
