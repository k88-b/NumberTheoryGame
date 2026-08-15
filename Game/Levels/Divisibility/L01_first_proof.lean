import GameServer
import Mathlib.Tactic

World "Divisibility"
Level 1
Title "Your First Proof"

/--
The `use` tactic is used to provide a \"witness\" to prove that something exists.
If your goal is `∃ k, 12 = 3 * k`, typing `use 4` changes the goal to `12 = 3 * 4`.
-/
TacticDoc use

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

NewTactic use
NewDefinition Dvd.dvd

Introduction "
Welcome to your first level! In Lean, you write proofs by using **tactics**. Tactics are commands that manipulate the goal until it is solved.

Our first statement is `3 ∣ 12`, which is read as \"3 divides 12\".
Check your **Definitions** tab on the right to read exactly what this means mathematically!

*(To type the divides symbol `∣`, type `\\|` or `\\mid` and press Space!)*

Lean sees `3 ∣ 12` as `∃ k, 12 = 3 * k`.
To prove this, you need to provide the number $k$. You can do this using the `use` tactic.
Type `use 4`. Lean will automatically substitute $k$ with 4 and close the goal since 12 equals 3 * 4!
"

/-- The exercise statement: 3 divides 12. -/
Statement : 3 ∣ 12 := by
  use 4

Conclusion "
Congratulations! You have just written your first proof in Lean 4!
You used `use` to provide a witness, and Lean automatically closed the obvious equality.
"
