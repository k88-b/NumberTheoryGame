import GameServer

/--
The `use` tactic is used to provide a \"witness\" to prove that something exists.
If your goal is `∃ k, 12 = 3 * k`, typing `use 4` changes the goal to `12 = 3 * 4`.

**Multiple arguments:**
If your goal has multiple existentials, for example `∃ x y : ℤ, 2 * x + 3 * y = 1`, you can provide multiple witnesses separated by commas: `use -1, 1`.
-/
TacticDoc use


/--
The `intro` tactic is used to introduce variables from a \"For all\" ($\\forall$) statement
or to assume the premise of an implication ($\\implies$).
For example, if the goal is `∀ a, P a`, typing `intro a` moves `a` into your context.
-/
TacticDoc intro


/--
The `ring` tactic automatically proves algebraic equalities by expanding and rearranging expressions.
It is a powerful tool so you don't have to manually apply basic axioms like commutativity or distributivity (e.g., `x + y = y + x` or `x * 1 = x`).

**What it works with:**
`ring` works on equations involving addition (`+`), subtraction (`-`), multiplication (`*`), and natural number exponents (`^`) within commutative rings (such as integers `ℤ`, rationals `ℚ`, or reals `ℝ`).

**What it does NOT work with:**
It cannot handle division (`/`), modulo arithmetic (`%`) or non-commutative structures (like matrices).
-/
TacticDoc ring


/--
The `obtain` tactic extracts a witness from a hypothesis that contains an \"exists\" ($\exists$) or a logical AND ($\wedge$).
If you have a hypothesis `h : x ∣ y` (which means `∃ k, y = x * k`), you can type
`obtain ⟨k, hk⟩ := h` to get the variable `k` and the equation `hk : y = x * k`.
*(To type `⟨` and `⟩`, write `\<` and `\>`, then press Space.)*

**Nested and multiple arguments:**
For more complex hypotheses, such as `IsGCD(c, m) 1` (which contains multiple nested `∧` and `∃`), you can extract everything at once by providing up to 4 arguments.
For example: `obtain ⟨_, x, y, hxy⟩ := h`.
The underscore `_` is used to discard parts of the hypothesis you don't need (like the divisibility facts), while binding the Bézout witnesses to `x` and `y` and the equation to `hxy`.

**Dot notation alternative:**
If a hypothesis is just a nested logical AND (`∧`), you can extract its pieces directly using **dot notation** without destroying the original hypothesis via `obtain`. For example, `h.1.1` gets the first fact, and `h.1.2` gets the second.
-/
TacticDoc obtain


/--
The `rw` (rewrite) tactic replaces a term with an equivalent term based on an equality you have.
If you have `h : A = B`, typing `rw [h]` will replace `A` with `B` in your goal.

**Multiple arguments:**
You can chain rewrites by putting multiple hypotheses in the brackets, separated by commas: `rw [h1, h2]`. Lean will apply them sequentially.

**Rewriting backwards:**
By default, `rw` replaces the left side of an equality with the right side. To rewrite from right to left, use the `←` symbol (type `\l` and Space): `rw [← h]`.

**Targeting hypotheses:**
By default, `rw` changes the goal. You can rewrite inside a hypothesis `h1` by using `at`: `rw [h_eq] at h1`.
You can also rewrite everywhere (in all hypotheses and the goal at once) using `at *`: `rw [h_eq] at *`.
-/
TacticDoc rw


/--
The `unfold` tactic replaces a definition with its underlying meaning.
If your goal contains `a ≡ b (mod m)`, typing `unfold ModEq` will change it to `m ∣ a - b`.

**Targeting hypotheses:**
By default, `unfold` applies only to the goal. You can unfold a definition inside a specific hypothesis `h` by typing `unfold ModEq at h`.
To unfold it everywhere (in all hypotheses and the goal at once), use `unfold ModEq at *`.
-/
TacticDoc unfold


/--
The `have` tactic allows you to prove intermediate steps. Once proven, a new hypothesis `h` is added to your context for the rest of the proof.

You are not limited to basic equalities (`X = Y`). You can use `have` for any proposition, such as modular equivalences (`a ≡ b (mod m)`), divisibility (`x ∣ y`), or predicates like `IsGCD(a, b) 1`.


**Important:** In this game, the assignment syntax (`:=`) is disabled. You must state the assumption and provide the proof on the following line.

**Using a proof block:**
You can state the assumption and provide the proof on the following lines. This sets your intermediate assumption as the current goal:
`have h : a ≡ b (mod m)`
`<proof steps>`
-/
TacticDoc «have»


/--
The `exact` tactic closes a goal if you provide a theorem that perfectly matches the goal.
-/
TacticDoc exact


/--
The `induction'` tactic is used to prove statements for all natural numbers `n`.
Typing `induction' n with d ih` splits your goal into two cases: the base case (`n = 0`) and the inductive step (`n = d + 1`), giving you the induction hypothesis `ih`.
-/
TacticDoc induction'


/--
The `constructor` tactic is used to prove goals consisting of a logical AND ($\wedge$).
It splits the goal `P ∧ Q` into two separate goals: `P` and `Q`.
-/
TacticDoc constructor
