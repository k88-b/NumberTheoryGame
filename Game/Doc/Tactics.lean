import GameServer

/--
The `use` tactic is used to provide a \"witness\" to prove that something exists.
If your goal is `∃ k, 12 = 3 * k`, typing `use 4` changes the goal to `12 = 3 * 4`.
-/
TacticDoc use


/--
The `intro` tactic is used to introduce variables from a \"For all\" ($\\forall$) statement
or to assume the premise of an implication ($\\implies$).
For example, if the goal is `∀ a, P a`, typing `intro a` moves `a` into your context.
-/
TacticDoc intro


/--
The `ring` tactic automatically proves algebraic equalities like `x + y = y + x`
or `x * 1 = x`. It is a powerful tool so you don't have to manually apply axioms.
-/
TacticDoc ring


/--
The `obtain` tactic extracts a witness from a hypothesis that contains an \"exists\" ($\exists$).
If you have a hypothesis `h : x ∣ y` (which means `∃ k, y = x * k`), you can type
`obtain ⟨k, hk⟩ := h` to get the variable `k` and the equation `hk : y = x * k`.
-/
TacticDoc obtain


/--
The `rw` (rewrite) tactic replaces a term with an equivalent term based on an equality you have.
If you have `h : A = B`, typing `rw [h]` will replace `A` with `B` in your goal.
-/
TacticDoc rw


/--
The `unfold` tactic replaces a definition with its underlying meaning.
If your goal contains `a ≡ b (mod m)`, typing `unfold ModEq` will change it to `m ∣ a - b`.
-/
TacticDoc unfold


/--
The `have` tactic allows you to prove intermediate steps.
Typing `have h : X = Y := by ring` creates a new hypothesis `h` in your context.
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



