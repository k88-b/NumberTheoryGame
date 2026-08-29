import GameServer
-- import Mathlib.Tactic.Common

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file Lean file per world
which imports all its levels.
-/

-- Workaround: lean4game doesn't show errors inside the proof term of  `have _ := _`,
-- so we disable it

syntax (name := gameHave) "have" letConfig letDecl : tactic

macro_rules (kind := gameHave)
  | `(tactic| have $_:letId $_* : $_ :=%$tk $_) => do
    Lean.Macro.throwErrorAt tk "`have _ := _` cannot be used in this game. \
    There is a bug which would not display errors inside the proof term. \
     Please use `have _ : _` and provide the proof on the next lines."
    `(tactic| skip)


