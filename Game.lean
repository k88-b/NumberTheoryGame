-- Import all worlds
import Game.Levels.Divisibility
import Game.Levels.Congruence
import Game.Levels.GCD
import Game.Levels.LinCong
import Game.Levels.DivRules
import Game.Levels.Problems

Title "Number Theory Game"

Introduction "
# Welcome to the Number Theory Game
#### An introduction to integer arithmetic and formal proofs.

In this game, we will explore the fascinating world of Number Theory.
We will start from the basic definition of divisibility and build our way up
to modular arithmetic and congruences.

Our ultimate goal is to understand how remainders work, how to safely manipulate
equations modulo $m$, and eventually reach powerful results like the
Chinese Remainder Theorem. We will do this by solving levels in a computer
puzzle game called Lean.

# Read this.

Learning how to use an interactive theorem prover takes time.
Tests show that the people who get the most out of this game are
those who read the help texts on the left side of the screen.

To start, click on the **Divisibility Club**.

## More

Click on the three lines in the top right and select \"Game Info\" for resources,
links, solutions, and ways to interact with the Lean community.
"


Info "
*Game version: 1.0*

## About

This game was created to teach Number Theory using formal verification in Lean 4.
It introduces players to fundamental properties of integers, modular arithmetic,
and divisibility, translating classical pen-and-paper mathematics into rigorous code.

## Credits

* **Creator:** Konstantin Belyanin

## Resources

* [Game Source Code](https://github.com/k88-b/NumberTheoryGame)
* [Game Solutions](https://github.com/k88-b/NumberTheoryGame_solutions)
* The [Lean Zulip chat](https://leanprover.zulipchat.com/) forum

## Problems?

Please ask any questions about this game in the
[Lean Zulip chat](https://leanprover.zulipchat.com/) forum, for example in
the stream \"New Members\". The community will happily help. Note that
the Lean Zulip chat is a professional research forum.
Please use your full real name there, stay on topic, and be nice. If you're
looking for somewhere less formal then head on over to the [Lean Discord](https://discord.gg/WZ9bs9UCvx).

If you experience issues / bugs with the game's content, please open an
[issue at the Number Theory Game repo](https://github.com/k88-b/NumberTheoryGame/issues).
"

-- Dependency tree: Players must complete worlds in this order
Dependency Divisibility → Congruence
Dependency Congruence → GCD
Dependency GCD → LinCong
Dependency LinCong → DivRules
Dependency DivRules → Problems

/-! Information to be displayed on the servers landing page. -/
Languages "en" "ru"
CaptionShort "An interactive introduction to Number Theory and modular arithmetic."
CaptionLong "In this game, you will learn the foundations of number theory.
Starting with basic divisibility, you will construct a full toolkit for
modular arithmetic (congruences) and prove theorems like a real mathematician."

CoverImage "images/cover.jpg"

MakeGame
