import GameServer

-- Import all worlds
import Game.Levels.Divisibility
import Game.Levels.Congruence
import Game.Levels.GCD

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
"

Info "
*Game version: 1.0*

## Progress saving

The game stores your progress in your local browser storage.
If you clear your cookies or site data, your progress will be lost!
Make sure to download your game progress if you switch browsers.

## About

This game was created to teach Number Theory using formal verification in Lean 4.
It introduces players to fundamental properties of integers, modular arithmetic,
and divisibility, translating classical pen-and-paper mathematics into rigorous code.
"

-- Dependency tree: Players must complete worlds in this order
-- Dependency Divisibility → Congruence

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "An interactive introduction to Number Theory and modular arithmetic."
CaptionLong "In this game, you will learn the foundations of number theory.
Starting with basic divisibility, you will construct a full toolkit for
modular arithmetic (congruences) and prove theorems like a real mathematician."
-- CoverImage "images/cover.png" -- Uncomment if you add an image later!

MakeGame
