# Number Theory Game

An interactive game that teaches integer arithmetic and Number Theory through theorem proving in Lean 4. It uses the Lean4 Game Engine and is designed to run live at [adam.math.hhu.de](https://adam.math.hhu.de).

## Game Content
The game translates classical pen-and-paper mathematics into rigorous code, introducing players to fundamental properties of integers. It currently consists of 6 worlds:

* **Divisibility Club**: The basics of divisibility ($a \mid b$), providing a foundation for integer arithmetic.
* **Congruence**: An introduction to modular arithmetic ($a \equiv b \pmod m$) and its algebraic properties.
* **GCD (In Search of the GCD)**: Defining the Greatest Common Divisor using Bézout's identity and proving the General Cancellation Law.
* **Linear Congruences and CRT**: Bringing everything together to solve linear equations ($a \cdot x \equiv b \pmod m$), find modular inverses, and prove fundamental results like Euclid's Lemma and the Chinese Remainder Theorem.
* **Divisibility Rules**: A short breather before the finale. You will formally prove the classic divisibility rules from school (for 2, 3, 4, 5, 9, 10, and 11) as direct consequences of modular arithmetic and polynomial congruences.
* **Problems**: The grand finale! You apply your massive toolkit of abstract theorems to crush concrete numerical challenges, compute huge powers, solve linear congruences, and use the Chinese Remainder Theorem in practice.


## Prerequisites
The game is extremely approachable and serves as an introduction to integer arithmetic and formal proofs. No advanced programming or math background is strictly required to get started.

## Building Locally
There are multiple ways to run the game while developing it. For full instructions, see the [lean4game documentation on running locally](https://github.com/leanprover-community/lean4game/blob/main/docs/running-locally.md).
*The recommended setup for development is using a VSCode Devcontainer or Codespaces.*

## Contributing
PRs and issues fixing typos, inconsistencies, missing hints, or unclear explanations are very welcome!
