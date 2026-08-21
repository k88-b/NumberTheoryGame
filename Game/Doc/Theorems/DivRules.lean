import GameServer


/--
**Divisibility by 10**

The remainder of any number modulo 10 is exactly its last digit.
$10 \cdot k + d \equiv d \pmod{10}$.
-/
TheoremDoc div10_rule as "div10_rule" in "DivRules"


/--
**Divisibility by 2**

Since 2 divides 10, the remainder of any number modulo 2 depends entirely on its last digit.
-/
TheoremDoc div2_rule as "div2_rule" in "DivRules"


/--
**Divisibility by 5**

Since 5 divides 10, the remainder of any number modulo 5 depends entirely on its last digit — same idea as the rule for 2.
-/
TheoremDoc div5_rule as "div5_rule" in "DivRules"



/--
**Divisibility by 4**

Since 4 divides 100, the remainder of any number modulo 4 depends only on its last two digits.
$100 \cdot k + d \equiv d \pmod 4$.
-/
TheoremDoc div4_rule as "div4_rule" in "DivRules"


/--
**Divisibility by 9**

A number is congruent to the sum of its digits modulo 9.
This works beautifully because any number can be written as a polynomial evaluated at 10, and $10 \equiv 1 \pmod 9$.
-/
TheoremDoc div9_rule_3 as "div9_rule_3" in "DivRules"


/--
**Divisibility by 3**

Since 3 divides 9, a number is congruent to the sum of its digits modulo 3, just like with 9.
-/
TheoremDoc div3_rule_3 as "div3_rule_3" in "DivRules"


/--
**Divisibility by 11**

A number is congruent to the alternating sum of its digits modulo 11.
This works because $10 \equiv -1 \pmod{11}$, so evaluating the digit polynomial at 10 is congruent to evaluating it at -1!
-/
TheoremDoc div11_rule_3 as "div11_rule_3" in "DivRules"
