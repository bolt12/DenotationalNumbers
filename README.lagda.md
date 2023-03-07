# From Geometry to Algebra: A Denotational Journey Through Whole Numbers, Fractions, and DivMod Type

In this blog post, we will explore the geometric interpretation of whole numbers and how
it can help us understand addition, subtraction, multiplication, and division. We will
then utilise this geometric interpretation to devise a denotational model for fractions,
which will shed light on why fraction addition appears to be so contrived.

But our journey won't stop there. With the denotation for fractions in hand, we will
explore the `DivMod` type and develop a vocabulary for combining values of this type via
denotational design. This will allow us to regain expressive strength lost by integer
division and prove stronger lemmas that weren't possible before.

This post is a literate Agda file which means it has a machine-checked Agda formalization
to make our ideas precise and provide concrete examples that demonstrate the power of
denotational thinking. So, join us on this mystical journey through the world of numbers,
and let's unlock the mysteries of arithmetic operations together.

## Number Lines

```agda
module README where
```

A (whole) number is a point in the number line. The number line is a
line with a designated mark/point on it as $0$. This line has equally
spaced marks to the right of $0$ and each of these marks represent a
number $1$, $2$, $3$, $4$, etc., as on a ruler. The whole numbers are
all the points present in this "infinite ruler". A whole number $n$ can
also be identified with the length of a line segment $[0, n]$ from $0$ to
$n$. For any line segment $[x, y]$ from a point $x$ to another point
$y$ on the number line, where it is understood from the notation
$[x, y]$ that $y$ is to the right of $x$ — we say the length of $[x, y]$
is $n$ for a whole number $n$ if, by sliding $[x, y]$ to the left
along the number line until $x$ rests at 0, the right endpoint $y$
rests at n.

An important aspect is that the positions of the whole numbers depend
completely on the choice of $0$ and $1$. Once these two numbers have
been fixed, the positions of the other whole numbers are likewise
fixed. The segment $[0, 1]$ is called the _unit segment_, and the
number $1$ is sometimes referred to as the _unit_.

*NOTE:* That two lines are the same line if they have the same choice
of unit.  There are occasions when it is useful to change the unit, in
which case there will be a different number line to deal with.

With this being said, the four arithmetic operations can be
interpreted geometrically in the number line.

For addition, we have that for any two whole numbers $m$ and $n$, $m + n = \text{the length of the segment obtained by concatenating the segments}\ [0, m]\ \text{and}\ [0, n]$:

```a
        m + n
<--------------------->
|------|--------------|
 [0, m]    [0, n]
```

As noted above a fundamental issue in the arithmetic operations on
whole numbers concerns the importance of having the _same unit_ as a
fixed reference! For example, imagine we have these two _different_
number lines:

```a
|--|--|--|--|--|--|  (A)
0  1  2  3  4  5  6

|-----|-----|-----|  (B)
0     1     2     3
```

If one takes segment $[0, 1]$ from the lower line (B) and segment $[0, 2]$
from the upper line (A), could it be argued that $1 + 2 = 2$?

```a
|-----|--|--|
   1  +  2
```

Although it looks like the lengths match with 2 the mistake is that
all geometric representations of operations on whole numbers, are done
on one number line, and therefore are done with respect to a fixed
unit segment. So the claim that $1 + 2 = 2$ is wrong because the unit
segments of the two lines are different, and thus they can't be
concatenated, because mixing units would lead to a line with an
undefined unit. If one would anotate each number with its respective unit
it would make it obvious the above expression shouldn't even be valid:
$1\_{A} + 2\_{B} = 2\_{B}$.

To drive the point home, look at the following expressions:

- $9 − 2 = 1$
- $8 + 16 = 2$
- $19 + 17 = 3$

Although every equation above is wrong according to the arithmetic of
whole numbers as we know it, it is not as absurd as it appears, once
one makes the units explicit:

- $9\_{\text{days}} − 2\_{\text{days}} = 1\_{\text{week}}$
- $8\_{\text{months}} + 16\_{\text{months}} = 2\_{\text{years}}$
- $19\_{\text{eggs}} + 17\_{\text{eggs}} = 3\_{\text{dozen eggs}}$

The point is to underline the implicit or explicit role played by the
unit in any addition or subtraction of numbers. The concept of a whole
number is an abstract one.

Whatever the interpretation of the abstract operations, each operation
must refer to the _same unit_.

Given this let's model what we learned so far:

- The number line is an infinite line with equally spaced marks to the
  right of the initial mark $0$. Two lines are equal if they have the
  same unit.

```agda
  open import Level renaming (zero to zeroℓ; suc to sucℓ)
  open import Data.Nat as ℕ using (ℕ)
  open import Relation.Binary

  -- Take a straight line and mark off a point as 0 (zero). Then fix a
  -- segment to the right of 0 and call it the unit segment. Mark the
  -- right endpoint of this segment on the line, thereby generating
  -- the first marked point. The multiples of this marked point then
  -- form a sequence of equispaced points to the right of 0.
  --
  -- Natural number line:
  -- zero ∣ ∣ ∣ ∣ ∣ ∣ ∣ ∣ ...
  --    0 1 2 3 4 5 6 7 8 ...
  --    
  data Line {Unit : Set} (unit : Unit) : Set where
    zero : Line unit
    _∣ : (l : Line unit) → Line unit
```

  Given this the natural number line is the line which unit is $1$
  (i.e. segment $[0, 1]$).

```agda

  -- Natural number line uses 1 as the unit
  ℕ-Line : Set
  ℕ-Line = Line 1
```

- Marks (or points) in the line either starts at the $0$ mark or is a
  successor of the previous one. Note that the length between each two
  consecutive marks is equally spaced in the line.

```agda
  -- A mark (or point) in the line depends on the line it sits on
  -- The length between two successive marks, i.e. a segment line
  -- [a, suc a] means 1 unit value.
  -- data Mark {Unit : Set} (line : Line Unit) : Set where
  --   zero : Mark line
  --   suc : (m : Mark line) → Mark line
```

  Agda supports number literals overloading via `BUILTING FROMNAT`
  pragma. We'll use this in order to be able to write $1$, $2$, etc. for
  each successive mark on any line, however each literal is going to
  have an implicit argument about which line is it on (i.e. what
  corresponding unit does this particular mark is in relation to).

```agda
  record NumberLiteral {Unit} (unit : Unit) : Set where
         field fromNat : ℕ → Line unit
  
  open NumberLiteral {{...}} public

  {-# BUILTIN FROMNAT fromNat #-}

  instance
    LineNat : ∀ {Unit} {unit : Unit} → NumberLiteral unit
    LineNat .NumberLiteral.fromNat = toMark
      where
        toMark : ∀ {Unit} {unit : Unit} (n : ℕ) → Line unit
        toMark ℕ.zero = zero
        toMark (ℕ.suc x) = (toMark x) ∣

  -- Mark (number) one in the number line
  𝟙 : ℕ-Line
  𝟙 = zero ∣

  -- Mark (number) one in the number line using literal overloading
  𝟙ₒ : ℕ-Line
  𝟙ₒ = 1

  -- Mark one in any number line
  𝟙ℓ : ∀ {Unit} {unit : Unit} → Line unit
  𝟙ℓ = 1
```

  So from now on when you see a number literal please assume it is the
  corresponding successive mark on any line, unless it is explicit which
  line it is.

- In a similar way to natural numbers as we know them, it is to be
  expected that if a mark $a$ is to the right of a mark $b$ then $a > b$.
  This allow us to define a line segment and its semantic:

```agda
  infix 4 _≤_
  data _≤_ {Unit : Set} {unit : Unit} : Rel (Line unit) 0ℓ where
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} (m≤n : m ≤ n) → m ∣   ≤ n ∣

  -- The length of segment [x, y] is n for a whole number n if, by
  -- sliding [x, y] to the left along the line until x rests at
  -- 0, the right endpoint y rests at n.
  [_,_] : ∀ {Unit : Set} {unit : Unit} (m n : Line unit) {m≤n : m ≤ n} → Line unit
  [ zero , zero ] = zero
  [ zero , y ∣ ]  = y ∣
  [ x ∣ , y ∣ ] {s≤s x≤y} = [ x , y ] {x≤y}
```

- Addition (`_+_`) of two marks (in the _same_ line) is the length of
  concatenatening two segment lines, i.e. adding two marks $x$ and
  $y$ can be understood as starting in $y$ and moving $x$ marks to the
  right of $y$ (or vice-versa).

```agda
  infixl 6 _+_
  _+_ : ∀ {Unit} {unit : Unit} → Line unit → Line unit → Line unit
  zero + y = y
  x ∣ + y  = x + y ∣
```

Everything looking good so far! There's a still a few operations left
to mention.

We've actually already defined subtraction somewhere above. It is easy
to see how, when understanding what subtraction means geometrically:
$m - n$, when $m > n$, in the number line is exactly the length of
going from $n$ to $m$, thus $m - n \equiv [n , m]$.

```a
|--------|-----|
0        n     m
         |-----|
          m - n
```

So:

```agda
  _-_ : ∀ {Unit} {unit : Unit} (m n : Line unit) {m≤n : n ≤ m} → Line unit
  (m - n) {n≤m} = [ n , m ] {n≤m}
```

What about multiplication? The product $3 * 4$, for example, can be
interpreted as the number $3$ on a number line whose unit $1$ is taken
to be (the magnitude or size represented by) the number $4$. Visually:

```a
|--|--|--|--|--|--|--|--|--|--|--|--|
0  1  2  3  4  5  6  7  8  9  10 11 12

Now introduce new markers on the same line, where the new unit is $4$:

|--|--|--|--|--|--|--|--|--|--|--|--|
0  1  2  3  4  5  6  7  8  9  10 11 12
|           |           |           |
0̣           1̣           2̣           3̣
```

In particular, $3 * 4$ is four copies of the new unit
and is therefore $3$ in the new number line.

This idea of using a new unit to re-interpret the multiplication of
numbers provides an alternative way to understand the multiplication
of fractions, that I am going to talk about later.

Unfortunately, this interesting line transformation is not expressable
when keeping both marks and the `Unit` abstract. Instead we model it
as successive jumps of groups of marks on the same line:

```agda
  infixl 7 _*_
  _*_ : ∀ {Unit} {unit : Unit} → Line unit → Line unit → Line unit
  zero * y = zero
  x ∣ * y  = y + (x * y)
```

## Fractions

```agda
  open import Data.Product 

  Fraction′ : ∀ {Unit} (d : Unit) → Set
  Fraction′ {Unit} d = ∃ {A = Unit} Line × Line d

  ½′ : Fraction′ {ℕ} (ℕ.suc (ℕ.suc ℕ.zero))
  ½′ = (ℕ.suc ℕ.zero , 1) , 1

  ¾′ : Fraction′ {ℕ} (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero))))
  ¾′ = (ℕ.suc ℕ.zero , 3) , 1 -- or ((3 , 1) , 1) 

  Fraction : ∀ {Unit : Set} (d : Unit) → Set 
  Fraction {Unit} d = ∃ {A = Unit} λ n → Line (n , d)

  ½ : Fraction {ℕ-Line} 2
  ½ = 1 , 1

  ¾ : Fraction {ℕ-Line} 4
  ¾ = 1 , 3 -- or (3 , 1)

  _≈_ : ∀ {d : ℕ} → Fraction′ d → Fraction′ d → Set
  ((u , n) , m) ≈ ((u′ , n′) , m′) = {!!}
``` 


---


Take the concept of a fraction or a decimal, for example. It is
almost never clearly defined. Yet children are asked to add, multi-
ply and divide fractions and decimals without knowing what they
are or what these operations mean, and textbooks contribute to
children’s misery by never defining them either.
