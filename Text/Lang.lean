import VersoManual
import Text.Meta
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Proofs.Lang"

#doc (Manual) "Languages" =>
%%%
tag := "lang"
%%%

# What is a language?

We may have an intuitive idea but in the context of this module we will use a precise definition:
- A language is is a set of words.
- A word is a sequence of symbols.
- A symbol is an element of an alphabet.
- An alphabet is any finite type with a decidable equality.

How to express this in Lean?

## Alphabets

We start with the alphabet it is common to use the greek letter Σ for alphabets but this is actually a reserved word in Lean hence I will write `Sigma`.

We will use type classes which express that a type has a certain structure. We use two type classes which are predefined in Lean
- `Fintype` the type is finite, that is we can write a loop looking at all elements,
- `DecidableEq` the type has a decidable equality, that is we can use a boolean test comparing two symbols.

We define a new type class `Alphabet` which expresses that a type is both:
```anchor Alphabet
class Alphabet (Sigma : Type) : Type where
  (fintype : Fintype Sigma)
  (decEq   : DecidableEq Sigma)
```
In the sequel we will often assume that `Sigma` is an alphabet
```anchor Sigma
variable (Sigma : Type)[Alphabet Sigma]
```
Here are some examples for alphabets, we will often use an alphabet just made up  from the symbols `a`,`b`,`c` which can be defined as follows:
```anchor SigmaABC
inductive SigmaABC : Type
| a | b | c
```
Lean can infer that this is an `Alphabet`, see the Lean source for details.

Another example are binary digits `0` and `1` which can be defined:
```anchor SigmaBin
abbrev SigmaBin : Type
:= Fin 2
```
We would expect that `Char` is another example of a finite type but since it is rather large (there are about 1,114,112 unicode characters) we Lean does not consider it as finite. We will just ignore this.



## Words

Words are just lists of symbols:
```anchor Word
abbrev Word := List Sigma
```
Note that this definition uses an implicit parameter `Sigma` hence we can will write `Word Sigma` to refer to the set of words over the alphabet `Sigma`.

So for example `[a,a,b,c] : Word SigmaABC` or
`[1,1,0] : Word SigmaBin`. We also introduce a notation `a^3` which is short for `[a,a,a]`. We can use `++` so for example `a^3 ++ b^3` is just a shorthand for `[a,a,a,b,b,b]`.

We also use the (overloaded) function `count` which counts the number of occurences of a symbol, so for example `[a,a,b,c].count a` evaluates to `2`.

## Languages

A language is a set of word, hence we define
```anchor Lang
abbrev Lang : Type :=  Set (Word Sigma)
```
but exactly what is a set in Lean? Actually sets are the same as predicates, hence languages are just predicates on words, this is `Word Sigma → Prop`.

However, Lean's `Set` come with some syntactic conventions which are common in set-based Mathematics. Given a language `L : Lang Sigma` and `w : Word Sigma` we write `w ∈ L` to express that `w` is in the language. Since `L` is just a predicate this is the same as saying `L w`.

### aeqb
Let's define a language over `SigmaABC` namely the language of words which contain the same number of `a` and `b` (we don't care about `c`).
We can use set comprehension notation to define this:
```anchor aeqb
abbrev aeqb : Lang SigmaABC
:= { w : Word SigmaABC | w.count a = w.count b}
```

This is equivalent to defining a predicate:
```anchor aeqb_pred
abbrev aeqb : Lang SigmaABC
| w => w.count a = w.count b
```

We have that `[a,b] ∈ aeqb` and `[a,a,b,c] ∉ aeqb` (note that `w ∉ L` just means `¬ (w ∈ L)`). We can prove this easily (and now we are grown up enough to use `simp`).
```anchor aeqb_ex
example : [a,b] ∈ aeqb := by simp
example : [a,a,b,c] ∉ aeqb := by simp
```

### anbn
Another example of a language over `SigmaABC` is the set of words which are formed from a sequence of `a`s followed by `b`s (no `c` allowed), We define this language:
```anchor anbm
abbrev anbm : Lang SigmaABC
:= { a^m ++ b^n | (m : ℕ)(n : ℕ)}
```
So for example `[a,a,b] ∈ anbm` while `[b,a,a] ∉ anbm`. For these cases `simp` isn't powerful enough. I leave it as an exercise to formally prove these examples.

### div3

Let's define a language over `SigmaBin` namely the language of binary numbers in little Endian (i.e. the least significant digit comes first)divisible by `3`.

We first define an evaluator for binary numbers:
```anchor val
def val : Word SigmaBin → ℕ
| []       => 0
| (x :: xs) => x + 2 * val xs
```
So for example `val [0, 1, 1]  = 6` while `val [1, 0, 1] = 5`. Now using the relation `m ≣ n [MOD k]` (which means that `m` and `n` have the same remainder when divided by `k`) we can define:
```anchor div3
abbrev div3 : Lang SigmaBin
:= { w | val w ≡ 0 [MOD 3]}
```
For example `[0, 1, 1] ∈ div3` but `[1, 0, 1] ∉ div3`.

### Finite languages

We can also define languages which only consist out of a finite set of words. We define the language of words over `SigmaABC` consisting out of 1 ,2 or 3 `a`s:
```anchor a3
def a3 : Lang SigmaABC
:= {[a],[a,a],[a,a,a]}
```

How does this work? Lean defines a type `Finset` which is very similar to `List` but we identify sequences which have the same elements, e.g. `{1,2,2,3} = {3,2,1}`. We have already seen the `∈` predicate on lists and this is also used to coerce `Finset` to `Set`. Equivalently, we could have defined
```anchor a3_pred
def a3 : Lang SigmaABC
| w => w=[a] ∨ w=[a,a] ∨ w=[a,a,a]
```

# Operations on Languages

## Union

Since languages are sets we can use the usual set theoretic operations in Lean. Given `L₁ L₂ : Lang Sigma` we construct the union `L₁ ∪ L₂ : Lang Sigma`. There is also the empty set `∅ : Lang Sigma`.

Viewing sets as predicates these are equivalent to
```anchor union_pred
abbrev L₁₂ : Lang Sigma
| w => w ∈ L₁ ∨ w ∈ L₂
abbrev L₀ : Lang Sigma
| _ => False
```
with `L₁₂ = L₁ ∪ L₂` and `L₀ = ∅`

As a running example we use the finite languages
```anchor l1l2
abbrev L₁ : Lang SigmaABC
:= { [a] , [a,a] , [a,a,a] }
abbrev L₂ : Lang SigmaABC
:= { [a] , [b,c] }
```
so for example
```anchor l1ul2
L₁ ∪ L₂ = { [a]  , [a,a] , [a,a,a] , [b,c]}
```

If you remember some algebra from COMP2065 you should recognize that `∪` is a commutative monoid with `∅` as the neutral element, and the additional property that `L ∪ L = L` (idempotence).

## Concatenation

Another important operation is *concatenation* of languages, informally we say that given `L₁ L₂ : Lang Sigma` their concatention `L₁ ⋅ L₂ : Lang Sigma` is the set of words that can be formed by concatening (append) a word from `L₁` and a word from L₂. More precisely we define
```anchor concat_def
L₁ ⋅ L₂ = { w ++ v | (w ∈ L₁)(v ∈ L₂) }
```
Here we use another feature of the set notation, as a predicate we would have written this `L₃ = L₁ ⋅ L₂` as
```anchor concat_pred
def L₃ : Lang Sigma
| x => ∃ w v : Word Sigma ,
        w ∈ L₂ ∧ v ∈ L₂ ∧ x = w ++ v
```

Using `L₁`,`L₂` as defined above we construct their concatenation :
```anchor l1dotl2
  L₁ ⋅ L₂ =
    { [a,a], [a,b,c], [a,a,a], [a,a,b,c],
      [a,a,a,a], [a,a,a,b,c] }
```
`⋅` forms a monoid and the neutral element is the language which only contains the empty word
```anchor epsilon_def
ε = { ([] : Word Sigma) }
```

It is important not to confuse `∅` (the empty language) and `ε` (the language containing only the empty word).

## Star

Finally we look at the star operation written `L * : Lang Sigma` for `L : Lang Sigma`. The language `L *` is the set of words that we can obtain by repeatedly concatenating words from `L`. Using `*` we can construct infinite languages from finite ones. So for example
`{ [a] }* = { [] , [a], [a,a], [a,a,a], ...}`.

To define `L *` formally we first define the `n`th power of a language, that is give `L : Lang Sigma` and `n : ℕ` we define `L^n : Lang Sigma` by primitive recursion :
```anchor lpow_zero
L ^ 0 = ε
```
```anchor lpow_succ
L ^ (n + 1) = L ⋅ (L ^ n)
```

So for example:
```anchor l2pow2
  L₂ ^ 2 =
    { [a,a], [a,b,c], [b,c,a], [b,c,b,c] }
```
```anchor l2pow3
  L₂ ^ 3 =
    { [a,a,a], [a,a,b,c], [a,b,c,a],
      [a,b,c,b,c], [b,c,a,a], [b,c,a,b,c],
      [b,c,b,c,a], [b,c,b,c,b,c] }
```

Now we define `L *` as the union of all the powers:
```anchor star_def
L * = { w : Word Sigma | ∃ n : ℕ, (w ∈  L ^ n) }
```

So for example
```anchor l2starex
  [a,b,c,a,a,b,c] ∈ L₂ *
```
because `[a,b,c,a,a,b,c] ∈ L₂ ^ 5`. We can also use `*` to define a language equivalent to `anbm` namely `{ [ a ]} * ⋅ { [ b ] } *`.

# Kleene algebra

Let's apply what we have learned about algebra in *Introduction to formal reasoning*.

We have that `∪` and `∅` form a commutative monoid
```anchor union_assoc
  (L ∪ K) ∪ M = L ∪ (K ∪ M)
```
```anchor union_empty_left
  (∅ : Lang Sigma) ∪ L = L
```
```anchor union_empty_right
  L ∪ (∅ : Lang Sigma) = L
```
```anchor union_comm
  L ∪ K = K ∪ L
```
which also is idempotent (unlike `+ , 0` since it is not true that `m + m = m`)
```anchor union_idem
  L ∪ L = L
```

We also have a monoid for `⋅,ε` but note that this monoid is not commutative (unlike `* , 1`)

```anchor concat_assoc
  (L ⋅ K) ⋅ M = L ⋅ (K ⋅ M)
```
```anchor concat_eps_left
  (ε : Lang Sigma) ⋅ L = L
```
```anchor concat_eps_right
  L ⋅ (ε : Lang Sigma) = L
```

Next we have the distributivity and the zero laws which are exactly the same has for `+` and `*`. But note that this time we do need both direction because `⋅` is not commutative.

```anchor concat_union_left
  (L ∪ K) ⋅ M = (L ⋅ M) ∪ (K ⋅ M)
```
```anchor concat_union_right
  L ⋅ (K ∪ M) = (L ⋅ K) ∪ (L ⋅ M)
```
```anchor concat_empty_left
  (∅ : Lang Sigma) ⋅ L = (∅ : Lang Sigma)
```
```anchor concat_empty_right
  L ⋅ (∅ : Lang Sigma) = (∅ : Lang Sigma)
```

We summarize that `∪,∅,⋅,ε` forms a semiring like `+,0,*,1` but `∪` is idempotent unlike `+` but `*` is not commutative unlike `*`.

We have some extra operator `*` which doesn't show up for natural numbers. We can charaterize it as the least operator which is closed under `ε ∪ (L ⋅ (L *)`. We first show that it is closed:
```anchor star_closed
  (ε : Lang Sigma) ∪ (L ⋅ (L *)) ⊆ (L *)
```

and that it is the least one with this property

```anchor star_least
  (h : (ε : Lang Sigma) ∪ (L ⋅ X) ⊆ X) :
  L * ⊆ X
```

In the last statement we actually quantify over all languages `X` which means that we are actually using higher order logic. Dexter Kozen has shown that we can avoid this and can just use some first order axioms which is what is called a *Kleene algebra*.
