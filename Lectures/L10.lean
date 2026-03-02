import Proofs.Lang
import Proofs.Autom

namespace pumping
open Lang Dfa
variable (Sigma : Type)[Alphabet Sigma]
instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)
variable {Sigma : Type}[Alphabet Sigma]

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}
/-
What is a regular language?
A language that can be defined by a DFA.
We don't necessarily know what that DFA is! But we do know
it's got some number of states, let's call this p.
Then, for accepted words longer than p, these words must
traverse a (nonempty) loop in the DFA.
In particular, the first loop must occur in the first p
characters.
This means if we traverse the loop multiple times, or cut
it out, then the corresponding words must also be accepted.
This gives rise to the Pumping Lemma:
-/
theorem pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n →
      ∃ x y z : Word Sigma,
      w = x ++ y ++ z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    ) := by sorry
/-
We use this to show that a language is NOT regular.
We assume, for a contradiction, that it is regular.
Then the pumping lemma must hold.
We will try to show that it does not hold, by picking
a long word where we cannot "traverse the loop".
The length of this word must be longer than the pumping
length. We know such a length must exist (if it's regular)
but we don't know what it is - hence we just give it
a name, like "p".
We pick our word in such a way that it is longer than p,
but no substring within the first p characters can be
repeated while remaining in the language.
That will show that the pumping lemma does not hold,
leading to a contradiction.
Hence, the language must not be regular.

Example: L = { a^n | n is prime }
To prove this is not regular, we assume for a contradiction
that it is.
Then the Pumping Lemma must hold.
Hence, there exists some unknown pumping length, let's
call it p.
Let q be prime such that q > p.
Consider the word a^q ∈ L
By the pumping lemma, this can be written as
xyz, where |xy| ≤ p and |y| ≥ 1
Let |y| = r, 1 ≤ r ≤ p
Then |xz| = q - r.
By the pumping lemma, xy^{q-r}z must be in L
But xy^{q-r}z = a^{q-r+(q-r)r} = a^{(1+r)(q-r)}
Hence, this is a non-prime number of as
xy^{q-r}z ∉ L, so the pumping lemma does not hold
This is a contradiction, and hence L is not regular.
-/
end pumping
/-
Context-Free Grammars CFG
level 2 of the Chomsky hierarchy
syntax of programming languages

arithmetic expressions
numbers, variables , + , * , (, )

( * a
3 + 4 * (5 + 1)

Sigma = { a , + , * , ( , ) }

a + a * (a + a)

CFG GA
Variables (Nonterminal symbols)
Sigma (Terminal symbols)

E = Expressions
T = Term
F = Factor

E , T , F : non terminal symbols
S = E , start symbol

rules, productions

E => T
E => E + T
T => F
T => T * F
F => a
F => ( E )

What is the language of the grammar ?

E => T => T * F => F * F => a * F
=> a * a

a * a ∈ L(GA)

E => T => T * F => F * F => a * F
=> a * ( E ) => a * ( E + T )
=> a * ( T + T ) => a * ( F + T )
=> a * ( F + F ) => a * ( a + F )
=> a * ( a + a )

a * ( a + a ) ∈ L(GA)

E => T | E + T
T => F | T * F
F => a | ( E )

-/
namespace Cfg
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure CFG : Type 1 where
  NT : Type
  [ alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma ))

open CFG
open Sum

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

abbrev Symbol : Type
  := G.NT ⊕ Sigma

scoped instance : Coe G.NT (Symbol G) :=
  ⟨Sum.inl⟩

scoped instance : Coe Sigma (Symbol G) :=
  ⟨Sum.inr⟩

abbrev Sent : Type
  := Word (Symbol G)

abbrev Deriv : Set (Sent G × Sent G)
:= { (α , β) | ∃ α₁ α₂ ,
      ∃ A , α = α₁ ++ [inl A] ++ α₂
      ∧ ∃ γ , (A , γ) ∈ G.P
      ∧ β = α₁ ++ γ ++ α₂ }

-- infixr:70 " ⟹ " => Deriv

inductive DerivStar : Sent G × Sent G → Prop
| refl : ∀ α , DerivStar (α , α)
| step : ∀ α β γ ,
    Deriv G (α , β) → DerivStar (β , γ)
    → DerivStar (α , γ)

abbrev emb : Word Sigma → Sent G
:= List.map inr

abbrev L : Lang Sigma
:= { w | DerivStar G ([inl G.S],emb G w)}


end Cfg



namespace CfgEx
open Lang
open Cfg
open Sum
open scoped Cfg.CFG

inductive SigmaA : Type
| lpar | rpar | a | plus | times
deriving Fintype, DecidableEq
open SigmaA

inductive NTA : Type
| E | T | F
deriving Fintype, DecidableEq
open NTA

abbrev E : NTA ⊕ SigmaA := inl (NTA.E)
abbrev T : NTA ⊕ SigmaA := inl (NTA.T)
abbrev F : NTA ⊕ SigmaA := inl (NTA.F)
abbrev lpar : NTA ⊕ SigmaA := inr SigmaA.lpar
abbrev rpar : NTA ⊕ SigmaA := inr SigmaA.rpar
abbrev a : NTA ⊕ SigmaA := inr SigmaA.a
abbrev plus : NTA ⊕ SigmaA := inr SigmaA.plus
abbrev times : NTA ⊕ SigmaA := inr SigmaA.times

abbrev GA : CFG SigmaA :=
{ NT := NTA
  S := NTA.E
  P := { (NTA.E, [T]),
         (NTA.E , [E,plus,T]),
         (NTA.T, [F]),
         (NTA.T , [E,times,T]),
         (NTA.F, [a]),
         (NTA.F, [lpar,E,rpar])}
   }

end CfgEx
