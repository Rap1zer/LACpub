/-
COMP2012 (LAC) 2026

Exercise 4

We are asking you to provide informal proofs
(i.e. in English) that the languages L₁, L₂ are
not regular. We are using Lean to specify the setup,
but you should give your answer in a comment.

If you are very Lean savvy you can try to do at
least the outline in Lean and rely on some lemmas
which are evident but which you don't want to
prove.
-/
import Mathlib.Tactic.DeriveFintype
import Proofs.Lang
import Proofs.Autom
open Lang Dfa DFA Lang.Examples SigmaABC

-- Here are the two languages:
abbrev L₁ : Lang SigmaABC
:= { a^n ++ b^m ++ c^(m+n)| (m : ℕ)(n : ℕ)}

abbrev L₂ : Lang SigmaABC
:= { w | w.count a = 2*(w.count b)
       ∧ w.count b = 2*(w.count c) }

-- this is the pumping lemma in Lean
-- we add it as an axiom here but it is
-- provable from our definition of DFA.
variable (Sigma : Type)[Alphabet Sigma]
instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)
variable {Sigma : Type}[Alphabet Sigma]

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}

axiom pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n ∧ w ∈ L₁ →
      ∃ x y z : Word Sigma,
      w = x ++ y ++ z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    )

-- Exercises

theorem ex1 : ¬ ∃ A : DFA SigmaABC, L A = L₁
:= sorry
/-
Proof that L₁ is not regular (in English).
  We can use the pumping lemma to provide a proof by contradiction that L₁ is not regular.

  L₁ describes a set of strings where "a" is repeated n times, "b" is repeated m times,
  and "c" is repeated a number of times equal to n + m.

  If a language is regular, then for all strings that are length of at least p, there will be a
  section of the string that can be pumped / repeated and still belong in the language. Therefore,
  if we want to prove L₁ is NOT a regular language, then we have to find a string in L₁ of at least
  length p that fails the pumping lemma.

  Let's take the string a^p ++ b^p ++ c^(2p). It is at least of length p and it is part of L₁.

  According to the pumping lemma, the string can be split into x, y, and z.
  y is the section of the string to be pumped.
  Since |xy| <= p and the string begins with p occurrences of "a", the substring y must consist entirely of "a"s.

  However, if we pump with m=0, we remove at least one "a" while keeping the number of "b"s and "c"s.
  That means the number of "c"s is no longer equal to the number of "a"s plus "b"s.

  Therefore, a^p ++ b^p ++ c^(2p) fails the pumping lemma.
  Hence, L₁ is not a regular language.
-/

theorem ex2 : ¬ ∃ A : DFA SigmaABC, L A = L₂
:= sorry
/-
Proof that L₂ is not regular (in English).
    Similar to q1, we will prove L₂ is not a regular language via using the pumping lemma
    to provide a proof by contradiction.

    L₂ contains all strings w where:
    - the number of "a"s is twice the number of "b"s
    - the number of "b"s is twice the number of "c"s
    This forms a geometric ratio where the number of "a"s is 4 times the number of "c"s.

    As explained in q1, we have to find a string in L₂ of at least pumping length p that fails the
    pumping lemma.

    Let's choose the string c^p ++ b^(2p) ++ a^(4p). It is at least of length p and it is part of L₂.

    According to the pumping lemma, the string can be split into x, y, and z.
    y is the section of the string to be pumped.
    Since |xy| <= p and the string begins with p occurrences of "c", the substring y must consist entirely of "c"s.

    If we pump the substring y with m = 2 (so we replace y by y^2), then the number of "c"s changes while the number
    of "b"s and "a"s stays the same. Therefore the equality w.count b = 2*(w.count c) is no longer true.

    Therefore, c^p ++ b^2p ++ a^4p fails the pumping lemma.
    Hence, L₂ is not a regular language.
-/
