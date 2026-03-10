/-
  Tutorial 3: Subset Construction and Regular Expressions
  Course: Language and Computation (COMP2012)
  TA: Aref Mohammadzadeh
  Date: 19 February 2026
-/


import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene
import Proofs.RE

open Lang Dfa DFA Nfa NFA Lang.Examples Kleene Re RE

-- Abbreviations
abbrev a : RE SigmaABC := sym SigmaABC.a
abbrev b : RE SigmaABC := sym SigmaABC.b
abbrev c : RE SigmaABC := sym SigmaABC.c
abbrev zero : RE (Fin 2) := sym 0
abbrev one : RE (Fin 2) := sym 1
variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)
namespace section1

  /-!
    ## SECTION 1: RECAP

  #  1. A DFA consists of:
   - States Q
   - Initial state s
   - Final states F
   - Transition function δ : Q → Sigma → Q

  # 2. An NFA consists of:
   - States Q
   - Initial states S
   - Final states F
   - Transition function δ : Q → Sigma → Set Q

  # 3. NFA to DFA Transformation
    Every NFA can be transformed into a DFA that recognizes the exact same language.

    Because an NFA can be in multiple states simultaneously, the equivalent DFA
    treats these "sets of NFA states" as its own single states.

    - **DFA States:** Subsets of the NFA's states (the Power Set).
    - **Initial State:** The subset containing the NFA's initial states.
    - **Final States:** Any subset that contains at least one NFA final state.
    - **Transitions:** From a subset `S` reading symbol `x`, the DFA transitions
      to the union of all NFA states reachable from any state in `S`.

    Formally, given an NFA A we construct a DFA B where:
-/

def nfa2dfa' (A : Nfa.NFA Sigma) : Dfa.DFA Sigma
     := { Q := Finset A.Q
          s := A.S
          F := ⟪ S ∈ nfaDfa.Pow A.Q |
                ∃ (q : A.Q) , q ∈ S ∧ q ∈ A.F ⟫
          δ := δ_step A }

/-
  # 4. Example of DFA to NFA:

    **Language:** All binary words that **start and end with different bits**.
    (e.g., "01", "10", "0001", "1110"). Length must be at least 2.

    Let's build this in our different formalisms to see how they connect.
  -/

  -- 1. The NFA
  -- Logic:
  -- q0 (start) reads the first bit.
  -- If it reads 0, it goes to q1 (waiting for a 1 at the end).
  -- If it reads 1, it goes to q2 (waiting for a 0 at the end).
  -- Non-determinism: In q1/q2, it can loop, or "guess" the current bit is the last one.
  inductive Q_nfa : Type | q0 | q1 | q2 | q3 | q4
  deriving Fintype, DecidableEq
  open Q_nfa

  abbrev A_NFA : NFA (Fin 2) :=
  {
    Q := Q_nfa
    S := {q0}
    F := {q3, q4}
    δ := λ q x => match q, x.val with
      | q0, 0 => {q1}
      | q0, 1 => {q2}
      | q1, 0 => {q1}
      | q1, 1 => {q1, q3} -- Guessing this '1' is the end
      | q2, 0 => {q2, q4} -- Guessing this '0' is the end
      | q2, 1 => {q2}
      | q3, _ => {}
      | q4, _ => {}
      | _, _  => {}
  }

 -- example : [1, 0 , 0] ∈ L A_NFA := by simp [Nfa.L, Nfa.δ_step, Nfa.δ_star ]
 -- example : [1, 0 , 1] ∉ L A_NFA := by simp [Nfa.L, Nfa.δ_step, Nfa.δ_star ]






  -- 2. Finding the DFA via Subset Construction
  -- Let's trace the reachable subsets from S0 = {q0}:
  -- S0 = {q0}
  -- S1 = {q1}        (reached by S0 reading 0)
  -- S2 = {q2}        (reached by S0 reading 1)
  -- S13 = {q1, q3}   (reached by S1 reading 1) -> ACCEPTING
  -- S24 = {q2, q4}   (reached by S2 reading 0) -> ACCEPTING

  inductive Q_dfa : Type | S0 | S1 | S2 | S13 | S24
  deriving Fintype, DecidableEq
  open Q_dfa

  abbrev A_DFA : DFA (Fin 2) :=
  {
    Q := Q_dfa
    s := S0
    F := {S13, S24}
    δ := λ q x => match q, x.val with
      | S0, 0  => S1
      | S0, 1  => S2
      | S1, 0  => S1
      | S1, 1  => S13
      | S2, 0  => S24
      | S2, 1  => S2
      | S13, 0 => S1
      | S13, 1 => S13
      | S24, 0 => S24
      | S24, 1 => S2
      | _, _   => S0
  }

/-

  # 5. Regular Expressions (RE)
    Regular expressions describe languages algebraically.
    They are equivalent to DFAs and NFAs.

    Operations:
    - **Union (`+`)**: `L₁ + L₂`
    - **Concatenation (`⋅`)**: `L₁ ⋅ L₂`
    - **Kleene Star (`★`)**: `L★`
    - **Empty String (`ε`)**: empty word `[]`.
    - **Empty Set (`∅`)**

    Regular expressions use these to formally describe languages:
-/
variable (Sigma : Type)[Alphabet Sigma]

inductive RE' : Type
| sym : Sigma → RE'
| append : RE' → RE' → RE' -- ⋅
| plus : RE' → RE' → RE' -- +
| epsilon : RE' -- ε
| empty : RE' -- ∅
| star : RE' → RE' -- ★

-- ## 6. The Regular Expression for our example:

  -- Logic: (Starts with 0, middle is anything, ends with 1) OR
  --        (Starts with 1, middle is anything, ends with 0)


  abbrev A_RE : RE (Fin 2) :=
    (zero ⋅ (zero + one)★ ⋅ one) + (one ⋅ (zero + one)★ ⋅ zero)

end section1

namespace RegexExercises
/-!

  ### SECTION 2: Other examples of Regular expressions

  -/

  -- Helper abbreviation for "Any sequence of characters"
  abbrev any : RE SigmaABC := (a + b + c)★

  -- Q1: All words such that all 'a's appear before all 'b's,
  -- and all 'b's appear before all 'c's. (e.g., "aaabbc", "bc", "a", "ac").
  abbrev e1 : RE SigmaABC :=
    sorry

  -- Q2: All words that DO NOT contain the consecutive substring "aa".
  -- If we see an 'a', the next character MUST be a 'b' or 'c', unless it's the end of the word.
  abbrev e2 : RE SigmaABC :=
    sorry

  -- Q3: All words whose length is a multiple of 3.
  -- (e.g., "abc", "aaa", "cbaabc", "ε").
  abbrev e3 : RE SigmaABC :=
    sorry

  -- Q4: All words where the 3rd symbol from the end is 'c' OR the word ends with 'c'.
  -- (e.g., "cab", "ccaa", "abcbb", "c", "abac").
  abbrev e4 : RE SigmaABC :=
    sorry

end RegexExercises
