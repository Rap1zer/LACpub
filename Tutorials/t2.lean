import Proofs.Lang
import Proofs.Autom

open Lang Dfa DFA Nfa NFA Lang.Examples SigmaABC
variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)

/-
Recap: Languages

A language is a set of words.
A word is a sequence of symbols from an alphabet.
An alphabet is a finite type with decidable equality.

Given languages L₁,L₂ we have the following operations:
L₁ ∪ L₂ : { w | w ∈ L₁ ∨ w ∈ L₂ }
L₁ ∩ L₂ : { w | w ∈ L₁ ∧ w ∈ L₂ }
L₁ ⋅ L₂ : { v ++ w | v ∈ L₁ ∧ w ∈ L₂ }
L₁* : { w₁ ++ w₂ ++ ... ++ wₙ | n ∈ ℕ, w₁,w₂,...,wₙ ∈ L₁ }

This week: automata.
Deterministic automaton over alphabet Sigma consists of:
 - States Q
 - Initial state s
 - Final states F
 - Transition function δ : Q → Sigma → Q
We extend δ to δ_star:
-/
def δ_star : A.Q → Word Sigma → A.Q
| q , [] => q
| q , (x :: w) => δ_star (A.δ q x) w
/-
The language of an automaton A is then
{ w | δ_star A A.s w ∈ A.F }
-/

/-
Example: simple request-response system, after every request
there will be a response before the next request arrives.
-/
inductive SigmaRss : Type
| req | res | wait
open SigmaRss

abbrev A₁ : DFA SigmaRss
:= {
  Q := Fin 3
  s := 0
  F := { 0 }
  δ := λ | 0, req => 1
         | 0, wait => 0
         | 0, res => 2
         | 1, req => 2
         | 1, wait => 1
         | 1, res => 0
         | 2, _ => 2
}

/-
Define the following DFAs:
L₁ : hailing a cab. All words over SigmaABC containing "cab"
L₂ : powers of 4, words over SigmaBin that are a power of 4
L₁ ⋅ L₂ : the concatenation of L₁ and L₂
-/
inductive SigmaCabStates : Type
| q0 -- nothing matched
| q1 -- seen c
| q2 -- seen ca
| q3 -- seen cab
deriving Fintype, DecidableEq
open SigmaCabStates

abbrev L₁ : DFA SigmaABC
:= {
  Q := SigmaCabStates
  s := q0
  F := {q3}
  δ := λ  | q0, c => q1
          | q0, _ => q0
          | q1, c => q1
          | q1, a => q2
          | q1, b => q0
          | q2, c => q1
          | q2, a => q0
          | q2, b => q3
          | q3, _ => q3
}

inductive L2_states : Type
| start | seen1_odd | seen1_even | fail -- fail means more than one 1 or an odd 1
deriving Fintype, DecidableEq
open L2_states

abbrev L₂ : DFA SigmaBin
:= {
  Q := L2_states
  s := start
  F := { seen1_even }
  δ := λ  | start, 1 => seen1_even
          | start, 0 => fail
          | seen1_odd, 1 => fail
          | seen1_odd, 0 => seen1_even
          | seen1_even, 1 => fail
          | seen1_even, 0 => seen1_odd
          | fail, _ => fail
}


/-
A nondeterministic automaton extends a deterministic automaton
by allowing for multiple transitions for the same label. An NFA
consists of:
 - States Q
 - Initial states S
 - Final states F
 - Transition function δ : Q → Sigma → Pow Q (sets over Q)
Intuitively, an NFA follows all the possible transitions in δ
concurrently.

Example: request-response system that first caches all
request and only responds once after the final request
-/
abbrev A₂ : NFA SigmaRss
:= {
  Q := Fin 2
  S := { 0 }
  F := { 1 }
  δ := λ | 0,req => {0,1}
         | 0,wait => {0}
         | 0,res => {}
         | 1,req => {}
         | 1,wait =>{1}
         | 1,res => {}
}

/-
Define the following NFAs:
L₃ : cabs XOR sheep. All words over SigmaABC that contain either "cab" or "baa", but not both
L₄ : All words over SigmaBin where the final 1 is preceded by a 0
L₂ ∪ L₄ : the union of "powers of 4" and "final 1 preceded by 0"
-/
