/-
COMP2012 (LAC) 2026

Exercise 5

Construct a CFG and PDA for the language of bracket-matched
words.

Don't change anything else in this file!
-/
import Proofs.CFG
import Mathlib.Tactic.DeriveFintype
import Proofs.PDA

namespace ex5

open Lang Sum Cfg CFG Pda PDA

/-
Let SigmaPar be the alphabet of left and right brackets
-/

inductive SigmaPar : Type
| lpar -- "⟨"
| rpar -- "⟩"
deriving Fintype, DecidableEq
open SigmaPar

/-
We consider the language L : Lang Σ of bracket-matched words, words
words in which every ⟨ is “closed” by a ⟩ occurring later in the word. For instance:
• [] ∈ L -- ϵ ∈ L
• [lpar,rpar] ∈ L -- ⟨⟩ ∈ L
• [lpar,lpar,rpar,lpar,rpar,rpar] ∈ L -- ⟨⟩⟨⟩ ∈ L
• [lpar,lpar,rpar] ∉ L   -- ⟨⟨⟩ ∉ L because it has more ⟨’s than ⟩’s,
• [lpar,rpar,rpar] ∉ L   -- ⟨⟩⟩ ∉ L because it has more ⟩’s than ⟨’s,
• [lpar,rpar,rpar,lpar] ∉ L -- ⟨⟩⟩⟨ ∉ L because the second ⟩ occurs before the corresponding ⟨.
-/

/- 1. Define a CFG for the language, you will also need to define an inductive type for the Non-terminals -/
inductive NTPar : Type
| S
deriving Fintype, DecidableEq
open NTPar

abbrev GPar : CFG SigmaPar
:= { NT := NTPar
     S := NTPar.S
     P := {
       (NTPar.S, []),
       (NTPar.S, [inr SigmaPar.lpar, inl NTPar.S, inr SigmaPar.rpar, inl NTPar.S])
     }
}

/- 2. Define a PDA for the language -/
-- You need to define inductive types for the states and the stack alphabet
inductive QPar : Type
| q0 | qf
deriving Fintype, DecidableEq
open QPar

inductive ΓPar : Type
| hash | lmark
deriving Fintype, DecidableEq
open ΓPar

abbrev PPar : PDA SigmaPar
:= { Q := QPar
     Γ := ΓPar
     s := q0
     Z₀ := hash
     F := { qf }
     δ q x z :=
       match q, x, z with
       | q0, some SigmaPar.lpar, z  => { (q0, [lmark, z]) }
       | q0, some SigmaPar.rpar, lmark => { (q0, []) }
       | q0, none, ΓPar.hash => { (qf, [hash]) }
       | _,  _, _ => {}
}

-- 3. Show that ⟨⟩⟨⟩ ∈ L PPar
-- you can either do this by spelling out the sequence of IDs in a comment or by proving
theorem e3 : [SigmaPar.lpar,SigmaPar.lpar, SigmaPar.rpar,SigmaPar.lpar,SigmaPar.rpar, SigmaPar.rpar] ∈ L PPar := by
  sorry
-- in Lean.

/-
⟨⟨⟩⟨⟩⟩ ∈ L PPar because:

(q0, [lpar,lpar,rpar,lpar,rpar,rpar], [hash])
-> (q0, [lpar,rpar,lpar,rpar,rpar], [lmark,hash])
-> (q0, [rpar,lpar,rpar,rpar], [lmark,lmark,hash])
-> (q0, [lpar,rpar,rpar], [lmark,hash])
-> (q0, [rpar,rpar], [lmark,lmark,hash])
-> (q0, [rpar], [lmark,hash])
-> (q0, [], [hash])
-> (qf, [], [hash])

So PPar accepts [lpar,lpar,rpar,lpar,rpar,rpar]
-/
end ex5
