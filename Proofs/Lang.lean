import Mathlib.Data.Finset.Basic

namespace Lang

variable {Sym : Type}[DecidableEq Sym]

variable (Sigma : Finset Sym)

abbrev Letter : Type
  := { x : Sym // x ∈ Sigma}

abbrev Word : Type
  := List (Letter Sigma)
--   := List Sigma

abbrev Lang : Type
    := Set (Word Sigma)

namespace Examples

def ABC : Finset Char
    := {'a','b','c'}

example : 'a' ∈ ABC := by decide

#check (⟨'a', by decide⟩ : Letter ABC)

abbrev a : Letter ABC := ⟨'a', by decide⟩
abbrev b : Letter ABC := ⟨'b', by decide⟩
abbrev c : Letter ABC := ⟨'c', by decide⟩

abbrev abba : Word ABC
    := [ a , b , b , a ]

abbrev L1 : Lang ABC
| w => w = abba

abbrev L1' : Lang ABC
  := { abba }

abbrev L2 : Lang ABC
  := { [] , [a,b] , [a,a,b,b]}




-- abbrev L1x : Finset (Word ABC)
-- := { abba }

-- abbrev L1y : Lang ABC
-- | w => w ∈ L1x

-- abbrev L1z : Lang ABC
--   := L1x

-- abbrev L1' : Lang ABC
-- | w => w ∈ { abba }



end Examples


end Lang
