namespace Kleene

class Star (α : Type u) where
  star : α → α

postfix:max "★" => Star.star

-- define a notation scope
declare_syntax_cat kleene

-- define the notations *inside a scoped block*
scoped notation "∅" => (0 : _)
scoped notation "ε" => (1 : _)
scoped infixl:70 " ⋅ " => HMul.hMul

end Kleene
