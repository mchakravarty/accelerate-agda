
record Category {A : Set} (e : A) (_·_ : Op₂ A) : Set where
  field
    ident : Identity _≡_ e _·_
    assoc : Associative _≡_ _·_

record MonoFunctor {|A| |B| : Set}
  {eA : |A|} {_·A_ : Op₂ |A|} {eB : |B|} {_·B_ : Op₂ |B|}
  (A : Category eA _·A_) (B : Category eB _·B_)
  (F : |A| → |B|)
  : Set where
  field
    f-ident  : F eA ≡ eB
    f-compat : ∀ {x y} → F (x ·A y) ≡ F x ·B F y

