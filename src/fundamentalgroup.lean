import homotopy

open set topological_space 
open classical

variable X:Type
variable [topological_space X] 
variable [pointed X] 


-- Tell the type class inference system about this equivalence relation.
local attribute [instance] homotopy.setoid


namespace homotopy


/-- La boucle constante égale à point X -/
def const_x₀  : loop X  :=  ⟨λ x, point X, 
        by {split, assume h,  exact continuous_const h, split, refl, refl}⟩

#check [const_x₀ ℝ | ℝ] -- classe d'homotopie de l'application constante sur ℝ 

-- La composition de boucles passe au quotient
lemma congr_comp (f₁ f₂ g₁ g₂ : loop X) : f₁≈f₂ -> g₁≈g₂
        ->  [loop_comp X f₁ g₁ | X] = [loop_comp X f₂ g₂ | X] :=
    begin
    intros h1 h2,
    cases h1 with H1 HH1, 
    cases h2 with H2 HH2, 
    apply quotient.sound, 
    let H : I×I -> X := λ x, ite (x.1.val≤0.5) (H1(⟨2*x.1.val,sorry ⟩,x.2))
          (H2(⟨ 2*x.1.val-1, sorry ⟩ ,x.2)),
    use H,
    sorry,
    end

/-La composition de classes d'homotopies de lacets-/
protected noncomputable definition comp : homotopy_classes X  → homotopy_classes X  → homotopy_classes X  :=
quotient.lift₂ (λ f g : loop X, [loop_comp X f g | X] ) (λ  f₁ f₂ g₁ g₂ h1 h2, congr_comp X f₁ g₁ f₂ g₂ h1 h2)

/-L'inversion passe au quotient-/
lemma congr_inv (f₁ f₂ : loop X) : f₁≈f₂ ->[loop_inv X f₁ | X ] = [loop_inv X f₂ | X] :=
begin
    intro h,
    cases h with H1 H1_hyp,
    apply quotient.sound,
    let H : I × I -> X := λ x, H1 (x.1, ⟨ 1-x.2.val, sorry ⟩),
    use H,
    split,

    intro t,
    split,
    rw loop_inv,
    simp,
    rw <- (H1_hyp.1 ⟨1-t.val, sorry⟩ ).1,
end
/- L'inverse d'une classe d'homotopie de lacets-/
protected definition inv : homotopy_classes X  → homotopy_classes X :=
quotient.lift (λ f : loop X, [loop_inv X f  | X] ) (λ  f₁ f₂ h , congr_inv X f₁  f₂ h)

/- Le groupe fondamental (à remplir) -/
noncomputable instance : group (homotopy_classes X) :=
{ mul := homotopy.comp X, 
  mul_assoc := _,
  one := [const_x₀ X | X] ,
  one_mul := _,
  mul_one := _,
  inv := homotopy.inv X ,
  mul_left_inv := _ }