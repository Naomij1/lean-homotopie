import homotopy

open set topological_space 
open classical

variable X:Type
variable [topological_space X] 
variable [pointed X] 

-- On demande à Lean de β-réduire les expressions automatiquement
set_option pp.beta true

-- Lean infère automatiquement que ≈ fait référence à l'homotopie
local attribute [instance] homotopy.setoid


namespace homotopy


/-- La boucle constante égale à point X -/
def const_x₀  : loop X  :=  ⟨λ x, point X, 
        by {split, assume h,  exact continuous_const h, split, refl, refl}⟩

#check [const_x₀ ℝ | ℝ] -- classe d'homotopie de l'application constante sur ℝ 

/- La composition de boucles passe au quotient -/
lemma congr_comp (f₁ f₂ g₁ g₂ : loop X) : f₁≈f₂ -> g₁≈g₂
        ->  [loop_comp X f₁ g₁ | X] = [loop_comp X f₂ g₂ | X] :=
    begin
  sorry
end

/-La composition de classes d'homotopies de lacets-/
protected noncomputable definition comp : homotopy_classes X  → homotopy_classes X  → homotopy_classes X  :=
quotient.lift₂ (λ f g : loop X, [loop_comp X f g | X] ) (λ  f₁ f₂ g₁ g₂ h1 h2, congr_comp X f₁ g₁ f₂ g₂ h1 h2)


/-L'inversion passe au quotient-/
lemma congr_inv (f₁ f₂ : loop X) : f₁≈f₂ -> [loop_inv X f₁ | X ] = [loop_inv X f₂ | X] :=
begin
    intro h,
    cases h with H1 H1_hyp,
    apply quotient.sound, -- démontrer que les classes d'équivalence sont égales, c'est démontrer 
                          -- qu'il existe une homotopie entre les représentants
    let H : I × I -> X := λ x, H1 (x.1, ⟨ 1-x.2.val, oneminus x.2 ⟩),
    use H,
    split,

    -- l'homotopie vaut \bar{f₁} et \bar{f₂} aux extrémités
    intro t,
    split,
    rw loop_inv,
    simp,
    rw <- (H1_hyp.1 ⟨1-t.val, oneminus t ⟩ ).1, -- le typage dépend de la démonstration
    rw loop_inv,
    simp,
    rw <- (H1_hyp.1 ⟨1-t.val, oneminus t ⟩ ).2,

    -- l'homotopie est continue
    apply continuous.comp,
    exact H1_hyp.2,
    cont 1, -- tactique définie dans le fichier tactics.lean
    apply continuous_subtype_mk,
    apply continuous.sub,
    cont 1,
end
/- L'inverse d'une classe d'homotopie de lacets-/
protected definition inv : homotopy_classes X  → homotopy_classes X :=
quotient.lift (λ f : loop X, [loop_inv X f  | X] ) (λ  f₁ f₂ h , congr_inv X f₁  f₂ h)
set_option trace.check true

/- [c₀⬝f] = [f]-/
theorem const_comp :  ∀ (a : homotopy_classes X), homotopy.comp X [const_x₀ X | X] a = a :=
begin
    intros f_quot,
    apply quotient.induction_on f_quot, -- transforme en un résultat pour un lacet f quelqconque
    intro f, -- soit f un tel lacet
    let H : I × I -> X := λ x, ite (x.2.val≤(1-x.1.val)/2) (point X) (f.val(⟨(2-x.1.val)*x.2.val-1+x.1.val,sorry ⟩)), 
    apply quotient.sound, -- on va montrer que H est une homotopie entre c₀⬝f et f
    use H,
    split,

    -- l'homotopie vaut c₀⬝f et f aux extrémités, découpées en 6 parties par split_ifs
    intro t,
    split,
    rw loop_comp,
    simp,
    split_ifs,
    
    simp *,
    split_ifs,
    simp at h_1, -- partie 1
    rw const_x₀,
    simp at h_1,
    exfalso, -- partie 2
      linarith, -- linarith détecte l'aspect absurde des hypothèses et conclue immédiatement

    simp *, 
    split_ifs,
    simp at h_1,
    exfalso, -- partie 3
      linarith,
    simp at h, -- partie 4
    simp at h_1,
    simp *,

    simp *,
    split_ifs,
    simp at h, -- partie 5
    have ht : t.val=(0:I).val, from antisymm h t.property.1,
    have ht' : t=0, from  subtype.eq ht, -- on "projette" sur le sous-type
    rw ht',
    rw f.property.2.2,

    simp at h, -- partie 6
    simp *,
    congr,
    apply subtype.eq',
    simp *,
    ring,  -- découle des propriétés dans un anneau
    
    -- l'homotopie est continue
    apply continuous_if,
    rotate,
    exact continuous_const,
    apply continuous.comp,
    exact f.property.1,
    apply continuous_subtype_mk,
    apply continuous.add,
    cont 1,
    apply continuous.mul,
    apply continuous.sub,
    exact continuous_const,
    apply continuous.comp,
    apply continuous_subtype_val,
    exact continuous_fst,
    apply continuous.comp,
    cont 0,
    -- valeur à la frontière
    sorry,
end
/- [f⬝c₀] = [f]-/
theorem comp_const :  ∀ (a : homotopy_classes X), homotopy.comp X a [const_x₀ X | X] = a :=
begin
    intros f_quot,
    apply quotient.induction_on f_quot,
    intro f,
    let H : I × I -> X := λ x, ite (x.2.val<=(1+x.1.val)/2) (f.val(⟨(2-x.1.val)*x.2.val,sorry ⟩)) (point X) , 
    apply quotient.sound,
    use H,
    split,

    intro t,
    split,
    rw loop_comp,
    simp,
    split_ifs,
    
    simp *,
    split_ifs,
    simp at h_1,
    simp *,
    simp at h_1,
    have t_geq_0 : t.val>= 0, from t.property.1,
    exfalso,
      linarith,

    simp *,
    split_ifs,
    simp at h_1,
    simp at h,
    exfalso,
      linarith,
    simp at h,
    simp at h_1,
    rw const_x₀,


    simp *,
    split_ifs,
    simp at h,
    congr,
    apply subtype.eq',
    simp *,
    ring,
    simp at h,
    exfalso,
      have t_leq_0 : t.val<= 1, from t.property.2,
      linarith,


    apply continuous_if,
    rotate,
    apply continuous.comp,
    exact f.property.1,
    apply continuous_subtype_mk,
    apply continuous.mul,
    cont 1,
    apply continuous.comp,
    cont 0,
    sorry,
end

/- Le groupe fondamental (à remplir) -/
noncomputable instance : group (homotopy_classes X) :=
{ mul := homotopy.comp X, -- loi de composition interne
  mul_assoc := by sorry, -- associativité
  one := [const_x₀ X | X], -- élément neutre
  one_mul := const_comp X, -- l'élément neutre est neutre à gauche
  mul_one := comp_const X, -- l'élément neutre est neutre à droite
  inv := homotopy.inv X, -- inverse
  mul_left_inv := by sorry } -- l'inverse donne le neutre à gauche 

def trivial  : Prop := ∀ f:loop X, [f|X]=[const_x₀ X|X]

/- π₁(ℝ,0) est trivial-/
example : trivial ℝ :=
begin
  intro,
  apply quotient.sound,
  let H : I×I -> ℝ :=λ x, (1-x.1.val)*f.val(x.2)+x.1.val*(const_x₀ ℝ).val(x.2),
  use H,
  split,
  intro t,
  split,
  simp *,
  simp,
  simp *,
  simp,

  cont 3,
  apply continuous.comp,
  cont 0,
  exact f.property.1,
  cont 0,
end

end homotopy

