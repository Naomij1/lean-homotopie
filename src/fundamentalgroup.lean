import homotopy

open set topological_space 
open classical

variable X:Type
variable [topological_space X] 
variable [pointed X] 

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
    apply quotient.sound,
    let H : I × I -> X := λ x, H1 (x.1, ⟨ 1-x.2.val, oneminus x.2 ⟩),
    use H,
    split,

    intro t,
    split,
    rw loop_inv,
    simp,
    rw <- (H1_hyp.1 ⟨1-t.val, oneminus t ⟩ ).1,
    rw loop_inv,
    simp,
    rw <- (H1_hyp.1 ⟨1-t.val, oneminus t ⟩ ).2,

    apply continuous.comp,
    exact H1_hyp.2,
    cont 1,
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
    apply quotient.induction_on f_quot,
    intro f,
    let H : I × I -> X := λ x, ite (x.2.val≤(1-x.1.val)/2) (point X) (f.val(⟨(2-x.1.val)*x.2.val-1+x.1.val,sorry ⟩)), 
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
    rw const_x₀,
    simp at h_1,
    exfalso,
      linarith,

    simp *,
    split_ifs,
    simp at h_1,
    exfalso,
      linarith,
    simp at h,
    simp at h_1,
    simp *,

    simp *,
    split_ifs,
    simp at h,
    have ht : t.val=(0:I).val, from antisymm h t.property.1,
    have ht' : t=0, from  subtype.eq ht,
    rw ht',
    rw f.property.2.2,

    simp at h,
    simp *,
    congr,
    apply subtype.eq',
    simp *,
    ring,
    
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
{ mul := homotopy.comp X, 
  mul_assoc := by sorry,
  one := [const_x₀ X | X],
  one_mul := const_comp X,
  mul_one := comp_const X, 
  inv := homotopy.inv X,
  mul_left_inv := by sorry }

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

