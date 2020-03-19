-- homotopie de fonctions
def is_homotopy (X : Type) [topological_space X] (f : X -> X) (g : X -> X) (H : X × I -> X) := 
         (∀ t, H(t,0)=f(t)) ∧ (∀ t, H(t,1)=g(t)) ∧ (continuous H) 
         
def const_0: ℝ -> ℝ  := λ x, 0

class contractible_space (X : Type) [topological_space X] :=
    (H : X × I → X)
    (const : X)
    (H_is_homotopy : is_homotopy X (λ x, const) id H)
 
def H : ℝ × I -> ℝ := λ x, (1-x.2.val) * const_0(x.1) + x.2.val * id(x.1)

lemma is_continuous_H : continuous H := 
begin
    rw H,
    rw const_0,
    simp,
    sorry,
end


theorem contractible_R : is_homotopy ℝ const_0 id H := 
begin
    split,
        intros,
        rw [H ,const_0],
        simp,
            left,
            refl,
        split,
            intros,
            rw [H ,const_0],
            simp,
            have h : (1 : I).val = 1, from rfl,
            rw h,
            ring,
        exact is_continuous_H,
end

noncomputable instance : contractible_space ℝ := ⟨H, 0, contractible_R⟩ 


instance : group (homotopy_classes X) :=
{ mul := _,
  mul_assoc := _,
  one := _,
  one_mul := _,
  mul_one := _,
  inv := _,
  mul_left_inv := _ }