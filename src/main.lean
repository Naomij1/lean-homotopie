--- TODO : 
--  - finir la contractilité de ℝ
--  - finir l'homotopie comme équivalence

import topology.basic
import topology.algebra.continuous_functions
import topology.continuous_on
import topology.algebra.ordered
import topology.constructions
import topology.algebra.ordered
import data.set.function

import topology.algebra.continuous_functions
import misc

open set topological_space 
open classical


set_option pp.beta true


-- définitions obsolètes
--def is_path (X : Type) [topological_space X] (f : I  -> X ) := continuous f
--def is_loop (X : Type) [topological_space X] (f : I  -> X ) := f(0)=f(1) ∧ (continuous f)

--Définitions par soustype d'un chemin et d'une boucle
/-- Chemin sur un type X -/
def path (X : Type) [topological_space X] := {f: I → X // continuous f} 
/-- Lacet sur un type X -/
def loop (X : Type) [topological_space X] := {f: I → X // continuous f ∧ f(0)=f(1)} 


def foo : I -> ℝ := λ x, 0
def const_0_I : loop ℝ  := ⟨foo, by {split, assume h,  exact continuous_const h, refl}⟩


/-- Homotopie de lacets -/
def loop_homotopy (X : Type) [topological_space X] (f : loop X) (g : loop X) : Prop := 
    ∃ (H : I × I -> X),  (∀ t, H(0,t) = f.val(t) ∧  H(1,t)=subtype.val g(t)) ∧ (continuous H) 

/-- Composition d'homotopies -/
noncomputable def loop_comp (X : Type) [topological_space X] (f : loop X) (g : loop X) : loop X := 
    ⟨λ t, if t.val≤0.5 then f.val(⟨2*t, sorry⟩) else g.val (⟨ 2*t-1, sorry⟩), sorry⟩

variable X:Type
variable [topological_space X] 

#check (loop_comp ℝ const_0_I const_0_I).val 

/-- L'homotopie est reflexive -/
theorem loop_homotopy_refl : reflexive (loop_homotopy X) :=
begin
    intros,
    assume f,
    let H : I × I -> X := λ x, f.val (x.2), 
    use H,
    split,
        intros,
        split, 
            simp *,
    have f_cont : continuous f.val, from f.property.left,
    apply continuous.comp,
    exact f_cont,
    simp,
    exact continuous_snd,
end

/-- L'homotopie est symmétrique -/
theorem loop_homotopy_symm : symmetric (loop_homotopy X) :=
begin
    assume f g,
    intro h1, 
    cases h1 with H hH,
    let H2 : I × I -> X := λ x, H(⟨1-x.1, sorry⟩, x.2),
    use H2,
    have stupid : ↑(0 : I) = (0 : ℝ ), from rfl,
    have stupid2 : (1 : ℝ) + -↑(0 : I) = (1 : ℝ),  rw stupid, ring,
    split,
        intros,
        split,
        simp *,
        sorry,
        sorry,
        sorry,
        --calc
          --  H (⟨1 + -↑((0, t).fst), _⟩, (0, t).snd) = H (⟨1 + -↑((0, t).fst), _⟩, t) : rfl
            --                            ...        = H (⟨1 + -↑((0, t).fst), _⟩, t)  : rfl
              --                          ...        = H (⟨1 + -↑0, _⟩, t) : rfl
                --                        ...        = H (1, t) : sorry
                  --                      ...        = g.val t : by rw loop_homotopy.property

end

/-- L'homotopie est transitive -/
theorem loop_homotopy_trans : transitive (loop_homotopy X) :=
begin
    assume f g h,
    intros hfg hgh,
    sorry,
end

/-- L'homotopie est une relation d'équivalence -/
theorem loop_homotopy_equiv : equivalence (loop_homotopy X) :=
    ⟨ loop_homotopy_refl X, loop_homotopy_symm X, loop_homotopy_trans X⟩

/-- Sétoïde (X, homotopies de X) -/
definition homotopy.setoid : setoid (loop X) := { r := loop_homotopy X, iseqv := loop_homotopy_equiv X}

-- Tell the type class inference system about this equivalence relation.
local attribute [instance] homotopy.setoid

/-- Ensemble des classes d'homotopie -/
definition homotopy_classes := quotient (homotopy.setoid X)

/-- Réduction à classe d'équivalence près -/
definition reduce_homotopy: (loop X) → homotopy_classes X := quot.mk (loop_homotopy X)

-- notation à améliorer (inférer le type automatiquement)
notation `[` f `|` X `]` := reduce_homotopy X f
#check [const_0_I | ℝ] -- classe d'homotopie de l'application constante sur ℝ 




-- homotopie de fonctions
def is_homotopy (X : Type) [topological_space X] (f : X -> X) (g : X -> X) (H : X × I -> X) := 
         (∀ t, H(t,0)=f(t)) ∧ (∀ t, H(t,1)=g(t)) ∧ (continuous H) 
         
def const_0: ℝ -> ℝ  := λ x, 0

/-- Espace contractible -/
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


/-- ℝ est contractible -/
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
