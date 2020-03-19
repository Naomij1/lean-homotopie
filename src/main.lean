--- TODO : 
--  - pointer la chose
--  - retirer des simps et optimiser
--  - finir l'homotopie comme équivalence
--  - interval semiring ?
import topology.basic
import topology.algebra.continuous_functions
import topology.continuous_on
import topology.algebra.ordered
import topology.constructions
import topology.algebra.ordered
import data.set.function
import topology.constructions

import topology.algebra.continuous_functions
import misc

open set topological_space 
open classical


set_option pp.beta true

variable X:Type
variable [topological_space X] 
variable [inhabited X] -- on va pointer les applications en default X


--Définitions par soustype d'un chemin et d'une boucle
/-- Chemin sur un type X -/
def path := {f: I → X // continuous f} 
/-- Boucle sur un type X -/
def loop := {f: I → X // continuous f ∧ f(0)=f(1)} 

--structure point base ?
def foo : I -> ℝ := λ x, 0
def const_0_I : loop ℝ  := ⟨foo, by {split, assume h,  exact continuous_const h, refl}⟩


/-- Homotopie de lacets -/
def loop_homotopy (f : loop X) (g : loop X) : Prop := 
    ∃ (H : I × I -> X),  (∀ t, H(0,t) = f.val(t) ∧  H(1,t)=g.val(t)) ∧ (continuous H) 


/-- Compostition de lacets -/
noncomputable def loop_comp (f : loop X) (g : loop X) : loop X := 
    ⟨λ t, if h:t.val≤0.5 then f.val(⟨2*t.val, twotimes t h⟩) 
    else g.val (⟨ 2*t-1, twotimesminus1 t (em_I t h)⟩), 
    begin 
    sorry
     end⟩



def loop_inv (f : loop X) : loop X := ⟨λ x:I, f.val(⟨1-x.val, oneminus x⟩ ), 
        and.intro (continuous.comp f.property.left oneminuscont) (by { simp [f.property.right], sorry })        ⟩

#check subtype

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
    let H2 : I × I -> X := λ x, H(⟨1-x.1.val, oneminus x.1⟩, x.2),
    use H2,
    split,

    -- fixe les extrémités
    intros,
    split,
    simp *,
    simp [ coe_of_0],
    rw <- (hH.1 t).2,
    congr,
    simp *,
    simp [one_minus_one_coe],
    rw <- (hH.1 t).1,
    congr,

    -- continuité
    apply continuous.comp,
    exact hH.2,
    apply continuous.prod_mk,
    apply continuous_subtype_mk,
    apply continuous.sub,
    apply continuous_const,
    apply continuous.comp,
    exact continuous_subtype_val,
    exact continuous_fst,
    exact continuous_snd,

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


