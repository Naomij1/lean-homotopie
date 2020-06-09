--- TODO : 
--  - retirer des simps et optimiser
--  - retirer les derniers sorry (nommer les hypothèses dans ite)

import topology.basic
import topology.algebra.continuous_functions
import topology.continuous_on
import topology.algebra.ordered
import topology.constructions
import topology.algebra.ordered
import data.set.function
import topology.constructions
import tactic.split_ifs
import tactics

import misc

open set topological_space 
open classical

set_option pp.beta true

/- Typeclass définissant un type pointé -/
class pointed (α : Type) :=
(point : α)

/- Prends un type pointé et lui renvoit son point base-/
def point (α : Type) [s : pointed α] : α :=
@pointed.point α s

-- On considère par la suite un espace topologique X pointé
variable X:Type
variable [topological_space X] 
variable [pointed X] 

-- Dans la suite du fichier, on pointe ℝ en 0
instance : pointed ℝ := pointed.mk 0


--Définitions par soustype d'un chemin et d'une boucle
/-- Chemin sur un type X -/
def path := {f: I → X // continuous f} 
/-- Boucle sur un type X -/
def loop := {f: I → X // continuous f ∧ f(0)=f(1) ∧ f(0) = point X  }

/-- Homotopie de lacets -/
def loop_homotopy (f : loop X) (g : loop X) : Prop := 
    ∃ (H : I × I -> X),  (∀ t, H(0,t) = f.val(t) ∧  H(1,t)=g.val(t)) ∧ (continuous H) 


/-- Compostition de lacets -/
noncomputable def loop_comp : (loop X ) -> (loop X) -> (loop X) := 
    λ f g, ⟨λ t, ite (t.val≤0.5) (f.val(⟨2*t.val, sorry⟩) )
        (g.val (⟨ 2*t.val-1, sorry⟩)), 
    begin 
    split, 
    apply continuous_if,
    rotate,
    apply continuous.comp,
    exact f.property.1,
    apply continuous_subtype_mk,
    apply continuous.mul,
    exact continuous_const,
    apply continuous_subtype_val,
    apply continuous.comp,
    exact g.property.1,
    apply continuous_subtype_mk,
    apply continuous.add,
    apply continuous.mul,
    exact continuous_const,
    apply continuous_subtype_val,
    exact continuous_const,

    split_ifs,
    simp at h_1,
    exfalso,
    sorry,

    split,
    simp,
    rw f.property.2.2,
    conv {to_lhs,
    rw <- g.property.2.2, 
    rw g.property.2.1,},
    congr,
    apply subtype.eq',
    simp,
    ring,

    simp,
    rw f.property.2.2,

    exfalso,
    simp at h,
    linarith,

    exfalso,
    simp at h,
    linarith,

    intros a ha,
    have a_def : a.val=1/2, -- il faut montrer que la frontière = {1/2, -}
    rw frontieronI' at ha,
    exact ha,
    rw a_def,
    rw invtwo,
    simp,
    rw g.property.2.2, 
    rw <- f.property.2.1,
    rw f.property.2.2,
end⟩



/- Lacet inverse -/
def loop_inv : loop X -> loop X := λ f, ⟨λ x:I, f.val(⟨1-x.val, oneminus x⟩ ), 
    begin
    split,
        apply continuous.comp,
        exact f.property.left,
        exact oneminuscont,
    split,
      simp,
      symmetry,
      exact f.property.2.1,
      simp,
      rw <- f.property.2.1,
      exact f.property.2.2,
    end
 ⟩ 


/-- L'homotopie est reflexive -/
theorem loop_homotopy_refl : reflexive (loop_homotopy X) :=
begin
    intro f,
    -- on utilise l'homotopie H(t,s) = f(s)
    let H : I × I -> X := λ x, f.val (x.2), 
    use H,
    split,

    -- l'homotopie vaut f aux extremités
    intros,
    split, 
        simp *,
    
    -- l'homotopie est continue
    apply continuous.comp, -- on déplit la composition
    exact f.property.left, -- f est continue
    exact continuous_snd, -- la projection sur le deuxième élément est continue
end



/-- L'homotopie est symmétrique -/
theorem loop_homotopy_symm : symmetric (loop_homotopy X) :=
begin
    intros f g,
    intro h1, 
    cases h1 with H hH,
    -- on utilise l'homotopie H_2(t,s) = H(1-t,s)
    let H2 : I × I -> X := λ x, H(⟨1-x.1.val, oneminus x.1⟩, x.2),
    use H2,
    split,

     -- l'homotopie vaut g et f aux extremités
    intros,
    split,
    simp *, -- on déplit la définition de H_2
    simp [ coe_of_0],
    rw (hH.1 t).2, -- on réécrit g en H(1,t)
    simp *, -- on déplit la définition de H_2
    simp [one_minus_one_coe],
    rw  (hH.1 t).1, -- on réécrit f en H(0,t)

    -- l'homotopie est continue
    apply continuous.comp, -- on déplit la composition
    exact hH.2, -- H est continue par hypothèse
    apply continuous.prod_mk, -- on déplit le produit
    apply continuous_subtype_mk, -- on déplit le passage au sous-type
    apply continuous.sub, -- on déplit la soustraction
    apply continuous_const, -- une fonction constante est continue
    apply continuous.comp, -- on déplit la composition
    exact continuous_subtype_val, -- le "relèvement" de sous-type est continu
    exact continuous_fst, -- la projection sur le premier élément est continue
    exact continuous_snd, -- la projection sur le deuxième élément est continue

end

/-- L'homotopie est transitive -/
theorem loop_homotopy_trans : transitive (loop_homotopy X) :=
begin
    intros f g h,
    intros h1 h2,
    cases h1 with h1func h1hyp,
    cases h2 with h2func h2hyp,
    -- on utilise l'homotopie H₃(t,s) = H₁(2t,s) si t ≤ 0.5
    --                                  H₂(2t-1,s) sinon
    let H : I × I -> X := λ x, ite (x.1.val≤0.5) (h1func( ⟨ 2*x.1.val, sorry ⟩, x.2))
         (h2func(⟨2*x.1.val-1, sorry⟩, x.2 )),  
    use H,
    split,

    -- l'homotopie vaut f et h aux extremités
    intros,
    split,
    simp *,
    split_ifs, -- on déplit la définition d'une condition
        rw <- (h1hyp.1 t).1, -- soit 0≤1/2
        congr,
        simp [coe_of_0], -- auquel cas les deux arguments sont égaux
    simp at h_1, -- soit 2<0
    exfalso,
    exact not_2_lt_0 h_1, -- auquel cas on obtient une absurdité

    simp *,
    split_ifs, -- on déplit la définition d'une condition
        simp at h_1, -- soit 1<1/2
        exfalso,
        exact not_1_lt_half h_1, -- auquel cas on obtient une absurdité
    rw <- (h2hyp.1 t).2, -- soit 1>0
    congr,
    rw <- oneisone,
    simp,
    ring,

    -- continuité
    simp *,
    apply continuous_if,
    rotate,
    -- partie 1
    apply continuous.comp,
    exact h1hyp.2,
    apply continuous.prod_mk,
    apply continuous_subtype_mk,
    apply continuous.mul,
    exact continuous_const,
    apply continuous.comp,
    exact continuous_subtype_val, -- le "relèvement" de sous-type est continu
    exact continuous_fst, 
    exact continuous_snd,
    -- partie 2
    apply continuous.comp,
    exact h2hyp.2,
    apply continuous.prod_mk,
    apply continuous_subtype_mk,
    apply continuous.sub,
    apply continuous.mul,
    exact continuous_const,
    apply continuous.comp,
    exact continuous_subtype_val, -- le "relèvement" de sous-type est continu
    exact continuous_fst, 
    exact continuous_const,
    exact continuous_snd,
    --frontière
    intros a ha,
    have a_def : a.fst.val=1/2, -- il faut montrer que la frontière = {1/2, -}
    rw frontieronI at ha,
    exact ha,
    rw a_def,
    rw invtwo,
    simp,
    rw (h1hyp.1 a.snd).2, 
    rw (h2hyp.1 a.snd).1,

end

/-- L'homotopie est une relation d'équivalence -/
theorem loop_homotopy_equiv : equivalence (loop_homotopy X) :=
    ⟨ loop_homotopy_refl X, loop_homotopy_symm X, loop_homotopy_trans X⟩

/-- Sétoïde (X, homotopies de X) -/
definition homotopy.setoid : setoid (loop X) := { r := loop_homotopy X, iseqv := loop_homotopy_equiv X}

/-- Ensemble des classes d'homotopie -/
definition homotopy_classes := quotient (homotopy.setoid X)

/-- Réduction à classe d'équivalence près -/
definition reduce_homotopy: (loop X) → homotopy_classes X := quot.mk (loop_homotopy X)

-- notation à améliorer (inférer le type automatiquement)
notation `[` f `|` X `]` := reduce_homotopy X f
