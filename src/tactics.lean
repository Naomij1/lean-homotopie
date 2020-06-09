import tactic.interactive
import data.set.intervals.basic
import data.real.basic
import topology.instances.real
import tactic.suggest
import topology.basic
import topology.algebra.continuous_functions
import topology.continuous_on
import topology.algebra.ordered
import topology.constructions
import topology.algebra.ordered
import data.set.function
import topology.constructions
import tactic.split_ifs

open set topological_space 

meta def applyc' (c : name) (cfg : tactic.apply_cfg := {}) : tactic unit :=
  do c' ← tactic.mk_const c, tactic.apply' c' cfg, tactic.skip --tactic.trace $ "" ++ (to_string c) ++ "",tactic.skip

meta def exactc (c : name) : tactic unit :=
  do c ← tactic.mk_const c, tactic.exact c, tactic.skip

meta def finish : list expr -> tactic unit 
  | [] := tactic.skip
  | (h :: hs) :=
   do {
      applyc' ``continuous_const <|>
      applyc' ``continuous_id<|>
      applyc' ``continuous_fst <|>
      applyc' ``continuous_snd <|>
      applyc' ``continuous_subtype_val <|>
      tactic.skip,
      finish hs
   }


meta def elaborate : tactic unit := do
{ applyc' ``continuous.prod_mk  <|> applyc' ``continuous_subtype_mk <|> applyc' ``continuous.sub 
                      <|> applyc' ``continuous.add
                      <|> applyc' ``continuous.comp 
                      <|> applyc' ``continuous.mul}
-- matcher le plut tôt possible avec hyp
meta def elaborate_cont : nat -> tactic unit
| 0 := tactic.skip
| (n+1) := do{
    --trié par priorité
    tactic.any_goals elaborate<|>
    tactic.skip,
    elaborate_cont n}
   -- élabore le plus possible toutes les continuités nécessaires, puis les résout avec finish
meta def cont : nat -> tactic unit 
| n := do
    let depth := n,
     do { `(continuous %%s) ← tactic.target,
      --tactic.trace $ "We are trying to prove that [" ++ (to_string s) ++ "] is continuous ",
      elaborate_cont depth,
      hs ← tactic.get_goals,
      finish hs}
     <|> tactic.fail "Goal is not continuous x"
     


--def f: ℝ × ℝ -> ℝ× ℝ:= λ x, (x.1+x.2,x.2)

--example : continuous f := 
--begin
    --cont 3,
--end