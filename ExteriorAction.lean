module
public import StabilizerControls

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTExteriorAction
noncomputable section
open PDTPfaffianCubic GravityScreening.ResponseClosureGeometry
open scoped Matrix
abbrev V6 := Fin 6 → ℝ
abbrev M6 := Matrix (Fin 6) (Fin 6) ℝ
abbrev M15 := Matrix I I ℝ

def ia (p : I) : Fin 6 :=
  if p.val < 5 then 0 else if p.val < 9 then 1 else if p.val < 12 then 2
  else if p.val < 14 then 3 else 4

def ib (p : I) : Fin 6 :=
  if p.val=0 then 1 else if p.val=1 then 2 else if p.val=2 then 3 else
  if p.val=3 then 4 else if p.val=4 then 5 else if p.val=5 then 2 else
  if p.val=6 then 3 else if p.val=7 then 4 else if p.val=8 then 5 else
  if p.val=9 then 3 else if p.val=10 then 4 else if p.val=11 then 5 else
  if p.val=12 then 4 else 5

theorem original_pairs : ∀ p : I, basisPairs p=(ia p,ib p) := by decide +kernel

/-- Actual two-by-two minors in the original bivector coordinate order. -/
def lift (M : M6) : M15 := fun r c =>
  M (ia r) (ia c)*M (ib r) (ib c)-M (ia r) (ib c)*M (ib r) (ia c)

def wedge (u v : V6) : I → ℝ := fun p => u (ia p)*v (ib p)-u (ib p)*v (ia p)

theorem lift_wedge (M : M6) (u v : V6) :
    lift M *ᵥ wedge u v=wedge (M *ᵥ u) (M *ᵥ v) := by
  ext p
  fin_cases p <;> norm_num [lift,wedge,Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ, Fin.succ] <;> ring!

theorem lift_mul (M N : M6) : lift (M*N)=lift M*lift N := by
  ext r c
  have h := congrFun (lift_wedge M (fun i => N i (ia c)) (fun i => N i (ib c))) r
  simpa only [lift, wedge, Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using h.symm

theorem lift_one : lift (1 : M6)=1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [lift,ia,ib,Matrix.one_apply,Fin.ext_iff]

theorem lift_column (M : M6) (p : I) :
    lift M *ᵥ Pi.single p 1=wedge (fun i => M i (ia p)) (fun i => M i (ib p)) := by
  rw [Matrix.mulVec_single_one]
  ext r
  simp only [Matrix.col_apply, lift, wedge]
  ring

#print axioms original_pairs
#print axioms lift_wedge
#print axioms lift_mul
#print axioms lift_one
#print axioms lift_column
end
end PDTExteriorAction
