module
public import PfaffianBridge

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PDTCovarianceCertificate
open GravityScreening.ResponseClosureCertificate

theorem metric_invariance : ∀ p : Fin 15,
    (adj p).transpose * Matrix.diagonal q + Matrix.diagonal q * adj p=0 := by
  decide +kernel

private def target (p j : Fin 15) : Fin 15 := match p.val,j.val with
  | 0,1 => 5
  | 0,2 => 6
  | 0,3 => 7
  | 0,4 => 8
  | 0,5 => 1
  | 0,6 => 2
  | 0,7 => 3
  | 0,8 => 4
  | 1,0 => 5
  | 1,2 => 9
  | 1,3 => 10
  | 1,4 => 11
  | 1,5 => 0
  | 1,9 => 2
  | 1,10 => 3
  | 1,11 => 4
  | 2,0 => 6
  | 2,1 => 9
  | 2,3 => 12
  | 2,4 => 13
  | 2,6 => 0
  | 2,9 => 1
  | 2,12 => 3
  | 2,13 => 4
  | 3,0 => 7
  | 3,1 => 10
  | 3,2 => 12
  | 3,4 => 14
  | 3,7 => 0
  | 3,10 => 1
  | 3,12 => 2
  | 3,14 => 4
  | 4,0 => 8
  | 4,1 => 11
  | 4,2 => 13
  | 4,3 => 14
  | 4,8 => 0
  | 4,11 => 1
  | 4,13 => 2
  | 4,14 => 3
  | 5,0 => 1
  | 5,1 => 0
  | 5,6 => 9
  | 5,7 => 10
  | 5,8 => 11
  | 5,9 => 6
  | 5,10 => 7
  | 5,11 => 8
  | 6,0 => 2
  | 6,2 => 0
  | 6,5 => 9
  | 6,7 => 12
  | 6,8 => 13
  | 6,9 => 5
  | 6,12 => 7
  | 6,13 => 8
  | 7,0 => 3
  | 7,3 => 0
  | 7,5 => 10
  | 7,6 => 12
  | 7,8 => 14
  | 7,10 => 5
  | 7,12 => 6
  | 7,14 => 8
  | 8,0 => 4
  | 8,4 => 0
  | 8,5 => 11
  | 8,6 => 13
  | 8,7 => 14
  | 8,11 => 5
  | 8,13 => 6
  | 8,14 => 7
  | 9,1 => 2
  | 9,2 => 1
  | 9,5 => 6
  | 9,6 => 5
  | 9,10 => 12
  | 9,11 => 13
  | 9,12 => 10
  | 9,13 => 11
  | 10,1 => 3
  | 10,3 => 1
  | 10,5 => 7
  | 10,7 => 5
  | 10,9 => 12
  | 10,11 => 14
  | 10,12 => 9
  | 10,14 => 11
  | 11,1 => 4
  | 11,4 => 1
  | 11,5 => 8
  | 11,8 => 5
  | 11,9 => 13
  | 11,10 => 14
  | 11,13 => 9
  | 11,14 => 10
  | 12,2 => 3
  | 12,3 => 2
  | 12,6 => 7
  | 12,7 => 6
  | 12,9 => 10
  | 12,10 => 9
  | 12,13 => 14
  | 12,14 => 13
  | 13,2 => 4
  | 13,4 => 2
  | 13,6 => 8
  | 13,8 => 6
  | 13,9 => 11
  | 13,11 => 9
  | 13,12 => 14
  | 13,14 => 12
  | 14,3 => 4
  | 14,4 => 3
  | 14,7 => 8
  | 14,8 => 7
  | 14,10 => 11
  | 14,11 => 10
  | 14,12 => 13
  | 14,13 => 12
  | _,_ => 0

private def sign (p j : Fin 15) : ℤ := match p.val,j.val with
  | 0,1 => -1
  | 0,2 => -1
  | 0,3 => -1
  | 0,4 => -1
  | 0,5 => 1
  | 0,6 => 1
  | 0,7 => 1
  | 0,8 => 1
  | 1,0 => 1
  | 1,2 => -1
  | 1,3 => -1
  | 1,4 => -1
  | 1,5 => -1
  | 1,9 => 1
  | 1,10 => 1
  | 1,11 => 1
  | 2,0 => 1
  | 2,1 => 1
  | 2,3 => -1
  | 2,4 => -1
  | 2,6 => 1
  | 2,9 => 1
  | 2,12 => -1
  | 2,13 => -1
  | 3,0 => 1
  | 3,1 => 1
  | 3,2 => 1
  | 3,4 => -1
  | 3,7 => -1
  | 3,10 => -1
  | 3,12 => -1
  | 3,14 => 1
  | 4,0 => 1
  | 4,1 => 1
  | 4,2 => 1
  | 4,3 => 1
  | 4,8 => 1
  | 4,11 => 1
  | 4,13 => 1
  | 4,14 => 1
  | 5,0 => -1
  | 5,1 => 1
  | 5,6 => -1
  | 5,7 => -1
  | 5,8 => -1
  | 5,9 => 1
  | 5,10 => 1
  | 5,11 => 1
  | 6,0 => -1
  | 6,2 => -1
  | 6,5 => 1
  | 6,7 => -1
  | 6,8 => -1
  | 6,9 => 1
  | 6,12 => -1
  | 6,13 => -1
  | 7,0 => -1
  | 7,3 => 1
  | 7,5 => 1
  | 7,6 => 1
  | 7,8 => -1
  | 7,10 => -1
  | 7,12 => -1
  | 7,14 => 1
  | 8,0 => -1
  | 8,4 => -1
  | 8,5 => 1
  | 8,6 => 1
  | 8,7 => 1
  | 8,11 => 1
  | 8,13 => 1
  | 8,14 => 1
  | 9,1 => -1
  | 9,2 => -1
  | 9,5 => -1
  | 9,6 => -1
  | 9,10 => -1
  | 9,11 => -1
  | 9,12 => -1
  | 9,13 => -1
  | 10,1 => -1
  | 10,3 => 1
  | 10,5 => -1
  | 10,7 => 1
  | 10,9 => 1
  | 10,11 => -1
  | 10,12 => -1
  | 10,14 => 1
  | 11,1 => -1
  | 11,4 => -1
  | 11,5 => -1
  | 11,8 => -1
  | 11,9 => 1
  | 11,10 => 1
  | 11,13 => 1
  | 11,14 => 1
  | 12,2 => 1
  | 12,3 => 1
  | 12,6 => 1
  | 12,7 => 1
  | 12,9 => 1
  | 12,10 => 1
  | 12,13 => 1
  | 12,14 => 1
  | 13,2 => 1
  | 13,4 => -1
  | 13,6 => 1
  | 13,8 => -1
  | 13,9 => 1
  | 13,11 => -1
  | 13,12 => -1
  | 13,14 => 1
  | 14,3 => -1
  | 14,4 => -1
  | 14,7 => -1
  | 14,8 => -1
  | 14,10 => -1
  | 14,11 => -1
  | 14,12 => -1
  | 14,13 => -1
  | _,_ => 0

private theorem column_formula : ∀ p j k : Fin 15,
    adj p k j=(if k=target p j then sign p j else 0) := by
  decide +kernel

private theorem pair_00_00 :
    comm adj00 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan00,add_mul,mul_add]

private theorem pair_00_01 :
    comm adj00 jordan01=(-1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan01,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_00_02 :
    comm adj00 jordan02=(-1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan02,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_00_03 :
    comm adj00 jordan03=(-1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan03,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_00_04 :
    comm adj00 jordan04=(-1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan04,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_00_05 :
    comm adj00 jordan05=(1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan05,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_00_06 :
    comm adj00 jordan06=(1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan06,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_00_07 :
    comm adj00 jordan07=(1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan07,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_00_08 :
    comm adj00 jordan08=(1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan08,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_00_09 :
    comm adj00 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_00_10 :
    comm adj00 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_00_11 :
    comm adj00 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_00_12 :
    comm adj00 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_00_13 :
    comm adj00 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_00_14 :
    comm adj00 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj00,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_01_00 :
    comm adj01 jordan00=(1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan00,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_01_01 :
    comm adj01 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan01,add_mul,mul_add]

private theorem pair_01_02 :
    comm adj01 jordan02=(-1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan02,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_01_03 :
    comm adj01 jordan03=(-1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan03,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_01_04 :
    comm adj01 jordan04=(-1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan04,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_01_05 :
    comm adj01 jordan05=(-1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan05,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_01_06 :
    comm adj01 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_01_07 :
    comm adj01 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_01_08 :
    comm adj01 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_01_09 :
    comm adj01 jordan09=(1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan09,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_01_10 :
    comm adj01 jordan10=(1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan10,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_01_11 :
    comm adj01 jordan11=(1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan11,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_01_12 :
    comm adj01 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_01_13 :
    comm adj01 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_01_14 :
    comm adj01 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj01,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_02_00 :
    comm adj02 jordan00=(1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan00,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_02_01 :
    comm adj02 jordan01=(1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan01,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_02_02 :
    comm adj02 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan02,add_mul,mul_add]

private theorem pair_02_03 :
    comm adj02 jordan03=(-1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan03,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_02_04 :
    comm adj02 jordan04=(-1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan04,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_02_05 :
    comm adj02 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_02_06 :
    comm adj02 jordan06=(1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan06,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_02_07 :
    comm adj02 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_02_08 :
    comm adj02 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_02_09 :
    comm adj02 jordan09=(1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan09,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_02_10 :
    comm adj02 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_02_11 :
    comm adj02 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_02_12 :
    comm adj02 jordan12=(-1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan12,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_02_13 :
    comm adj02 jordan13=(-1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan13,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_02_14 :
    comm adj02 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj02,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_03_00 :
    comm adj03 jordan00=(1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan00,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_03_01 :
    comm adj03 jordan01=(1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan01,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_03_02 :
    comm adj03 jordan02=(1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan02,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_03_03 :
    comm adj03 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan03,add_mul,mul_add]

private theorem pair_03_04 :
    comm adj03 jordan04=(-1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan04,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_03_05 :
    comm adj03 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_03_06 :
    comm adj03 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_03_07 :
    comm adj03 jordan07=(-1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan07,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_03_08 :
    comm adj03 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_03_09 :
    comm adj03 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_03_10 :
    comm adj03 jordan10=(-1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan10,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_03_11 :
    comm adj03 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_03_12 :
    comm adj03 jordan12=(-1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan12,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_03_13 :
    comm adj03 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_03_14 :
    comm adj03 jordan14=(1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj03,jordan14,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_04_00 :
    comm adj04 jordan00=(1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan00,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_04_01 :
    comm adj04 jordan01=(1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan01,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_04_02 :
    comm adj04 jordan02=(1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan02,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_04_03 :
    comm adj04 jordan03=(1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan03,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_04_04 :
    comm adj04 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan04,add_mul,mul_add]

private theorem pair_04_05 :
    comm adj04 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_04_06 :
    comm adj04 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_04_07 :
    comm adj04 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_04_08 :
    comm adj04 jordan08=(1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan08,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_04_09 :
    comm adj04 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_04_10 :
    comm adj04 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_04_11 :
    comm adj04 jordan11=(1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan11,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_04_12 :
    comm adj04 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_04_13 :
    comm adj04 jordan13=(1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan13,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_04_14 :
    comm adj04 jordan14=(1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj04,jordan14,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_05_00 :
    comm adj05 jordan00=(-1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan00,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_05_01 :
    comm adj05 jordan01=(1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan01,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_05_02 :
    comm adj05 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_05_03 :
    comm adj05 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_05_04 :
    comm adj05 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_05_05 :
    comm adj05 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan05,add_mul,mul_add]

private theorem pair_05_06 :
    comm adj05 jordan06=(-1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan06,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_05_07 :
    comm adj05 jordan07=(-1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan07,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_05_08 :
    comm adj05 jordan08=(-1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan08,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_05_09 :
    comm adj05 jordan09=(1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan09,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_05_10 :
    comm adj05 jordan10=(1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan10,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_05_11 :
    comm adj05 jordan11=(1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan11,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_05_12 :
    comm adj05 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_05_13 :
    comm adj05 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_05_14 :
    comm adj05 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj05,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_06_00 :
    comm adj06 jordan00=(-1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan00,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_06_01 :
    comm adj06 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_06_02 :
    comm adj06 jordan02=(-1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan02,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_06_03 :
    comm adj06 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_06_04 :
    comm adj06 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_06_05 :
    comm adj06 jordan05=(1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan05,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_06_06 :
    comm adj06 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan06,add_mul,mul_add]

private theorem pair_06_07 :
    comm adj06 jordan07=(-1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan07,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_06_08 :
    comm adj06 jordan08=(-1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan08,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_06_09 :
    comm adj06 jordan09=(1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan09,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_06_10 :
    comm adj06 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_06_11 :
    comm adj06 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_06_12 :
    comm adj06 jordan12=(-1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan12,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_06_13 :
    comm adj06 jordan13=(-1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan13,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_06_14 :
    comm adj06 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj06,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_07_00 :
    comm adj07 jordan00=(-1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan00,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_07_01 :
    comm adj07 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_07_02 :
    comm adj07 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_07_03 :
    comm adj07 jordan03=(1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan03,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_07_04 :
    comm adj07 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_07_05 :
    comm adj07 jordan05=(1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan05,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_07_06 :
    comm adj07 jordan06=(1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan06,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_07_07 :
    comm adj07 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan07,add_mul,mul_add]

private theorem pair_07_08 :
    comm adj07 jordan08=(-1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan08,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_07_09 :
    comm adj07 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_07_10 :
    comm adj07 jordan10=(-1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan10,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_07_11 :
    comm adj07 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_07_12 :
    comm adj07 jordan12=(-1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan12,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_07_13 :
    comm adj07 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_07_14 :
    comm adj07 jordan14=(1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj07,jordan14,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_08_00 :
    comm adj08 jordan00=(-1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan00,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_08_01 :
    comm adj08 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_08_02 :
    comm adj08 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_08_03 :
    comm adj08 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_08_04 :
    comm adj08 jordan04=(-1 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan04,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_08_05 :
    comm adj08 jordan05=(1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan05,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_08_06 :
    comm adj08 jordan06=(1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan06,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_08_07 :
    comm adj08 jordan07=(1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan07,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_08_08 :
    comm adj08 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan08,add_mul,mul_add]

private theorem pair_08_09 :
    comm adj08 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_08_10 :
    comm adj08 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_08_11 :
    comm adj08 jordan11=(1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan11,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_08_12 :
    comm adj08 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_08_13 :
    comm adj08 jordan13=(1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan13,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_08_14 :
    comm adj08 jordan14=(1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj08,jordan14,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_09_00 :
    comm adj09 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_09_01 :
    comm adj09 jordan01=(-1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan01,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_09_02 :
    comm adj09 jordan02=(-1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan02,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_09_03 :
    comm adj09 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_09_04 :
    comm adj09 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_09_05 :
    comm adj09 jordan05=(-1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan05,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_09_06 :
    comm adj09 jordan06=(-1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan06,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_09_07 :
    comm adj09 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_09_08 :
    comm adj09 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_09_09 :
    comm adj09 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan09,add_mul,mul_add]

private theorem pair_09_10 :
    comm adj09 jordan10=(-1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan10,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_09_11 :
    comm adj09 jordan11=(-1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan11,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_09_12 :
    comm adj09 jordan12=(-1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan12,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_09_13 :
    comm adj09 jordan13=(-1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan13,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_09_14 :
    comm adj09 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj09,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_10_00 :
    comm adj10 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_10_01 :
    comm adj10 jordan01=(-1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan01,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_10_02 :
    comm adj10 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_10_03 :
    comm adj10 jordan03=(1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan03,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_10_04 :
    comm adj10 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_10_05 :
    comm adj10 jordan05=(-1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan05,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_10_06 :
    comm adj10 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_10_07 :
    comm adj10 jordan07=(1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan07,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_10_08 :
    comm adj10 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_10_09 :
    comm adj10 jordan09=(1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan09,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_10_10 :
    comm adj10 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan10,add_mul,mul_add]

private theorem pair_10_11 :
    comm adj10 jordan11=(-1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan11,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_10_12 :
    comm adj10 jordan12=(-1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan12,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_10_13 :
    comm adj10 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_10_14 :
    comm adj10 jordan14=(1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj10,jordan14,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_11_00 :
    comm adj11 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_11_01 :
    comm adj11 jordan01=(-1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan01,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_11_02 :
    comm adj11 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_11_03 :
    comm adj11 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_11_04 :
    comm adj11 jordan04=(-1 : ℤ) • jordan01 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan04,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_11_05 :
    comm adj11 jordan05=(-1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan05,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_11_06 :
    comm adj11 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_11_07 :
    comm adj11 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_11_08 :
    comm adj11 jordan08=(-1 : ℤ) • jordan05 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan08,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_11_09 :
    comm adj11 jordan09=(1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan09,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_11_10 :
    comm adj11 jordan10=(1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan10,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_11_11 :
    comm adj11 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan11,add_mul,mul_add]

private theorem pair_11_12 :
    comm adj11 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_11_13 :
    comm adj11 jordan13=(1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan13,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_11_14 :
    comm adj11 jordan14=(1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj11,jordan14,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_12_00 :
    comm adj12 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_12_01 :
    comm adj12 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_12_02 :
    comm adj12 jordan02=(1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan02,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_12_03 :
    comm adj12 jordan03=(1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan03,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_12_04 :
    comm adj12 jordan04=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_12_05 :
    comm adj12 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_12_06 :
    comm adj12 jordan06=(1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan06,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_12_07 :
    comm adj12 jordan07=(1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan07,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_12_08 :
    comm adj12 jordan08=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_12_09 :
    comm adj12 jordan09=(1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan09,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_12_10 :
    comm adj12 jordan10=(1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan10,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_12_11 :
    comm adj12 jordan11=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_12_12 :
    comm adj12 jordan12=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan12,add_mul,mul_add]

private theorem pair_12_13 :
    comm adj12 jordan13=(1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan13,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_12_14 :
    comm adj12 jordan14=(1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj12,jordan14,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_13_00 :
    comm adj13 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_13_01 :
    comm adj13 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_13_02 :
    comm adj13 jordan02=(1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan02,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_13_03 :
    comm adj13 jordan03=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_13_04 :
    comm adj13 jordan04=(-1 : ℤ) • jordan02 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan04,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_13_05 :
    comm adj13 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_13_06 :
    comm adj13 jordan06=(1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan06,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_13_07 :
    comm adj13 jordan07=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_13_08 :
    comm adj13 jordan08=(-1 : ℤ) • jordan06 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan08,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_13_09 :
    comm adj13 jordan09=(1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan09,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_13_10 :
    comm adj13 jordan10=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_13_11 :
    comm adj13 jordan11=(-1 : ℤ) • jordan09 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan11,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_13_12 :
    comm adj13 jordan12=(-1 : ℤ) • jordan14 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan12,jordan14,add_mul,mul_add]
  all_goals abel

private theorem pair_13_13 :
    comm adj13 jordan13=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan13,add_mul,mul_add]

private theorem pair_13_14 :
    comm adj13 jordan14=(1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj13,jordan14,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_14_00 :
    comm adj14 jordan00=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan00,add_mul,mul_add]
  all_goals abel

private theorem pair_14_01 :
    comm adj14 jordan01=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan01,add_mul,mul_add]
  all_goals abel

private theorem pair_14_02 :
    comm adj14 jordan02=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan02,add_mul,mul_add]
  all_goals abel

private theorem pair_14_03 :
    comm adj14 jordan03=(-1 : ℤ) • jordan04 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan03,jordan04,add_mul,mul_add]
  all_goals abel

private theorem pair_14_04 :
    comm adj14 jordan04=(-1 : ℤ) • jordan03 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan04,jordan03,add_mul,mul_add]
  all_goals abel

private theorem pair_14_05 :
    comm adj14 jordan05=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan05,add_mul,mul_add]
  all_goals abel

private theorem pair_14_06 :
    comm adj14 jordan06=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan06,add_mul,mul_add]
  all_goals abel

private theorem pair_14_07 :
    comm adj14 jordan07=(-1 : ℤ) • jordan08 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan07,jordan08,add_mul,mul_add]
  all_goals abel

private theorem pair_14_08 :
    comm adj14 jordan08=(-1 : ℤ) • jordan07 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan08,jordan07,add_mul,mul_add]
  all_goals abel

private theorem pair_14_09 :
    comm adj14 jordan09=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan09,add_mul,mul_add]
  all_goals abel

private theorem pair_14_10 :
    comm adj14 jordan10=(-1 : ℤ) • jordan11 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan10,jordan11,add_mul,mul_add]
  all_goals abel

private theorem pair_14_11 :
    comm adj14 jordan11=(-1 : ℤ) • jordan10 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan11,jordan10,add_mul,mul_add]
  all_goals abel

private theorem pair_14_12 :
    comm adj14 jordan12=(-1 : ℤ) • jordan13 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan12,jordan13,add_mul,mul_add]
  all_goals abel

private theorem pair_14_13 :
    comm adj14 jordan13=(-1 : ℤ) • jordan12 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan13,jordan12,add_mul,mul_add]
  all_goals abel

private theorem pair_14_14 :
    comm adj14 jordan14=(0 : ℤ) • jordan00 := by
  simp [GravityScreening.ResponseClosureCertificate.comm,adj14,jordan14,add_mul,mul_add]

/-- The actual Jordan matrices transform as the original bivector representation. -/
theorem integral_covariance (p j : Fin 15) :
    comm (adj p) (jordan j)=∑ k : Fin 15, adj p k j • jordan k := by
  have hc : (∑ k : Fin 15, adj p k j • jordan k)=sign p j • jordan (target p j) := by
    simp_rw [column_formula]
    simp
  rw [hc]
  fin_cases p <;> fin_cases j
  · exact pair_00_00
  · exact pair_00_01
  · exact pair_00_02
  · exact pair_00_03
  · exact pair_00_04
  · exact pair_00_05
  · exact pair_00_06
  · exact pair_00_07
  · exact pair_00_08
  · exact pair_00_09
  · exact pair_00_10
  · exact pair_00_11
  · exact pair_00_12
  · exact pair_00_13
  · exact pair_00_14
  · exact pair_01_00
  · exact pair_01_01
  · exact pair_01_02
  · exact pair_01_03
  · exact pair_01_04
  · exact pair_01_05
  · exact pair_01_06
  · exact pair_01_07
  · exact pair_01_08
  · exact pair_01_09
  · exact pair_01_10
  · exact pair_01_11
  · exact pair_01_12
  · exact pair_01_13
  · exact pair_01_14
  · exact pair_02_00
  · exact pair_02_01
  · exact pair_02_02
  · exact pair_02_03
  · exact pair_02_04
  · exact pair_02_05
  · exact pair_02_06
  · exact pair_02_07
  · exact pair_02_08
  · exact pair_02_09
  · exact pair_02_10
  · exact pair_02_11
  · exact pair_02_12
  · exact pair_02_13
  · exact pair_02_14
  · exact pair_03_00
  · exact pair_03_01
  · exact pair_03_02
  · exact pair_03_03
  · exact pair_03_04
  · exact pair_03_05
  · exact pair_03_06
  · exact pair_03_07
  · exact pair_03_08
  · exact pair_03_09
  · exact pair_03_10
  · exact pair_03_11
  · exact pair_03_12
  · exact pair_03_13
  · exact pair_03_14
  · exact pair_04_00
  · exact pair_04_01
  · exact pair_04_02
  · exact pair_04_03
  · exact pair_04_04
  · exact pair_04_05
  · exact pair_04_06
  · exact pair_04_07
  · exact pair_04_08
  · exact pair_04_09
  · exact pair_04_10
  · exact pair_04_11
  · exact pair_04_12
  · exact pair_04_13
  · exact pair_04_14
  · exact pair_05_00
  · exact pair_05_01
  · exact pair_05_02
  · exact pair_05_03
  · exact pair_05_04
  · exact pair_05_05
  · exact pair_05_06
  · exact pair_05_07
  · exact pair_05_08
  · exact pair_05_09
  · exact pair_05_10
  · exact pair_05_11
  · exact pair_05_12
  · exact pair_05_13
  · exact pair_05_14
  · exact pair_06_00
  · exact pair_06_01
  · exact pair_06_02
  · exact pair_06_03
  · exact pair_06_04
  · exact pair_06_05
  · exact pair_06_06
  · exact pair_06_07
  · exact pair_06_08
  · exact pair_06_09
  · exact pair_06_10
  · exact pair_06_11
  · exact pair_06_12
  · exact pair_06_13
  · exact pair_06_14
  · exact pair_07_00
  · exact pair_07_01
  · exact pair_07_02
  · exact pair_07_03
  · exact pair_07_04
  · exact pair_07_05
  · exact pair_07_06
  · exact pair_07_07
  · exact pair_07_08
  · exact pair_07_09
  · exact pair_07_10
  · exact pair_07_11
  · exact pair_07_12
  · exact pair_07_13
  · exact pair_07_14
  · exact pair_08_00
  · exact pair_08_01
  · exact pair_08_02
  · exact pair_08_03
  · exact pair_08_04
  · exact pair_08_05
  · exact pair_08_06
  · exact pair_08_07
  · exact pair_08_08
  · exact pair_08_09
  · exact pair_08_10
  · exact pair_08_11
  · exact pair_08_12
  · exact pair_08_13
  · exact pair_08_14
  · exact pair_09_00
  · exact pair_09_01
  · exact pair_09_02
  · exact pair_09_03
  · exact pair_09_04
  · exact pair_09_05
  · exact pair_09_06
  · exact pair_09_07
  · exact pair_09_08
  · exact pair_09_09
  · exact pair_09_10
  · exact pair_09_11
  · exact pair_09_12
  · exact pair_09_13
  · exact pair_09_14
  · exact pair_10_00
  · exact pair_10_01
  · exact pair_10_02
  · exact pair_10_03
  · exact pair_10_04
  · exact pair_10_05
  · exact pair_10_06
  · exact pair_10_07
  · exact pair_10_08
  · exact pair_10_09
  · exact pair_10_10
  · exact pair_10_11
  · exact pair_10_12
  · exact pair_10_13
  · exact pair_10_14
  · exact pair_11_00
  · exact pair_11_01
  · exact pair_11_02
  · exact pair_11_03
  · exact pair_11_04
  · exact pair_11_05
  · exact pair_11_06
  · exact pair_11_07
  · exact pair_11_08
  · exact pair_11_09
  · exact pair_11_10
  · exact pair_11_11
  · exact pair_11_12
  · exact pair_11_13
  · exact pair_11_14
  · exact pair_12_00
  · exact pair_12_01
  · exact pair_12_02
  · exact pair_12_03
  · exact pair_12_04
  · exact pair_12_05
  · exact pair_12_06
  · exact pair_12_07
  · exact pair_12_08
  · exact pair_12_09
  · exact pair_12_10
  · exact pair_12_11
  · exact pair_12_12
  · exact pair_12_13
  · exact pair_12_14
  · exact pair_13_00
  · exact pair_13_01
  · exact pair_13_02
  · exact pair_13_03
  · exact pair_13_04
  · exact pair_13_05
  · exact pair_13_06
  · exact pair_13_07
  · exact pair_13_08
  · exact pair_13_09
  · exact pair_13_10
  · exact pair_13_11
  · exact pair_13_12
  · exact pair_13_13
  · exact pair_13_14
  · exact pair_14_00
  · exact pair_14_01
  · exact pair_14_02
  · exact pair_14_03
  · exact pair_14_04
  · exact pair_14_05
  · exact pair_14_06
  · exact pair_14_07
  · exact pair_14_08
  · exact pair_14_09
  · exact pair_14_10
  · exact pair_14_11
  · exact pair_14_12
  · exact pair_14_13
  · exact pair_14_14

#print axioms metric_invariance
#print axioms integral_covariance
end PDTCovarianceCertificate
