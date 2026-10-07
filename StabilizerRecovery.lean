module
public import StabilizerTests

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTStabilizerRecovery
noncomputable section
open PDTPfaffianCubic PDTCubicInvariance PDTHessianCovariance PDTStabilizerTests
open scoped Matrix

def decode (A : Mat) (k : I) : ℝ :=
  if k.val=0 then A 1 5 else
  if k.val=1 then -A 0 5 else
  if k.val=2 then A 0 6 else
  if k.val=3 then -A 0 7 else
  if k.val=4 then A 0 8 else
  if k.val=5 then A 0 1 else
  if k.val=6 then -A 0 2 else
  if k.val=7 then A 0 3 else
  if k.val=8 then -A 0 4 else
  if k.val=9 then -A 1 2 else
  if k.val=10 then A 1 3 else
  if k.val=11 then -A 1 4 else
  if k.val=12 then A 2 3 else
  if k.val=13 then -A 2 4 else
  if k.val=14 then -A 3 4 else 0

private theorem entry_00_00 (A : Mat) (h : Certificate A) :
    A 0 0=connection ℝ (decode A) 0 0 := by
  have h0 := h 0
  change 2*A 0 0=0 at h0
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h0

private theorem entry_00_01 (A : Mat) (_h : Certificate A) :
    A 0 1=connection ℝ (decode A) 0 1 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_02 (A : Mat) (_h : Certificate A) :
    A 0 2=connection ℝ (decode A) 0 2 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_03 (A : Mat) (_h : Certificate A) :
    A 0 3=connection ℝ (decode A) 0 3 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_04 (A : Mat) (_h : Certificate A) :
    A 0 4=connection ℝ (decode A) 0 4 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_05 (A : Mat) (_h : Certificate A) :
    A 0 5=connection ℝ (decode A) 0 5 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_06 (A : Mat) (_h : Certificate A) :
    A 0 6=connection ℝ (decode A) 0 6 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_07 (A : Mat) (_h : Certificate A) :
    A 0 7=connection ℝ (decode A) 0 7 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_08 (A : Mat) (_h : Certificate A) :
    A 0 8=connection ℝ (decode A) 0 8 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_00_09 (A : Mat) (h : Certificate A) :
    A 0 9=connection ℝ (decode A) 0 9 := by
  have h9 := h 9
  change A 0 9 + -A 9 0=0 at h9
  have h104 := h 104
  change -A 9 14 + -A 14 9=0 at h104
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h150 := h 150
  change -A 14 0 + -A 14 1 + -A 14 6=0 at h150
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h9 + 1 * h104 + 1 * h120 + 1 * h125 + -1 * h126 + 1 * h150

private theorem entry_00_10 (A : Mat) (h : Certificate A) :
    A 0 10=connection ℝ (decode A) 0 10 := by
  have h10 := h 10
  change A 0 10 + A 10 0=0 at h10
  have h108 := h 108
  change A 10 13 + A 13 10=0 at h108
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h151 := h 151
  change A 13 0 + A 13 1 + A 13 7=0 at h151
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h10 + 1 * h108 + 1 * h121 + 1 * h124 + -1 * h127 + 1 * h151

private theorem entry_00_11 (A : Mat) (h : Certificate A) :
    A 0 11=connection ℝ (decode A) 0 11 := by
  have h11 := h 11
  change A 0 11 + -A 11 0=0 at h11
  have h111 := h 111
  change -A 11 12 + -A 12 11=0 at h111
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h152 := h 152
  change -A 12 0 + -A 12 1 + -A 12 8=0 at h152
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h11 + 1 * h111 + 1 * h122 + 1 * h123 + -1 * h128 + 1 * h152

private theorem entry_00_12 (A : Mat) (h : Certificate A) :
    A 0 12=connection ℝ (decode A) 0 12 := by
  have h12 := h 12
  change A 0 12 + -A 12 0=0 at h12
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h152 := h 152
  change -A 12 0 + -A 12 1 + -A 12 8=0 at h152
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h12 + 1 * h128 + -1 * h152

private theorem entry_00_13 (A : Mat) (h : Certificate A) :
    A 0 13=connection ℝ (decode A) 0 13 := by
  have h13 := h 13
  change A 0 13 + A 13 0=0 at h13
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h151 := h 151
  change A 13 0 + A 13 1 + A 13 7=0 at h151
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h13 + 1 * h127 + -1 * h151

private theorem entry_00_14 (A : Mat) (h : Certificate A) :
    A 0 14=connection ℝ (decode A) 0 14 := by
  have h14 := h 14
  change A 0 14 + -A 14 0=0 at h14
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h150 := h 150
  change -A 14 0 + -A 14 1 + -A 14 6=0 at h150
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h14 + 1 * h126 + -1 * h150

private theorem entry_01_00 (A : Mat) (h : Certificate A) :
    A 1 0=connection ℝ (decode A) 1 0 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h1

private theorem entry_01_01 (A : Mat) (h : Certificate A) :
    A 1 1=connection ℝ (decode A) 1 1 := by
  have h15 := h 15
  change 2*A 1 1=0 at h15
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h15

private theorem entry_01_02 (A : Mat) (_h : Certificate A) :
    A 1 2=connection ℝ (decode A) 1 2 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_01_03 (A : Mat) (_h : Certificate A) :
    A 1 3=connection ℝ (decode A) 1 3 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_01_04 (A : Mat) (_h : Certificate A) :
    A 1 4=connection ℝ (decode A) 1 4 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_01_05 (A : Mat) (_h : Certificate A) :
    A 1 5=connection ℝ (decode A) 1 5 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_01_06 (A : Mat) (h : Certificate A) :
    A 1 6=connection ℝ (decode A) 1 6 := by
  have h20 := h 20
  change A 1 6 + -A 6 1=0 at h20
  have h83 := h 83
  change -A 6 14 + -A 14 6=0 at h83
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h153 := h 153
  change A 14 0 + A 14 1 + A 14 9=0 at h153
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h20 + 1 * h83 + 1 * h120 + -1 * h126 + -1 * h131 + -1 * h153

private theorem entry_01_07 (A : Mat) (h : Certificate A) :
    A 1 7=connection ℝ (decode A) 1 7 := by
  have h21 := h 21
  change A 1 7 + A 7 1=0 at h21
  have h90 := h 90
  change A 7 13 + A 13 7=0 at h90
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h154 := h 154
  change -A 13 0 + -A 13 1 + -A 13 10=0 at h154
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h21 + 1 * h90 + 1 * h121 + -1 * h127 + -1 * h130 + -1 * h154

private theorem entry_01_08 (A : Mat) (h : Certificate A) :
    A 1 8=connection ℝ (decode A) 1 8 := by
  have h22 := h 22
  change A 1 8 + -A 8 1=0 at h22
  have h96 := h 96
  change -A 8 12 + -A 12 8=0 at h96
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h155 := h 155
  change A 12 0 + A 12 1 + A 12 11=0 at h155
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h22 + 1 * h96 + 1 * h122 + -1 * h128 + -1 * h129 + -1 * h155

private theorem entry_01_09 (A : Mat) (h : Certificate A) :
    A 1 9=connection ℝ (decode A) 1 9 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  have h23 := h 23
  change A 1 9 + -A 9 1=0 at h23
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h158 := h 158
  change -A 6 0 + -A 6 1 + -A 6 14 + A 9 0 + A 9 1 + A 9 14=0 at h158
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h6 + 1 * h23 + -1 * h125 + -1 * h131 + 1 * h158

private theorem entry_01_10 (A : Mat) (h : Certificate A) :
    A 1 10=connection ℝ (decode A) 1 10 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  have h24 := h 24
  change A 1 10 + A 10 1=0 at h24
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h157 := h 157
  change A 7 0 + A 7 1 + A 7 13 + -A 10 0 + -A 10 1 + -A 10 13=0 at h157
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h7 + 1 * h24 + -1 * h124 + -1 * h130 + 1 * h157

private theorem entry_01_11 (A : Mat) (h : Certificate A) :
    A 1 11=connection ℝ (decode A) 1 11 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  have h25 := h 25
  change A 1 11 + -A 11 1=0 at h25
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h156 := h 156
  change -A 8 0 + -A 8 1 + -A 8 12 + A 11 0 + A 11 1 + A 11 12=0 at h156
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8 + 1 * h25 + -1 * h123 + -1 * h129 + 1 * h156

private theorem entry_01_12 (A : Mat) (h : Certificate A) :
    A 1 12=connection ℝ (decode A) 1 12 := by
  have h26 := h 26
  change A 1 12 + -A 12 1=0 at h26
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h155 := h 155
  change A 12 0 + A 12 1 + A 12 11=0 at h155
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h26 + -1 * h122 + 1 * h155

private theorem entry_01_13 (A : Mat) (h : Certificate A) :
    A 1 13=connection ℝ (decode A) 1 13 := by
  have h27 := h 27
  change A 1 13 + A 13 1=0 at h27
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h154 := h 154
  change -A 13 0 + -A 13 1 + -A 13 10=0 at h154
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h27 + -1 * h121 + 1 * h154

private theorem entry_01_14 (A : Mat) (h : Certificate A) :
    A 1 14=connection ℝ (decode A) 1 14 := by
  have h28 := h 28
  change A 1 14 + -A 14 1=0 at h28
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h153 := h 153
  change A 14 0 + A 14 1 + A 14 9=0 at h153
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h28 + -1 * h120 + 1 * h153

private theorem entry_02_00 (A : Mat) (h : Certificate A) :
    A 2 0=connection ℝ (decode A) 2 0 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h2

private theorem entry_02_01 (A : Mat) (h : Certificate A) :
    A 2 1=connection ℝ (decode A) 2 1 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16

private theorem entry_02_02 (A : Mat) (h : Certificate A) :
    A 2 2=connection ℝ (decode A) 2 2 := by
  have h29 := h 29
  change -2*A 2 2=0 at h29
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h29

private theorem entry_02_03 (A : Mat) (_h : Certificate A) :
    A 2 3=connection ℝ (decode A) 2 3 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_02_04 (A : Mat) (_h : Certificate A) :
    A 2 4=connection ℝ (decode A) 2 4 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_02_05 (A : Mat) (h : Certificate A) :
    A 2 5=connection ℝ (decode A) 2 5 := by
  have h32 := h 32
  change -A 2 5 + A 5 2=0 at h32
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h159 := h 159
  change A 14 0 + A 14 2 + A 14 9=0 at h159
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h32 + -1 * h74 + -1 * h120 + -1 * h132 + 1 * h137 + 1 * h159

private theorem entry_02_06 (A : Mat) (h : Certificate A) :
    A 2 6=connection ℝ (decode A) 2 6 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  have h33 := h 33
  change -A 2 6 + -A 6 2=0 at h33
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h195 := h 195
  change A 5 1 + A 5 2 + A 5 14 + -A 6 1 + -A 6 2 + -A 6 14=0 at h195
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h19 + -1 * h33 + -1 * h131 + -1 * h137 + 1 * h195

private theorem entry_02_07 (A : Mat) (h : Certificate A) :
    A 2 7=connection ℝ (decode A) 2 7 := by
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h162 := h 162
  change A 11 0 + A 11 2 + A 11 12=0 at h162
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h34 + -1 * h88 + -1 * h123 + 1 * h133 + -1 * h136 + 1 * h162

private theorem entry_02_08 (A : Mat) (h : Certificate A) :
    A 2 8=connection ℝ (decode A) 2 8 := by
  have h35 := h 35
  change -A 2 8 + -A 8 2=0 at h35
  have h94 := h 94
  change -A 8 10 + A 10 8=0 at h94
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h134 := h 134
  change A 10 2 + A 10 8=0 at h134
  have h135 := h 135
  change A 8 2 + A 8 10=0 at h135
  have h163 := h 163
  change -A 10 0 + -A 10 2 + -A 10 13=0 at h163
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h35 + -1 * h94 + -1 * h124 + 1 * h134 + -1 * h135 + 1 * h163

private theorem entry_02_09 (A : Mat) (h : Certificate A) :
    A 2 9=connection ℝ (decode A) 2 9 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  have h36 := h 36
  change -A 2 9 + -A 9 2=0 at h36
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h164 := h 164
  change A 5 0 + A 5 2 + A 5 14 + A 9 0 + A 9 2 + A 9 14=0 at h164
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h5 + -1 * h36 + 1 * h125 + 1 * h137 + -1 * h164

private theorem entry_02_10 (A : Mat) (h : Certificate A) :
    A 2 10=connection ℝ (decode A) 2 10 := by
  have h37 := h 37
  change -A 2 10 + A 10 2=0 at h37
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h163 := h 163
  change -A 10 0 + -A 10 2 + -A 10 13=0 at h163
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h37 + 1 * h124 + -1 * h163

private theorem entry_02_11 (A : Mat) (h : Certificate A) :
    A 2 11=connection ℝ (decode A) 2 11 := by
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h162 := h 162
  change A 11 0 + A 11 2 + A 11 12=0 at h162
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h38 + 1 * h123 + -1 * h162

private theorem entry_02_12 (A : Mat) (h : Certificate A) :
    A 2 12=connection ℝ (decode A) 2 12 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  have h39 := h 39
  change -A 2 12 + -A 12 2=0 at h39
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h161 := h 161
  change -A 7 0 + -A 7 2 + -A 7 11 + A 12 0 + A 12 2 + A 12 11=0 at h161
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h7 + -1 * h39 + 1 * h122 + 1 * h136 + -1 * h161

private theorem entry_02_13 (A : Mat) (h : Certificate A) :
    A 2 13=connection ℝ (decode A) 2 13 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  have h40 := h 40
  change -A 2 13 + A 13 2=0 at h40
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h135 := h 135
  change A 8 2 + A 8 10=0 at h135
  have h160 := h 160
  change A 8 0 + A 8 2 + A 8 10 + -A 13 0 + -A 13 2 + -A 13 10=0 at h160
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8 + -1 * h40 + 1 * h121 + 1 * h135 + -1 * h160

private theorem entry_02_14 (A : Mat) (h : Certificate A) :
    A 2 14=connection ℝ (decode A) 2 14 := by
  have h41 := h 41
  change -A 2 14 + -A 14 2=0 at h41
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h159 := h 159
  change A 14 0 + A 14 2 + A 14 9=0 at h159
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h41 + 1 * h120 + -1 * h159

private theorem entry_03_00 (A : Mat) (h : Certificate A) :
    A 3 0=connection ℝ (decode A) 3 0 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h3

private theorem entry_03_01 (A : Mat) (h : Certificate A) :
    A 3 1=connection ℝ (decode A) 3 1 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h17

private theorem entry_03_02 (A : Mat) (h : Certificate A) :
    A 3 2=connection ℝ (decode A) 3 2 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30

private theorem entry_03_03 (A : Mat) (h : Certificate A) :
    A 3 3=connection ℝ (decode A) 3 3 := by
  have h42 := h 42
  change 2*A 3 3=0 at h42
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h42

private theorem entry_03_04 (A : Mat) (_h : Certificate A) :
    A 3 4=connection ℝ (decode A) 3 4 := by
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]

private theorem entry_03_05 (A : Mat) (h : Certificate A) :
    A 3 5=connection ℝ (decode A) 3 5 := by
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h166 := h 166
  change -A 13 0 + -A 13 3 + -A 13 10=0 at h166
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h44 + 1 * h73 + 1 * h121 + 1 * h138 + 1 * h143 + -1 * h166

private theorem entry_03_06 (A : Mat) (h : Certificate A) :
    A 3 6=connection ℝ (decode A) 3 6 := by
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h168 := h 168
  change A 11 0 + A 11 3 + A 11 12=0 at h168
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h45 + 1 * h80 + 1 * h123 + 1 * h139 + 1 * h142 + -1 * h168

private theorem entry_03_07 (A : Mat) (h : Certificate A) :
    A 3 7=connection ℝ (decode A) 3 7 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  have h46 := h 46
  change A 3 7 + A 7 3=0 at h46
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h196 := h 196
  change -A 5 1 + -A 5 3 + -A 5 13 + A 7 1 + A 7 3 + A 7 13=0 at h196
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h19 + 1 * h46 + 1 * h130 + 1 * h143 + -1 * h196

private theorem entry_03_08 (A : Mat) (h : Certificate A) :
    A 3 8=connection ℝ (decode A) 3 8 := by
  have h47 := h 47
  change A 3 8 + -A 8 3=0 at h47
  have h93 := h 93
  change -A 8 9 + -A 9 8=0 at h93
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h140 := h 140
  change -A 9 3 + -A 9 8=0 at h140
  have h141 := h 141
  change -A 8 3 + -A 8 9=0 at h141
  have h170 := h 170
  change A 9 0 + A 9 3 + A 9 14=0 at h170
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h47 + 1 * h93 + 1 * h125 + -1 * h140 + -1 * h141 + -1 * h170

private theorem entry_03_09 (A : Mat) (h : Certificate A) :
    A 3 9=connection ℝ (decode A) 3 9 := by
  have h48 := h 48
  change A 3 9 + -A 9 3=0 at h48
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h170 := h 170
  change A 9 0 + A 9 3 + A 9 14=0 at h170
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h48 + -1 * h125 + 1 * h170

private theorem entry_03_10 (A : Mat) (h : Certificate A) :
    A 3 10=connection ℝ (decode A) 3 10 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  have h49 := h 49
  change A 3 10 + A 10 3=0 at h49
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h169 := h 169
  change -A 5 0 + -A 5 3 + -A 5 13 + -A 10 0 + -A 10 3 + -A 10 13=0 at h169
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h5 + 1 * h49 + -1 * h124 + -1 * h143 + 1 * h169

private theorem entry_03_11 (A : Mat) (h : Certificate A) :
    A 3 11=connection ℝ (decode A) 3 11 := by
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h168 := h 168
  change A 11 0 + A 11 3 + A 11 12=0 at h168
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h50 + -1 * h123 + 1 * h168

private theorem entry_03_12 (A : Mat) (h : Certificate A) :
    A 3 12=connection ℝ (decode A) 3 12 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  have h51 := h 51
  change A 3 12 + -A 12 3=0 at h51
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h167 := h 167
  change A 6 0 + A 6 3 + A 6 11 + A 12 0 + A 12 3 + A 12 11=0 at h167
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h6 + 1 * h51 + -1 * h122 + -1 * h142 + 1 * h167

private theorem entry_03_13 (A : Mat) (h : Certificate A) :
    A 3 13=connection ℝ (decode A) 3 13 := by
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h166 := h 166
  change -A 13 0 + -A 13 3 + -A 13 10=0 at h166
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h52 + -1 * h121 + 1 * h166

private theorem entry_03_14 (A : Mat) (h : Certificate A) :
    A 3 14=connection ℝ (decode A) 3 14 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  have h53 := h 53
  change A 3 14 + -A 14 3=0 at h53
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h141 := h 141
  change -A 8 3 + -A 8 9=0 at h141
  have h165 := h 165
  change -A 8 0 + -A 8 3 + -A 8 9 + A 14 0 + A 14 3 + A 14 9=0 at h165
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8 + 1 * h53 + -1 * h120 + -1 * h141 + 1 * h165

private theorem entry_04_00 (A : Mat) (h : Certificate A) :
    A 4 0=connection ℝ (decode A) 4 0 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h4

private theorem entry_04_01 (A : Mat) (h : Certificate A) :
    A 4 1=connection ℝ (decode A) 4 1 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h18

private theorem entry_04_02 (A : Mat) (h : Certificate A) :
    A 4 2=connection ℝ (decode A) 4 2 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h31

private theorem entry_04_03 (A : Mat) (h : Certificate A) :
    A 4 3=connection ℝ (decode A) 4 3 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43

private theorem entry_04_04 (A : Mat) (h : Certificate A) :
    A 4 4=connection ℝ (decode A) 4 4 := by
  have h54 := h 54
  change -2*A 4 4=0 at h54
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h54

private theorem entry_04_05 (A : Mat) (h : Certificate A) :
    A 4 5=connection ℝ (decode A) 4 5 := by
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h173 := h 173
  change A 12 0 + A 12 4 + A 12 11=0 at h173
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h55 + -1 * h72 + -1 * h122 + -1 * h144 + 1 * h149 + 1 * h173

private theorem entry_04_06 (A : Mat) (h : Certificate A) :
    A 4 6=connection ℝ (decode A) 4 6 := by
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h175 := h 175
  change -A 10 0 + -A 10 4 + -A 10 13=0 at h175
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h56 + -1 * h79 + -1 * h124 + -1 * h145 + 1 * h148 + 1 * h175

private theorem entry_04_07 (A : Mat) (h : Certificate A) :
    A 4 7=connection ℝ (decode A) 4 7 := by
  have h57 := h 57
  change -A 4 7 + A 7 4=0 at h57
  have h86 := h 86
  change A 7 9 + -A 9 7=0 at h86
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h146 := h 146
  change A 9 4 + A 9 7=0 at h146
  have h147 := h 147
  change A 7 4 + A 7 9=0 at h147
  have h176 := h 176
  change A 9 0 + A 9 4 + A 9 14=0 at h176
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h57 + -1 * h86 + -1 * h125 + -1 * h146 + 1 * h147 + 1 * h176

private theorem entry_04_08 (A : Mat) (h : Certificate A) :
    A 4 8=connection ℝ (decode A) 4 8 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  have h58 := h 58
  change -A 4 8 + -A 8 4=0 at h58
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h197 := h 197
  change A 5 1 + A 5 4 + A 5 12 + -A 8 1 + -A 8 4 + -A 8 12=0 at h197
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h19 + -1 * h58 + -1 * h129 + -1 * h149 + 1 * h197

private theorem entry_04_09 (A : Mat) (h : Certificate A) :
    A 4 9=connection ℝ (decode A) 4 9 := by
  have h59 := h 59
  change -A 4 9 + -A 9 4=0 at h59
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h176 := h 176
  change A 9 0 + A 9 4 + A 9 14=0 at h176
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h59 + 1 * h125 + -1 * h176

private theorem entry_04_10 (A : Mat) (h : Certificate A) :
    A 4 10=connection ℝ (decode A) 4 10 := by
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h175 := h 175
  change -A 10 0 + -A 10 4 + -A 10 13=0 at h175
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h60 + 1 * h124 + -1 * h175

private theorem entry_04_11 (A : Mat) (h : Certificate A) :
    A 4 11=connection ℝ (decode A) 4 11 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  have h61 := h 61
  change -A 4 11 + -A 11 4=0 at h61
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h174 := h 174
  change A 5 0 + A 5 4 + A 5 12 + A 11 0 + A 11 4 + A 11 12=0 at h174
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h5 + -1 * h61 + 1 * h123 + 1 * h149 + -1 * h174

private theorem entry_04_12 (A : Mat) (h : Certificate A) :
    A 4 12=connection ℝ (decode A) 4 12 := by
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h173 := h 173
  change A 12 0 + A 12 4 + A 12 11=0 at h173
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h62 + 1 * h122 + -1 * h173

private theorem entry_04_13 (A : Mat) (h : Certificate A) :
    A 4 13=connection ℝ (decode A) 4 13 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  have h63 := h 63
  change -A 4 13 + A 13 4=0 at h63
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h172 := h 172
  change -A 6 0 + -A 6 4 + -A 6 10 + -A 13 0 + -A 13 4 + -A 13 10=0 at h172
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h6 + -1 * h63 + 1 * h121 + 1 * h148 + -1 * h172

private theorem entry_04_14 (A : Mat) (h : Certificate A) :
    A 4 14=connection ℝ (decode A) 4 14 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  have h64 := h 64
  change -A 4 14 + -A 14 4=0 at h64
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h147 := h 147
  change A 7 4 + A 7 9=0 at h147
  have h171 := h 171
  change A 7 0 + A 7 4 + A 7 9 + A 14 0 + A 14 4 + A 14 9=0 at h171
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h7 + -1 * h64 + 1 * h120 + 1 * h147 + -1 * h171

private theorem entry_05_00 (A : Mat) (h : Certificate A) :
    A 5 0=connection ℝ (decode A) 5 0 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h5

private theorem entry_05_01 (A : Mat) (h : Certificate A) :
    A 5 1=connection ℝ (decode A) 5 1 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h19

private theorem entry_05_02 (A : Mat) (h : Certificate A) :
    A 5 2=connection ℝ (decode A) 5 2 := by
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h159 := h 159
  change A 14 0 + A 14 2 + A 14 9=0 at h159
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h74 + -1 * h120 + -1 * h132 + 1 * h137 + 1 * h159

private theorem entry_05_03 (A : Mat) (h : Certificate A) :
    A 5 3=connection ℝ (decode A) 5 3 := by
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h166 := h 166
  change -A 13 0 + -A 13 3 + -A 13 10=0 at h166
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h73 + -1 * h121 + -1 * h138 + -1 * h143 + 1 * h166

private theorem entry_05_04 (A : Mat) (h : Certificate A) :
    A 5 4=connection ℝ (decode A) 5 4 := by
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h173 := h 173
  change A 12 0 + A 12 4 + A 12 11=0 at h173
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h72 + -1 * h122 + -1 * h144 + 1 * h149 + 1 * h173

private theorem entry_05_05 (A : Mat) (h : Certificate A) :
    A 5 5=connection ℝ (decode A) 5 5 := by
  have h65 := h 65
  change 2*A 5 5=0 at h65
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h65

private theorem entry_05_06 (A : Mat) (h : Certificate A) :
    A 5 6=connection ℝ (decode A) 5 6 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  have h32 := h 32
  change -A 2 5 + A 5 2=0 at h32
  have h41 := h 41
  change -A 2 14 + -A 14 2=0 at h41
  have h66 := h 66
  change A 5 6 + -A 6 5=0 at h66
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h200 := h 200
  change A 2 1 + A 2 5 + A 2 14 + -A 6 1 + -A 6 5 + -A 6 14=0 at h200
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16 + -1 * h32 + -1 * h41 + 1 * h66 + -1 * h74 + 1 * h131 + -1 * h132 + 1 * h137 + -1 * h200

private theorem entry_05_07 (A : Mat) (h : Certificate A) :
    A 5 7=connection ℝ (decode A) 5 7 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h67 := h 67
  change A 5 7 + A 7 5=0 at h67
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h199 := h 199
  change -A 3 1 + -A 3 5 + -A 3 13 + A 7 1 + A 7 5 + A 7 13=0 at h199
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h17 + -1 * h44 + -1 * h52 + 1 * h67 + -1 * h73 + 1 * h130 + -1 * h138 + -1 * h143 + -1 * h199

private theorem entry_05_08 (A : Mat) (h : Certificate A) :
    A 5 8=connection ℝ (decode A) 5 8 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h68 := h 68
  change A 5 8 + -A 8 5=0 at h68
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h198 := h 198
  change A 4 1 + A 4 5 + A 4 12 + -A 8 1 + -A 8 5 + -A 8 12=0 at h198
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h18 + -1 * h55 + -1 * h62 + 1 * h68 + -1 * h72 + 1 * h129 + -1 * h144 + 1 * h149 + -1 * h198

private theorem entry_05_09 (A : Mat) (h : Certificate A) :
    A 5 9=connection ℝ (decode A) 5 9 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  have h32 := h 32
  change -A 2 5 + A 5 2=0 at h32
  have h41 := h 41
  change -A 2 14 + -A 14 2=0 at h41
  have h69 := h 69
  change A 5 9 + -A 9 5=0 at h69
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h179 := h 179
  change A 2 0 + A 2 5 + A 2 14 + A 9 0 + A 9 5 + A 9 14=0 at h179
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h2 + 1 * h32 + 1 * h41 + 1 * h69 + 1 * h74 + -1 * h125 + 1 * h132 + -1 * h137 + 1 * h179

private theorem entry_05_10 (A : Mat) (h : Certificate A) :
    A 5 10=connection ℝ (decode A) 5 10 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h70 := h 70
  change A 5 10 + A 10 5=0 at h70
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h178 := h 178
  change -A 3 0 + -A 3 5 + -A 3 13 + -A 10 0 + -A 10 5 + -A 10 13=0 at h178
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h3 + 1 * h44 + 1 * h52 + 1 * h70 + 1 * h73 + -1 * h124 + 1 * h138 + 1 * h143 + 1 * h178

private theorem entry_05_11 (A : Mat) (h : Certificate A) :
    A 5 11=connection ℝ (decode A) 5 11 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h71 := h 71
  change A 5 11 + -A 11 5=0 at h71
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h177 := h 177
  change A 4 0 + A 4 5 + A 4 12 + A 11 0 + A 11 5 + A 11 12=0 at h177
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h4 + 1 * h55 + 1 * h62 + 1 * h71 + 1 * h72 + -1 * h123 + 1 * h144 + -1 * h149 + 1 * h177

private theorem entry_05_12 (A : Mat) (h : Certificate A) :
    A 5 12=connection ℝ (decode A) 5 12 := by
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h173 := h 173
  change A 12 0 + A 12 4 + A 12 11=0 at h173
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h72 + 1 * h122 + 1 * h144 + -1 * h173

private theorem entry_05_13 (A : Mat) (h : Certificate A) :
    A 5 13=connection ℝ (decode A) 5 13 := by
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h166 := h 166
  change -A 13 0 + -A 13 3 + -A 13 10=0 at h166
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h73 + 1 * h121 + 1 * h138 + -1 * h166

private theorem entry_05_14 (A : Mat) (h : Certificate A) :
    A 5 14=connection ℝ (decode A) 5 14 := by
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h159 := h 159
  change A 14 0 + A 14 2 + A 14 9=0 at h159
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h74 + 1 * h120 + 1 * h132 + -1 * h159

private theorem entry_06_00 (A : Mat) (h : Certificate A) :
    A 6 0=connection ℝ (decode A) 6 0 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h6

private theorem entry_06_01 (A : Mat) (h : Certificate A) :
    A 6 1=connection ℝ (decode A) 6 1 := by
  have h83 := h 83
  change -A 6 14 + -A 14 6=0 at h83
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h153 := h 153
  change A 14 0 + A 14 1 + A 14 9=0 at h153
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h83 + 1 * h120 + -1 * h126 + -1 * h131 + -1 * h153

private theorem entry_06_02 (A : Mat) (h : Certificate A) :
    A 6 2=connection ℝ (decode A) 6 2 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h195 := h 195
  change A 5 1 + A 5 2 + A 5 14 + -A 6 1 + -A 6 2 + -A 6 14=0 at h195
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h19 + 1 * h131 + 1 * h137 + -1 * h195

private theorem entry_06_03 (A : Mat) (h : Certificate A) :
    A 6 3=connection ℝ (decode A) 6 3 := by
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h168 := h 168
  change A 11 0 + A 11 3 + A 11 12=0 at h168
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h80 + 1 * h123 + 1 * h139 + 1 * h142 + -1 * h168

private theorem entry_06_04 (A : Mat) (h : Certificate A) :
    A 6 4=connection ℝ (decode A) 6 4 := by
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h175 := h 175
  change -A 10 0 + -A 10 4 + -A 10 13=0 at h175
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h79 + 1 * h124 + 1 * h145 + -1 * h148 + -1 * h175

private theorem entry_06_05 (A : Mat) (h : Certificate A) :
    A 6 5=connection ℝ (decode A) 6 5 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  have h32 := h 32
  change -A 2 5 + A 5 2=0 at h32
  have h41 := h 41
  change -A 2 14 + -A 14 2=0 at h41
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h200 := h 200
  change A 2 1 + A 2 5 + A 2 14 + -A 6 1 + -A 6 5 + -A 6 14=0 at h200
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16 + -1 * h32 + -1 * h41 + -1 * h74 + 1 * h131 + -1 * h132 + 1 * h137 + -1 * h200

private theorem entry_06_06 (A : Mat) (h : Certificate A) :
    A 6 6=connection ℝ (decode A) 6 6 := by
  have h75 := h 75
  change -2*A 6 6=0 at h75
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h75

private theorem entry_06_07 (A : Mat) (h : Certificate A) :
    A 6 7=connection ℝ (decode A) 6 7 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h76 := h 76
  change -A 6 7 + A 7 6=0 at h76
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h204 := h 204
  change A 7 1 + A 7 6 + A 7 13 + -A 14 1 + -A 14 6 + -A 14 13=0 at h204
  have h208 := h 208
  change -A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13=0 at h208
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30 + 1 * h44 + 1 * h52 + 1 * h73 + -1 * h76 + -1 * h126 + -1 * h130 + -1 * h132 + 1 * h138 + 1 * h143 + 1 * h204 + 1 * h208

private theorem entry_06_08 (A : Mat) (h : Certificate A) :
    A 6 8=connection ℝ (decode A) 6 8 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h77 := h 77
  change -A 6 8 + -A 8 6=0 at h77
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h203 := h 203
  change -A 8 1 + -A 8 6 + -A 8 12 + -A 14 1 + -A 14 6 + -A 14 12=0 at h203
  have h207 := h 207
  change A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12=0 at h207
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h31 + 1 * h55 + 1 * h62 + 1 * h72 + -1 * h77 + -1 * h126 + -1 * h129 + -1 * h132 + 1 * h144 + -1 * h149 + 1 * h203 + 1 * h207

private theorem entry_06_09 (A : Mat) (h : Certificate A) :
    A 6 9=connection ℝ (decode A) 6 9 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  have h20 := h 20
  change A 1 6 + -A 6 1=0 at h20
  have h28 := h 28
  change A 1 14 + -A 14 1=0 at h28
  have h78 := h 78
  change -A 6 9 + -A 9 6=0 at h78
  have h83 := h 83
  change -A 6 14 + -A 14 6=0 at h83
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h182 := h 182
  change -A 1 0 + -A 1 6 + -A 1 14 + A 9 0 + A 9 6 + A 9 14=0 at h182
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h1 + -1 * h20 + -1 * h28 + -1 * h78 + -1 * h83 + 1 * h125 + 1 * h126 + 1 * h131 + -1 * h182

private theorem entry_06_10 (A : Mat) (h : Certificate A) :
    A 6 10=connection ℝ (decode A) 6 10 := by
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h175 := h 175
  change -A 10 0 + -A 10 4 + -A 10 13=0 at h175
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h79 + -1 * h124 + -1 * h145 + 1 * h175

private theorem entry_06_11 (A : Mat) (h : Certificate A) :
    A 6 11=connection ℝ (decode A) 6 11 := by
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h168 := h 168
  change A 11 0 + A 11 3 + A 11 12=0 at h168
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h80 + -1 * h123 + -1 * h139 + 1 * h168

private theorem entry_06_12 (A : Mat) (h : Certificate A) :
    A 6 12=connection ℝ (decode A) 6 12 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h81 := h 81
  change -A 6 12 + -A 12 6=0 at h81
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h181 := h 181
  change A 3 0 + A 3 6 + A 3 11 + A 12 0 + A 12 6 + A 12 11=0 at h181
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h3 + 1 * h45 + 1 * h50 + 1 * h80 + -1 * h81 + 1 * h122 + 1 * h139 + 1 * h142 + -1 * h181

private theorem entry_06_13 (A : Mat) (h : Certificate A) :
    A 6 13=connection ℝ (decode A) 6 13 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h82 := h 82
  change -A 6 13 + A 13 6=0 at h82
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h180 := h 180
  change -A 4 0 + -A 4 6 + -A 4 10 + -A 13 0 + -A 13 6 + -A 13 10=0 at h180
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h4 + 1 * h56 + 1 * h60 + 1 * h79 + -1 * h82 + 1 * h121 + 1 * h145 + -1 * h148 + -1 * h180

private theorem entry_06_14 (A : Mat) (h : Certificate A) :
    A 6 14=connection ℝ (decode A) 6 14 := by
  have h83 := h 83
  change -A 6 14 + -A 14 6=0 at h83
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h153 := h 153
  change A 14 0 + A 14 1 + A 14 9=0 at h153
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h83 + -1 * h120 + 1 * h126 + 1 * h153

private theorem entry_07_00 (A : Mat) (h : Certificate A) :
    A 7 0=connection ℝ (decode A) 7 0 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h7

private theorem entry_07_01 (A : Mat) (h : Certificate A) :
    A 7 1=connection ℝ (decode A) 7 1 := by
  have h90 := h 90
  change A 7 13 + A 13 7=0 at h90
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h154 := h 154
  change -A 13 0 + -A 13 1 + -A 13 10=0 at h154
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h90 + -1 * h121 + 1 * h127 + 1 * h130 + 1 * h154

private theorem entry_07_02 (A : Mat) (h : Certificate A) :
    A 7 2=connection ℝ (decode A) 7 2 := by
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h162 := h 162
  change A 11 0 + A 11 2 + A 11 12=0 at h162
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h88 + -1 * h123 + 1 * h133 + -1 * h136 + 1 * h162

private theorem entry_07_03 (A : Mat) (h : Certificate A) :
    A 7 3=connection ℝ (decode A) 7 3 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h196 := h 196
  change -A 5 1 + -A 5 3 + -A 5 13 + A 7 1 + A 7 3 + A 7 13=0 at h196
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h19 + -1 * h130 + -1 * h143 + 1 * h196

private theorem entry_07_04 (A : Mat) (h : Certificate A) :
    A 7 4=connection ℝ (decode A) 7 4 := by
  have h86 := h 86
  change A 7 9 + -A 9 7=0 at h86
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h146 := h 146
  change A 9 4 + A 9 7=0 at h146
  have h147 := h 147
  change A 7 4 + A 7 9=0 at h147
  have h176 := h 176
  change A 9 0 + A 9 4 + A 9 14=0 at h176
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h86 + -1 * h125 + -1 * h146 + 1 * h147 + 1 * h176

private theorem entry_07_05 (A : Mat) (h : Certificate A) :
    A 7 5=connection ℝ (decode A) 7 5 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h199 := h 199
  change -A 3 1 + -A 3 5 + -A 3 13 + A 7 1 + A 7 5 + A 7 13=0 at h199
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h17 + 1 * h44 + 1 * h52 + 1 * h73 + -1 * h130 + 1 * h138 + 1 * h143 + 1 * h199

private theorem entry_07_06 (A : Mat) (h : Certificate A) :
    A 7 6=connection ℝ (decode A) 7 6 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h204 := h 204
  change A 7 1 + A 7 6 + A 7 13 + -A 14 1 + -A 14 6 + -A 14 13=0 at h204
  have h208 := h 208
  change -A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13=0 at h208
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30 + 1 * h44 + 1 * h52 + 1 * h73 + -1 * h126 + -1 * h130 + -1 * h132 + 1 * h138 + 1 * h143 + 1 * h204 + 1 * h208

private theorem entry_07_07 (A : Mat) (h : Certificate A) :
    A 7 7=connection ℝ (decode A) 7 7 := by
  have h84 := h 84
  change 2*A 7 7=0 at h84
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h84

private theorem entry_07_08 (A : Mat) (h : Certificate A) :
    A 7 8=connection ℝ (decode A) 7 8 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h85 := h 85
  change A 7 8 + -A 8 7=0 at h85
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h206 := h 206
  change -A 8 1 + -A 8 7 + -A 8 12 + A 13 1 + A 13 7 + A 13 12=0 at h206
  have h209 := h 209
  change A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12=0 at h209
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43 + -1 * h55 + -1 * h62 + -1 * h72 + 1 * h85 + 1 * h127 + 1 * h129 + 1 * h138 + -1 * h144 + 1 * h149 + -1 * h206 + -1 * h209

private theorem entry_07_09 (A : Mat) (h : Certificate A) :
    A 7 9=connection ℝ (decode A) 7 9 := by
  have h86 := h 86
  change A 7 9 + -A 9 7=0 at h86
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h146 := h 146
  change A 9 4 + A 9 7=0 at h146
  have h176 := h 176
  change A 9 0 + A 9 4 + A 9 14=0 at h176
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h86 + 1 * h125 + 1 * h146 + -1 * h176

private theorem entry_07_10 (A : Mat) (h : Certificate A) :
    A 7 10=connection ℝ (decode A) 7 10 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  have h21 := h 21
  change A 1 7 + A 7 1=0 at h21
  have h27 := h 27
  change A 1 13 + A 13 1=0 at h27
  have h87 := h 87
  change A 7 10 + A 10 7=0 at h87
  have h90 := h 90
  change A 7 13 + A 13 7=0 at h90
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h185 := h 185
  change A 1 0 + A 1 7 + A 1 13 + -A 10 0 + -A 10 7 + -A 10 13=0 at h185
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h1 + -1 * h21 + -1 * h27 + 1 * h87 + -1 * h90 + -1 * h124 + 1 * h127 + 1 * h130 + 1 * h185

private theorem entry_07_11 (A : Mat) (h : Certificate A) :
    A 7 11=connection ℝ (decode A) 7 11 := by
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h162 := h 162
  change A 11 0 + A 11 2 + A 11 12=0 at h162
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h88 + 1 * h123 + -1 * h133 + -1 * h162

private theorem entry_07_12 (A : Mat) (h : Certificate A) :
    A 7 12=connection ℝ (decode A) 7 12 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h89 := h 89
  change A 7 12 + -A 12 7=0 at h89
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h184 := h 184
  change -A 2 0 + -A 2 7 + -A 2 11 + A 12 0 + A 12 7 + A 12 11=0 at h184
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h2 + -1 * h34 + -1 * h38 + -1 * h88 + 1 * h89 + -1 * h122 + 1 * h133 + -1 * h136 + 1 * h184

private theorem entry_07_13 (A : Mat) (h : Certificate A) :
    A 7 13=connection ℝ (decode A) 7 13 := by
  have h90 := h 90
  change A 7 13 + A 13 7=0 at h90
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h154 := h 154
  change -A 13 0 + -A 13 1 + -A 13 10=0 at h154
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h90 + 1 * h121 + -1 * h127 + -1 * h154

private theorem entry_07_14 (A : Mat) (h : Certificate A) :
    A 7 14=connection ℝ (decode A) 7 14 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  have h57 := h 57
  change -A 4 7 + A 7 4=0 at h57
  have h59 := h 59
  change -A 4 9 + -A 9 4=0 at h59
  have h86 := h 86
  change A 7 9 + -A 9 7=0 at h86
  have h91 := h 91
  change A 7 14 + -A 14 7=0 at h91
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h146 := h 146
  change A 9 4 + A 9 7=0 at h146
  have h147 := h 147
  change A 7 4 + A 7 9=0 at h147
  have h183 := h 183
  change A 4 0 + A 4 7 + A 4 9 + A 14 0 + A 14 7 + A 14 9=0 at h183
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h4 + 1 * h57 + 1 * h59 + 1 * h86 + 1 * h91 + -1 * h120 + 1 * h146 + -1 * h147 + 1 * h183

private theorem entry_08_00 (A : Mat) (h : Certificate A) :
    A 8 0=connection ℝ (decode A) 8 0 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8

private theorem entry_08_01 (A : Mat) (h : Certificate A) :
    A 8 1=connection ℝ (decode A) 8 1 := by
  have h96 := h 96
  change -A 8 12 + -A 12 8=0 at h96
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h155 := h 155
  change A 12 0 + A 12 1 + A 12 11=0 at h155
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h96 + 1 * h122 + -1 * h128 + -1 * h129 + -1 * h155

private theorem entry_08_02 (A : Mat) (h : Certificate A) :
    A 8 2=connection ℝ (decode A) 8 2 := by
  have h94 := h 94
  change -A 8 10 + A 10 8=0 at h94
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h134 := h 134
  change A 10 2 + A 10 8=0 at h134
  have h135 := h 135
  change A 8 2 + A 8 10=0 at h135
  have h163 := h 163
  change -A 10 0 + -A 10 2 + -A 10 13=0 at h163
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h94 + 1 * h124 + -1 * h134 + 1 * h135 + -1 * h163

private theorem entry_08_03 (A : Mat) (h : Certificate A) :
    A 8 3=connection ℝ (decode A) 8 3 := by
  have h93 := h 93
  change -A 8 9 + -A 9 8=0 at h93
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h140 := h 140
  change -A 9 3 + -A 9 8=0 at h140
  have h141 := h 141
  change -A 8 3 + -A 8 9=0 at h141
  have h170 := h 170
  change A 9 0 + A 9 3 + A 9 14=0 at h170
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h93 + 1 * h125 + -1 * h140 + -1 * h141 + -1 * h170

private theorem entry_08_04 (A : Mat) (h : Certificate A) :
    A 8 4=connection ℝ (decode A) 8 4 := by
  have h19 := h 19
  change A 1 5 + A 5 1=0 at h19
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h197 := h 197
  change A 5 1 + A 5 4 + A 5 12 + -A 8 1 + -A 8 4 + -A 8 12=0 at h197
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h19 + 1 * h129 + 1 * h149 + -1 * h197

private theorem entry_08_05 (A : Mat) (h : Certificate A) :
    A 8 5=connection ℝ (decode A) 8 5 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h198 := h 198
  change A 4 1 + A 4 5 + A 4 12 + -A 8 1 + -A 8 5 + -A 8 12=0 at h198
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h18 + -1 * h55 + -1 * h62 + -1 * h72 + 1 * h129 + -1 * h144 + 1 * h149 + -1 * h198

private theorem entry_08_06 (A : Mat) (h : Certificate A) :
    A 8 6=connection ℝ (decode A) 8 6 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h203 := h 203
  change -A 8 1 + -A 8 6 + -A 8 12 + -A 14 1 + -A 14 6 + -A 14 12=0 at h203
  have h207 := h 207
  change A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12=0 at h207
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h31 + -1 * h55 + -1 * h62 + -1 * h72 + 1 * h126 + 1 * h129 + 1 * h132 + -1 * h144 + 1 * h149 + -1 * h203 + -1 * h207

private theorem entry_08_07 (A : Mat) (h : Certificate A) :
    A 8 7=connection ℝ (decode A) 8 7 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h206 := h 206
  change -A 8 1 + -A 8 7 + -A 8 12 + A 13 1 + A 13 7 + A 13 12=0 at h206
  have h209 := h 209
  change A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12=0 at h209
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43 + -1 * h55 + -1 * h62 + -1 * h72 + 1 * h127 + 1 * h129 + 1 * h138 + -1 * h144 + 1 * h149 + -1 * h206 + -1 * h209

private theorem entry_08_08 (A : Mat) (h : Certificate A) :
    A 8 8=connection ℝ (decode A) 8 8 := by
  have h92 := h 92
  change -2*A 8 8=0 at h92
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h92

private theorem entry_08_09 (A : Mat) (h : Certificate A) :
    A 8 9=connection ℝ (decode A) 8 9 := by
  have h93 := h 93
  change -A 8 9 + -A 9 8=0 at h93
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h140 := h 140
  change -A 9 3 + -A 9 8=0 at h140
  have h170 := h 170
  change A 9 0 + A 9 3 + A 9 14=0 at h170
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h93 + -1 * h125 + 1 * h140 + 1 * h170

private theorem entry_08_10 (A : Mat) (h : Certificate A) :
    A 8 10=connection ℝ (decode A) 8 10 := by
  have h94 := h 94
  change -A 8 10 + A 10 8=0 at h94
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h134 := h 134
  change A 10 2 + A 10 8=0 at h134
  have h163 := h 163
  change -A 10 0 + -A 10 2 + -A 10 13=0 at h163
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h94 + -1 * h124 + 1 * h134 + 1 * h163

private theorem entry_08_11 (A : Mat) (h : Certificate A) :
    A 8 11=connection ℝ (decode A) 8 11 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  have h22 := h 22
  change A 1 8 + -A 8 1=0 at h22
  have h26 := h 26
  change A 1 12 + -A 12 1=0 at h26
  have h95 := h 95
  change -A 8 11 + -A 11 8=0 at h95
  have h96 := h 96
  change -A 8 12 + -A 12 8=0 at h96
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h188 := h 188
  change -A 1 0 + -A 1 8 + -A 1 12 + A 11 0 + A 11 8 + A 11 12=0 at h188
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h1 + -1 * h22 + -1 * h26 + -1 * h95 + -1 * h96 + 1 * h123 + 1 * h128 + 1 * h129 + -1 * h188

private theorem entry_08_12 (A : Mat) (h : Certificate A) :
    A 8 12=connection ℝ (decode A) 8 12 := by
  have h96 := h 96
  change -A 8 12 + -A 12 8=0 at h96
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h155 := h 155
  change A 12 0 + A 12 1 + A 12 11=0 at h155
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h96 + -1 * h122 + 1 * h128 + 1 * h155

private theorem entry_08_13 (A : Mat) (h : Certificate A) :
    A 8 13=connection ℝ (decode A) 8 13 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  have h35 := h 35
  change -A 2 8 + -A 8 2=0 at h35
  have h37 := h 37
  change -A 2 10 + A 10 2=0 at h37
  have h94 := h 94
  change -A 8 10 + A 10 8=0 at h94
  have h97 := h 97
  change -A 8 13 + A 13 8=0 at h97
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h134 := h 134
  change A 10 2 + A 10 8=0 at h134
  have h135 := h 135
  change A 8 2 + A 8 10=0 at h135
  have h187 := h 187
  change A 2 0 + A 2 8 + A 2 10 + -A 13 0 + -A 13 8 + -A 13 10=0 at h187
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h2 + -1 * h35 + -1 * h37 + -1 * h94 + -1 * h97 + 1 * h121 + 1 * h134 + -1 * h135 + -1 * h187

private theorem entry_08_14 (A : Mat) (h : Certificate A) :
    A 8 14=connection ℝ (decode A) 8 14 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  have h47 := h 47
  change A 3 8 + -A 8 3=0 at h47
  have h48 := h 48
  change A 3 9 + -A 9 3=0 at h48
  have h93 := h 93
  change -A 8 9 + -A 9 8=0 at h93
  have h98 := h 98
  change -A 8 14 + -A 14 8=0 at h98
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h140 := h 140
  change -A 9 3 + -A 9 8=0 at h140
  have h141 := h 141
  change -A 8 3 + -A 8 9=0 at h141
  have h186 := h 186
  change -A 3 0 + -A 3 8 + -A 3 9 + A 14 0 + A 14 8 + A 14 9=0 at h186
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h3 + -1 * h47 + -1 * h48 + -1 * h93 + -1 * h98 + 1 * h120 + 1 * h140 + 1 * h141 + -1 * h186

private theorem entry_09_00 (A : Mat) (h : Certificate A) :
    A 9 0=connection ℝ (decode A) 9 0 := by
  have h104 := h 104
  change -A 9 14 + -A 14 9=0 at h104
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h150 := h 150
  change -A 14 0 + -A 14 1 + -A 14 6=0 at h150
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h104 + 1 * h120 + 1 * h125 + -1 * h126 + 1 * h150

private theorem entry_09_01 (A : Mat) (h : Certificate A) :
    A 9 1=connection ℝ (decode A) 9 1 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h158 := h 158
  change -A 6 0 + -A 6 1 + -A 6 14 + A 9 0 + A 9 1 + A 9 14=0 at h158
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h6 + -1 * h125 + -1 * h131 + 1 * h158

private theorem entry_09_02 (A : Mat) (h : Certificate A) :
    A 9 2=connection ℝ (decode A) 9 2 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h164 := h 164
  change A 5 0 + A 5 2 + A 5 14 + A 9 0 + A 9 2 + A 9 14=0 at h164
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h5 + -1 * h125 + -1 * h137 + 1 * h164

private theorem entry_09_03 (A : Mat) (h : Certificate A) :
    A 9 3=connection ℝ (decode A) 9 3 := by
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h170 := h 170
  change A 9 0 + A 9 3 + A 9 14=0 at h170
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h125 + 1 * h170

private theorem entry_09_04 (A : Mat) (h : Certificate A) :
    A 9 4=connection ℝ (decode A) 9 4 := by
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h176 := h 176
  change A 9 0 + A 9 4 + A 9 14=0 at h176
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h125 + 1 * h176

private theorem entry_09_05 (A : Mat) (h : Certificate A) :
    A 9 5=connection ℝ (decode A) 9 5 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  have h32 := h 32
  change -A 2 5 + A 5 2=0 at h32
  have h41 := h 41
  change -A 2 14 + -A 14 2=0 at h41
  have h74 := h 74
  change A 5 14 + -A 14 5=0 at h74
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h137 := h 137
  change A 5 2 + A 5 14=0 at h137
  have h179 := h 179
  change A 2 0 + A 2 5 + A 2 14 + A 9 0 + A 9 5 + A 9 14=0 at h179
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h2 + 1 * h32 + 1 * h41 + 1 * h74 + -1 * h125 + 1 * h132 + -1 * h137 + 1 * h179

private theorem entry_09_06 (A : Mat) (h : Certificate A) :
    A 9 6=connection ℝ (decode A) 9 6 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  have h20 := h 20
  change A 1 6 + -A 6 1=0 at h20
  have h28 := h 28
  change A 1 14 + -A 14 1=0 at h28
  have h83 := h 83
  change -A 6 14 + -A 14 6=0 at h83
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h131 := h 131
  change -A 6 1 + -A 6 14=0 at h131
  have h182 := h 182
  change -A 1 0 + -A 1 6 + -A 1 14 + A 9 0 + A 9 6 + A 9 14=0 at h182
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h1 + 1 * h20 + 1 * h28 + 1 * h83 + -1 * h125 + -1 * h126 + -1 * h131 + 1 * h182

private theorem entry_09_07 (A : Mat) (h : Certificate A) :
    A 9 7=connection ℝ (decode A) 9 7 := by
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h146 := h 146
  change A 9 4 + A 9 7=0 at h146
  have h176 := h 176
  change A 9 0 + A 9 4 + A 9 14=0 at h176
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h125 + 1 * h146 + -1 * h176

private theorem entry_09_08 (A : Mat) (h : Certificate A) :
    A 9 8=connection ℝ (decode A) 9 8 := by
  have h125 := h 125
  change A 9 0 + A 9 14=0 at h125
  have h140 := h 140
  change -A 9 3 + -A 9 8=0 at h140
  have h170 := h 170
  change A 9 0 + A 9 3 + A 9 14=0 at h170
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h125 + -1 * h140 + -1 * h170

private theorem entry_09_09 (A : Mat) (h : Certificate A) :
    A 9 9=connection ℝ (decode A) 9 9 := by
  have h99 := h 99
  change -2*A 9 9=0 at h99
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h99

private theorem entry_09_10 (A : Mat) (h : Certificate A) :
    A 9 10=connection ℝ (decode A) 9 10 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h100 := h 100
  change -A 9 10 + A 10 9=0 at h100
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h192 := h 192
  change -A 10 0 + -A 10 9 + -A 10 13 + A 14 0 + A 14 9 + A 14 13=0 at h192
  have h208 := h 208
  change -A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13=0 at h208
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30 + 1 * h44 + 1 * h52 + 1 * h73 + -1 * h100 + 1 * h120 + 1 * h124 + -1 * h132 + 1 * h138 + 1 * h143 + -1 * h192 + 1 * h208

private theorem entry_09_11 (A : Mat) (h : Certificate A) :
    A 9 11=connection ℝ (decode A) 9 11 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h101 := h 101
  change -A 9 11 + -A 11 9=0 at h101
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h191 := h 191
  change A 11 0 + A 11 9 + A 11 12 + A 14 0 + A 14 9 + A 14 12=0 at h191
  have h207 := h 207
  change A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12=0 at h207
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h31 + 1 * h55 + 1 * h62 + 1 * h72 + -1 * h101 + 1 * h120 + 1 * h123 + -1 * h132 + 1 * h144 + -1 * h149 + -1 * h191 + 1 * h207

private theorem entry_09_12 (A : Mat) (h : Certificate A) :
    A 9 12=connection ℝ (decode A) 9 12 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h102 := h 102
  change -A 9 12 + -A 12 9=0 at h102
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h190 := h 190
  change A 12 0 + A 12 9 + A 12 11 + A 14 0 + A 14 9 + A 14 11=0 at h190
  have h202 := h 202
  change A 3 1 + A 3 6 + A 3 11 + -A 14 1 + -A 14 6 + -A 14 11=0 at h202
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h17 + 1 * h45 + 1 * h50 + 1 * h80 + -1 * h102 + 1 * h120 + 1 * h122 + 1 * h126 + 1 * h139 + 1 * h142 + -1 * h190 + -1 * h202

private theorem entry_09_13 (A : Mat) (h : Certificate A) :
    A 9 13=connection ℝ (decode A) 9 13 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h103 := h 103
  change -A 9 13 + A 13 9=0 at h103
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h189 := h 189
  change -A 13 0 + -A 13 9 + -A 13 10 + A 14 0 + A 14 9 + A 14 10=0 at h189
  have h201 := h 201
  change -A 4 1 + -A 4 6 + -A 4 10 + -A 14 1 + -A 14 6 + -A 14 10=0 at h201
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h18 + 1 * h56 + 1 * h60 + 1 * h79 + -1 * h103 + 1 * h120 + 1 * h121 + 1 * h126 + 1 * h145 + -1 * h148 + -1 * h189 + -1 * h201

private theorem entry_09_14 (A : Mat) (h : Certificate A) :
    A 9 14=connection ℝ (decode A) 9 14 := by
  have h104 := h 104
  change -A 9 14 + -A 14 9=0 at h104
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h150 := h 150
  change -A 14 0 + -A 14 1 + -A 14 6=0 at h150
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h104 + -1 * h120 + 1 * h126 + -1 * h150

private theorem entry_10_00 (A : Mat) (h : Certificate A) :
    A 10 0=connection ℝ (decode A) 10 0 := by
  have h108 := h 108
  change A 10 13 + A 13 10=0 at h108
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h151 := h 151
  change A 13 0 + A 13 1 + A 13 7=0 at h151
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h108 + -1 * h121 + -1 * h124 + 1 * h127 + -1 * h151

private theorem entry_10_01 (A : Mat) (h : Certificate A) :
    A 10 1=connection ℝ (decode A) 10 1 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h157 := h 157
  change A 7 0 + A 7 1 + A 7 13 + -A 10 0 + -A 10 1 + -A 10 13=0 at h157
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h7 + 1 * h124 + 1 * h130 + -1 * h157

private theorem entry_10_02 (A : Mat) (h : Certificate A) :
    A 10 2=connection ℝ (decode A) 10 2 := by
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h163 := h 163
  change -A 10 0 + -A 10 2 + -A 10 13=0 at h163
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h124 + -1 * h163

private theorem entry_10_03 (A : Mat) (h : Certificate A) :
    A 10 3=connection ℝ (decode A) 10 3 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h169 := h 169
  change -A 5 0 + -A 5 3 + -A 5 13 + -A 10 0 + -A 10 3 + -A 10 13=0 at h169
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h5 + 1 * h124 + 1 * h143 + -1 * h169

private theorem entry_10_04 (A : Mat) (h : Certificate A) :
    A 10 4=connection ℝ (decode A) 10 4 := by
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h175 := h 175
  change -A 10 0 + -A 10 4 + -A 10 13=0 at h175
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h124 + -1 * h175

private theorem entry_10_05 (A : Mat) (h : Certificate A) :
    A 10 5=connection ℝ (decode A) 10 5 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h178 := h 178
  change -A 3 0 + -A 3 5 + -A 3 13 + -A 10 0 + -A 10 5 + -A 10 13=0 at h178
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h3 + -1 * h44 + -1 * h52 + -1 * h73 + 1 * h124 + -1 * h138 + -1 * h143 + -1 * h178

private theorem entry_10_06 (A : Mat) (h : Certificate A) :
    A 10 6=connection ℝ (decode A) 10 6 := by
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h175 := h 175
  change -A 10 0 + -A 10 4 + -A 10 13=0 at h175
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h124 + -1 * h145 + 1 * h175

private theorem entry_10_07 (A : Mat) (h : Certificate A) :
    A 10 7=connection ℝ (decode A) 10 7 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  have h21 := h 21
  change A 1 7 + A 7 1=0 at h21
  have h27 := h 27
  change A 1 13 + A 13 1=0 at h27
  have h90 := h 90
  change A 7 13 + A 13 7=0 at h90
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h130 := h 130
  change A 7 1 + A 7 13=0 at h130
  have h185 := h 185
  change A 1 0 + A 1 7 + A 1 13 + -A 10 0 + -A 10 7 + -A 10 13=0 at h185
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h1 + 1 * h21 + 1 * h27 + 1 * h90 + 1 * h124 + -1 * h127 + -1 * h130 + -1 * h185

private theorem entry_10_08 (A : Mat) (h : Certificate A) :
    A 10 8=connection ℝ (decode A) 10 8 := by
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h134 := h 134
  change A 10 2 + A 10 8=0 at h134
  have h163 := h 163
  change -A 10 0 + -A 10 2 + -A 10 13=0 at h163
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h124 + 1 * h134 + 1 * h163

private theorem entry_10_09 (A : Mat) (h : Certificate A) :
    A 10 9=connection ℝ (decode A) 10 9 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h124 := h 124
  change -A 10 0 + -A 10 13=0 at h124
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h192 := h 192
  change -A 10 0 + -A 10 9 + -A 10 13 + A 14 0 + A 14 9 + A 14 13=0 at h192
  have h208 := h 208
  change -A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13=0 at h208
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30 + 1 * h44 + 1 * h52 + 1 * h73 + 1 * h120 + 1 * h124 + -1 * h132 + 1 * h138 + 1 * h143 + -1 * h192 + 1 * h208

private theorem entry_10_10 (A : Mat) (h : Certificate A) :
    A 10 10=connection ℝ (decode A) 10 10 := by
  have h105 := h 105
  change 2*A 10 10=0 at h105
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h105

private theorem entry_10_11 (A : Mat) (h : Certificate A) :
    A 10 11=connection ℝ (decode A) 10 11 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h106 := h 106
  change A 10 11 + -A 11 10=0 at h106
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h194 := h 194
  change A 11 0 + A 11 10 + A 11 12 + -A 13 0 + -A 13 10 + -A 13 12=0 at h194
  have h209 := h 209
  change A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12=0 at h209
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43 + -1 * h55 + -1 * h62 + -1 * h72 + 1 * h106 + -1 * h121 + -1 * h123 + 1 * h138 + -1 * h144 + 1 * h149 + 1 * h194 + -1 * h209

private theorem entry_10_12 (A : Mat) (h : Certificate A) :
    A 10 12=connection ℝ (decode A) 10 12 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h107 := h 107
  change A 10 12 + -A 12 10=0 at h107
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h193 := h 193
  change A 12 0 + A 12 10 + A 12 11 + -A 13 0 + -A 13 10 + -A 13 11=0 at h193
  have h205 := h 205
  change -A 2 1 + -A 2 7 + -A 2 11 + A 13 1 + A 13 7 + A 13 11=0 at h205
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16 + -1 * h34 + -1 * h38 + -1 * h88 + 1 * h107 + -1 * h121 + -1 * h122 + -1 * h127 + 1 * h133 + -1 * h136 + 1 * h193 + 1 * h205

private theorem entry_10_13 (A : Mat) (h : Certificate A) :
    A 10 13=connection ℝ (decode A) 10 13 := by
  have h108 := h 108
  change A 10 13 + A 13 10=0 at h108
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h151 := h 151
  change A 13 0 + A 13 1 + A 13 7=0 at h151
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h108 + 1 * h121 + -1 * h127 + 1 * h151

private theorem entry_10_14 (A : Mat) (h : Certificate A) :
    A 10 14=connection ℝ (decode A) 10 14 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h109 := h 109
  change A 10 14 + -A 14 10=0 at h109
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h201 := h 201
  change -A 4 1 + -A 4 6 + -A 4 10 + -A 14 1 + -A 14 6 + -A 14 10=0 at h201
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h18 + 1 * h56 + 1 * h60 + 1 * h79 + 1 * h109 + 1 * h126 + 1 * h145 + -1 * h148 + -1 * h201

private theorem entry_11_00 (A : Mat) (h : Certificate A) :
    A 11 0=connection ℝ (decode A) 11 0 := by
  have h111 := h 111
  change -A 11 12 + -A 12 11=0 at h111
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h152 := h 152
  change -A 12 0 + -A 12 1 + -A 12 8=0 at h152
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h111 + 1 * h122 + 1 * h123 + -1 * h128 + 1 * h152

private theorem entry_11_01 (A : Mat) (h : Certificate A) :
    A 11 1=connection ℝ (decode A) 11 1 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h156 := h 156
  change -A 8 0 + -A 8 1 + -A 8 12 + A 11 0 + A 11 1 + A 11 12=0 at h156
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8 + -1 * h123 + -1 * h129 + 1 * h156

private theorem entry_11_02 (A : Mat) (h : Certificate A) :
    A 11 2=connection ℝ (decode A) 11 2 := by
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h162 := h 162
  change A 11 0 + A 11 2 + A 11 12=0 at h162
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h123 + 1 * h162

private theorem entry_11_03 (A : Mat) (h : Certificate A) :
    A 11 3=connection ℝ (decode A) 11 3 := by
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h168 := h 168
  change A 11 0 + A 11 3 + A 11 12=0 at h168
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h123 + 1 * h168

private theorem entry_11_04 (A : Mat) (h : Certificate A) :
    A 11 4=connection ℝ (decode A) 11 4 := by
  have h5 := h 5
  change A 0 5 + A 5 0=0 at h5
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h174 := h 174
  change A 5 0 + A 5 4 + A 5 12 + A 11 0 + A 11 4 + A 11 12=0 at h174
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h5 + -1 * h123 + -1 * h149 + 1 * h174

private theorem entry_11_05 (A : Mat) (h : Certificate A) :
    A 11 5=connection ℝ (decode A) 11 5 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h177 := h 177
  change A 4 0 + A 4 5 + A 4 12 + A 11 0 + A 11 5 + A 11 12=0 at h177
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h4 + 1 * h55 + 1 * h62 + 1 * h72 + -1 * h123 + 1 * h144 + -1 * h149 + 1 * h177

private theorem entry_11_06 (A : Mat) (h : Certificate A) :
    A 11 6=connection ℝ (decode A) 11 6 := by
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h168 := h 168
  change A 11 0 + A 11 3 + A 11 12=0 at h168
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h123 + 1 * h139 + -1 * h168

private theorem entry_11_07 (A : Mat) (h : Certificate A) :
    A 11 7=connection ℝ (decode A) 11 7 := by
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h162 := h 162
  change A 11 0 + A 11 2 + A 11 12=0 at h162
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h123 + -1 * h133 + -1 * h162

private theorem entry_11_08 (A : Mat) (h : Certificate A) :
    A 11 8=connection ℝ (decode A) 11 8 := by
  have h1 := h 1
  change A 0 1 + A 1 0=0 at h1
  have h22 := h 22
  change A 1 8 + -A 8 1=0 at h22
  have h26 := h 26
  change A 1 12 + -A 12 1=0 at h26
  have h96 := h 96
  change -A 8 12 + -A 12 8=0 at h96
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h129 := h 129
  change -A 8 1 + -A 8 12=0 at h129
  have h188 := h 188
  change -A 1 0 + -A 1 8 + -A 1 12 + A 11 0 + A 11 8 + A 11 12=0 at h188
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h1 + 1 * h22 + 1 * h26 + 1 * h96 + -1 * h123 + -1 * h128 + -1 * h129 + 1 * h188

private theorem entry_11_09 (A : Mat) (h : Certificate A) :
    A 11 9=connection ℝ (decode A) 11 9 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h191 := h 191
  change A 11 0 + A 11 9 + A 11 12 + A 14 0 + A 14 9 + A 14 12=0 at h191
  have h207 := h 207
  change A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12=0 at h207
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h31 + -1 * h55 + -1 * h62 + -1 * h72 + -1 * h120 + -1 * h123 + 1 * h132 + -1 * h144 + 1 * h149 + 1 * h191 + -1 * h207

private theorem entry_11_10 (A : Mat) (h : Certificate A) :
    A 11 10=connection ℝ (decode A) 11 10 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h123 := h 123
  change A 11 0 + A 11 12=0 at h123
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h194 := h 194
  change A 11 0 + A 11 10 + A 11 12 + -A 13 0 + -A 13 10 + -A 13 12=0 at h194
  have h209 := h 209
  change A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12=0 at h209
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43 + -1 * h55 + -1 * h62 + -1 * h72 + -1 * h121 + -1 * h123 + 1 * h138 + -1 * h144 + 1 * h149 + 1 * h194 + -1 * h209

private theorem entry_11_11 (A : Mat) (h : Certificate A) :
    A 11 11=connection ℝ (decode A) 11 11 := by
  have h110 := h 110
  change -2*A 11 11=0 at h110
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h110

private theorem entry_11_12 (A : Mat) (h : Certificate A) :
    A 11 12=connection ℝ (decode A) 11 12 := by
  have h111 := h 111
  change -A 11 12 + -A 12 11=0 at h111
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h152 := h 152
  change -A 12 0 + -A 12 1 + -A 12 8=0 at h152
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h111 + -1 * h122 + 1 * h128 + -1 * h152

private theorem entry_11_13 (A : Mat) (h : Certificate A) :
    A 11 13=connection ℝ (decode A) 11 13 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h112 := h 112
  change -A 11 13 + A 13 11=0 at h112
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h205 := h 205
  change -A 2 1 + -A 2 7 + -A 2 11 + A 13 1 + A 13 7 + A 13 11=0 at h205
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16 + -1 * h34 + -1 * h38 + -1 * h88 + -1 * h112 + -1 * h127 + 1 * h133 + -1 * h136 + 1 * h205

private theorem entry_11_14 (A : Mat) (h : Certificate A) :
    A 11 14=connection ℝ (decode A) 11 14 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h113 := h 113
  change -A 11 14 + -A 14 11=0 at h113
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h202 := h 202
  change A 3 1 + A 3 6 + A 3 11 + -A 14 1 + -A 14 6 + -A 14 11=0 at h202
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h17 + -1 * h45 + -1 * h50 + -1 * h80 + -1 * h113 + -1 * h126 + -1 * h139 + -1 * h142 + 1 * h202

private theorem entry_12_00 (A : Mat) (h : Certificate A) :
    A 12 0=connection ℝ (decode A) 12 0 := by
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h152 := h 152
  change -A 12 0 + -A 12 1 + -A 12 8=0 at h152
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h128 + -1 * h152

private theorem entry_12_01 (A : Mat) (h : Certificate A) :
    A 12 1=connection ℝ (decode A) 12 1 := by
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h155 := h 155
  change A 12 0 + A 12 1 + A 12 11=0 at h155
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h122 + 1 * h155

private theorem entry_12_02 (A : Mat) (h : Certificate A) :
    A 12 2=connection ℝ (decode A) 12 2 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h161 := h 161
  change -A 7 0 + -A 7 2 + -A 7 11 + A 12 0 + A 12 2 + A 12 11=0 at h161
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h7 + -1 * h122 + -1 * h136 + 1 * h161

private theorem entry_12_03 (A : Mat) (h : Certificate A) :
    A 12 3=connection ℝ (decode A) 12 3 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h167 := h 167
  change A 6 0 + A 6 3 + A 6 11 + A 12 0 + A 12 3 + A 12 11=0 at h167
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h6 + -1 * h122 + -1 * h142 + 1 * h167

private theorem entry_12_04 (A : Mat) (h : Certificate A) :
    A 12 4=connection ℝ (decode A) 12 4 := by
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h173 := h 173
  change A 12 0 + A 12 4 + A 12 11=0 at h173
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h122 + 1 * h173

private theorem entry_12_05 (A : Mat) (h : Certificate A) :
    A 12 5=connection ℝ (decode A) 12 5 := by
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h173 := h 173
  change A 12 0 + A 12 4 + A 12 11=0 at h173
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h122 + 1 * h144 + -1 * h173

private theorem entry_12_06 (A : Mat) (h : Certificate A) :
    A 12 6=connection ℝ (decode A) 12 6 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h181 := h 181
  change A 3 0 + A 3 6 + A 3 11 + A 12 0 + A 12 6 + A 12 11=0 at h181
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h3 + -1 * h45 + -1 * h50 + -1 * h80 + -1 * h122 + -1 * h139 + -1 * h142 + 1 * h181

private theorem entry_12_07 (A : Mat) (h : Certificate A) :
    A 12 7=connection ℝ (decode A) 12 7 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h184 := h 184
  change -A 2 0 + -A 2 7 + -A 2 11 + A 12 0 + A 12 7 + A 12 11=0 at h184
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h2 + -1 * h34 + -1 * h38 + -1 * h88 + -1 * h122 + 1 * h133 + -1 * h136 + 1 * h184

private theorem entry_12_08 (A : Mat) (h : Certificate A) :
    A 12 8=connection ℝ (decode A) 12 8 := by
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h155 := h 155
  change A 12 0 + A 12 1 + A 12 11=0 at h155
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h122 + -1 * h128 + -1 * h155

private theorem entry_12_09 (A : Mat) (h : Certificate A) :
    A 12 9=connection ℝ (decode A) 12 9 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h190 := h 190
  change A 12 0 + A 12 9 + A 12 11 + A 14 0 + A 14 9 + A 14 11=0 at h190
  have h202 := h 202
  change A 3 1 + A 3 6 + A 3 11 + -A 14 1 + -A 14 6 + -A 14 11=0 at h202
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h17 + -1 * h45 + -1 * h50 + -1 * h80 + -1 * h120 + -1 * h122 + -1 * h126 + -1 * h139 + -1 * h142 + 1 * h190 + 1 * h202

private theorem entry_12_10 (A : Mat) (h : Certificate A) :
    A 12 10=connection ℝ (decode A) 12 10 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h193 := h 193
  change A 12 0 + A 12 10 + A 12 11 + -A 13 0 + -A 13 10 + -A 13 11=0 at h193
  have h205 := h 205
  change -A 2 1 + -A 2 7 + -A 2 11 + A 13 1 + A 13 7 + A 13 11=0 at h205
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16 + -1 * h34 + -1 * h38 + -1 * h88 + -1 * h121 + -1 * h122 + -1 * h127 + 1 * h133 + -1 * h136 + 1 * h193 + 1 * h205

private theorem entry_12_11 (A : Mat) (h : Certificate A) :
    A 12 11=connection ℝ (decode A) 12 11 := by
  have h122 := h 122
  change A 12 0 + A 12 11=0 at h122
  have h128 := h 128
  change -A 12 1 + -A 12 8=0 at h128
  have h152 := h 152
  change -A 12 0 + -A 12 1 + -A 12 8=0 at h152
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h122 + -1 * h128 + 1 * h152

private theorem entry_12_12 (A : Mat) (h : Certificate A) :
    A 12 12=connection ℝ (decode A) 12 12 := by
  have h114 := h 114
  change -2*A 12 12=0 at h114
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h114

private theorem entry_12_13 (A : Mat) (h : Certificate A) :
    A 12 13=connection ℝ (decode A) 12 13 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h115 := h 115
  change -A 12 13 + A 13 12=0 at h115
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h209 := h 209
  change A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12=0 at h209
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43 + -1 * h55 + -1 * h62 + -1 * h72 + -1 * h115 + 1 * h138 + -1 * h144 + 1 * h149 + -1 * h209

private theorem entry_12_14 (A : Mat) (h : Certificate A) :
    A 12 14=connection ℝ (decode A) 12 14 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h116 := h 116
  change -A 12 14 + -A 14 12=0 at h116
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h207 := h 207
  change A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12=0 at h207
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h31 + -1 * h55 + -1 * h62 + -1 * h72 + -1 * h116 + 1 * h132 + -1 * h144 + 1 * h149 + -1 * h207

private theorem entry_13_00 (A : Mat) (h : Certificate A) :
    A 13 0=connection ℝ (decode A) 13 0 := by
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h151 := h 151
  change A 13 0 + A 13 1 + A 13 7=0 at h151
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h127 + 1 * h151

private theorem entry_13_01 (A : Mat) (h : Certificate A) :
    A 13 1=connection ℝ (decode A) 13 1 := by
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h154 := h 154
  change -A 13 0 + -A 13 1 + -A 13 10=0 at h154
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h121 + -1 * h154

private theorem entry_13_02 (A : Mat) (h : Certificate A) :
    A 13 2=connection ℝ (decode A) 13 2 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h135 := h 135
  change A 8 2 + A 8 10=0 at h135
  have h160 := h 160
  change A 8 0 + A 8 2 + A 8 10 + -A 13 0 + -A 13 2 + -A 13 10=0 at h160
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8 + 1 * h121 + 1 * h135 + -1 * h160

private theorem entry_13_03 (A : Mat) (h : Certificate A) :
    A 13 3=connection ℝ (decode A) 13 3 := by
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h166 := h 166
  change -A 13 0 + -A 13 3 + -A 13 10=0 at h166
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h121 + -1 * h166

private theorem entry_13_04 (A : Mat) (h : Certificate A) :
    A 13 4=connection ℝ (decode A) 13 4 := by
  have h6 := h 6
  change A 0 6 + -A 6 0=0 at h6
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h172 := h 172
  change -A 6 0 + -A 6 4 + -A 6 10 + -A 13 0 + -A 13 4 + -A 13 10=0 at h172
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h6 + 1 * h121 + 1 * h148 + -1 * h172

private theorem entry_13_05 (A : Mat) (h : Certificate A) :
    A 13 5=connection ℝ (decode A) 13 5 := by
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h166 := h 166
  change -A 13 0 + -A 13 3 + -A 13 10=0 at h166
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h121 + -1 * h138 + 1 * h166

private theorem entry_13_06 (A : Mat) (h : Certificate A) :
    A 13 6=connection ℝ (decode A) 13 6 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h180 := h 180
  change -A 4 0 + -A 4 6 + -A 4 10 + -A 13 0 + -A 13 6 + -A 13 10=0 at h180
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h4 + 1 * h56 + 1 * h60 + 1 * h79 + 1 * h121 + 1 * h145 + -1 * h148 + -1 * h180

private theorem entry_13_07 (A : Mat) (h : Certificate A) :
    A 13 7=connection ℝ (decode A) 13 7 := by
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h154 := h 154
  change -A 13 0 + -A 13 1 + -A 13 10=0 at h154
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h121 + 1 * h127 + 1 * h154

private theorem entry_13_08 (A : Mat) (h : Certificate A) :
    A 13 8=connection ℝ (decode A) 13 8 := by
  have h2 := h 2
  change A 0 2 + -A 2 0=0 at h2
  have h35 := h 35
  change -A 2 8 + -A 8 2=0 at h35
  have h37 := h 37
  change -A 2 10 + A 10 2=0 at h37
  have h94 := h 94
  change -A 8 10 + A 10 8=0 at h94
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h134 := h 134
  change A 10 2 + A 10 8=0 at h134
  have h135 := h 135
  change A 8 2 + A 8 10=0 at h135
  have h187 := h 187
  change A 2 0 + A 2 8 + A 2 10 + -A 13 0 + -A 13 8 + -A 13 10=0 at h187
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h2 + -1 * h35 + -1 * h37 + -1 * h94 + 1 * h121 + 1 * h134 + -1 * h135 + -1 * h187

private theorem entry_13_09 (A : Mat) (h : Certificate A) :
    A 13 9=connection ℝ (decode A) 13 9 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h189 := h 189
  change -A 13 0 + -A 13 9 + -A 13 10 + A 14 0 + A 14 9 + A 14 10=0 at h189
  have h201 := h 201
  change -A 4 1 + -A 4 6 + -A 4 10 + -A 14 1 + -A 14 6 + -A 14 10=0 at h201
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h18 + 1 * h56 + 1 * h60 + 1 * h79 + 1 * h120 + 1 * h121 + 1 * h126 + 1 * h145 + -1 * h148 + -1 * h189 + -1 * h201

private theorem entry_13_10 (A : Mat) (h : Certificate A) :
    A 13 10=connection ℝ (decode A) 13 10 := by
  have h121 := h 121
  change -A 13 0 + -A 13 10=0 at h121
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h151 := h 151
  change A 13 0 + A 13 1 + A 13 7=0 at h151
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h121 + 1 * h127 + -1 * h151

private theorem entry_13_11 (A : Mat) (h : Certificate A) :
    A 13 11=connection ℝ (decode A) 13 11 := by
  have h16 := h 16
  change A 1 2 + -A 2 1=0 at h16
  have h34 := h 34
  change -A 2 7 + A 7 2=0 at h34
  have h38 := h 38
  change -A 2 11 + -A 11 2=0 at h38
  have h88 := h 88
  change A 7 11 + -A 11 7=0 at h88
  have h127 := h 127
  change A 13 1 + A 13 7=0 at h127
  have h133 := h 133
  change -A 11 2 + -A 11 7=0 at h133
  have h136 := h 136
  change -A 7 2 + -A 7 11=0 at h136
  have h205 := h 205
  change -A 2 1 + -A 2 7 + -A 2 11 + A 13 1 + A 13 7 + A 13 11=0 at h205
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h16 + -1 * h34 + -1 * h38 + -1 * h88 + -1 * h127 + 1 * h133 + -1 * h136 + 1 * h205

private theorem entry_13_12 (A : Mat) (h : Certificate A) :
    A 13 12=connection ℝ (decode A) 13 12 := by
  have h43 := h 43
  change A 3 4 + -A 4 3=0 at h43
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h209 := h 209
  change A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12=0 at h209
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h43 + -1 * h55 + -1 * h62 + -1 * h72 + 1 * h138 + -1 * h144 + 1 * h149 + -1 * h209

private theorem entry_13_13 (A : Mat) (h : Certificate A) :
    A 13 13=connection ℝ (decode A) 13 13 := by
  have h117 := h 117
  change 2*A 13 13=0 at h117
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (1/2 : ℝ) * h117

private theorem entry_13_14 (A : Mat) (h : Certificate A) :
    A 13 14=connection ℝ (decode A) 13 14 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h118 := h 118
  change A 13 14 + -A 14 13=0 at h118
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h208 := h 208
  change -A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13=0 at h208
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30 + 1 * h44 + 1 * h52 + 1 * h73 + 1 * h118 + -1 * h132 + 1 * h138 + 1 * h143 + 1 * h208

private theorem entry_14_00 (A : Mat) (h : Certificate A) :
    A 14 0=connection ℝ (decode A) 14 0 := by
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h150 := h 150
  change -A 14 0 + -A 14 1 + -A 14 6=0 at h150
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h126 + -1 * h150

private theorem entry_14_01 (A : Mat) (h : Certificate A) :
    A 14 1=connection ℝ (decode A) 14 1 := by
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h153 := h 153
  change A 14 0 + A 14 1 + A 14 9=0 at h153
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h120 + 1 * h153

private theorem entry_14_02 (A : Mat) (h : Certificate A) :
    A 14 2=connection ℝ (decode A) 14 2 := by
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h159 := h 159
  change A 14 0 + A 14 2 + A 14 9=0 at h159
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h120 + 1 * h159

private theorem entry_14_03 (A : Mat) (h : Certificate A) :
    A 14 3=connection ℝ (decode A) 14 3 := by
  have h8 := h 8
  change A 0 8 + -A 8 0=0 at h8
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h141 := h 141
  change -A 8 3 + -A 8 9=0 at h141
  have h165 := h 165
  change -A 8 0 + -A 8 3 + -A 8 9 + A 14 0 + A 14 3 + A 14 9=0 at h165
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h8 + -1 * h120 + -1 * h141 + 1 * h165

private theorem entry_14_04 (A : Mat) (h : Certificate A) :
    A 14 4=connection ℝ (decode A) 14 4 := by
  have h7 := h 7
  change A 0 7 + A 7 0=0 at h7
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h147 := h 147
  change A 7 4 + A 7 9=0 at h147
  have h171 := h 171
  change A 7 0 + A 7 4 + A 7 9 + A 14 0 + A 14 4 + A 14 9=0 at h171
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination -1 * h7 + -1 * h120 + -1 * h147 + 1 * h171

private theorem entry_14_05 (A : Mat) (h : Certificate A) :
    A 14 5=connection ℝ (decode A) 14 5 := by
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h159 := h 159
  change A 14 0 + A 14 2 + A 14 9=0 at h159
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h120 + 1 * h132 + -1 * h159

private theorem entry_14_06 (A : Mat) (h : Certificate A) :
    A 14 6=connection ℝ (decode A) 14 6 := by
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h153 := h 153
  change A 14 0 + A 14 1 + A 14 9=0 at h153
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h120 + -1 * h126 + -1 * h153

private theorem entry_14_07 (A : Mat) (h : Certificate A) :
    A 14 7=connection ℝ (decode A) 14 7 := by
  have h4 := h 4
  change A 0 4 + -A 4 0=0 at h4
  have h57 := h 57
  change -A 4 7 + A 7 4=0 at h57
  have h59 := h 59
  change -A 4 9 + -A 9 4=0 at h59
  have h86 := h 86
  change A 7 9 + -A 9 7=0 at h86
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h146 := h 146
  change A 9 4 + A 9 7=0 at h146
  have h147 := h 147
  change A 7 4 + A 7 9=0 at h147
  have h183 := h 183
  change A 4 0 + A 4 7 + A 4 9 + A 14 0 + A 14 7 + A 14 9=0 at h183
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h4 + 1 * h57 + 1 * h59 + 1 * h86 + -1 * h120 + 1 * h146 + -1 * h147 + 1 * h183

private theorem entry_14_08 (A : Mat) (h : Certificate A) :
    A 14 8=connection ℝ (decode A) 14 8 := by
  have h3 := h 3
  change A 0 3 + A 3 0=0 at h3
  have h47 := h 47
  change A 3 8 + -A 8 3=0 at h47
  have h48 := h 48
  change A 3 9 + -A 9 3=0 at h48
  have h93 := h 93
  change -A 8 9 + -A 9 8=0 at h93
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h140 := h 140
  change -A 9 3 + -A 9 8=0 at h140
  have h141 := h 141
  change -A 8 3 + -A 8 9=0 at h141
  have h186 := h 186
  change -A 3 0 + -A 3 8 + -A 3 9 + A 14 0 + A 14 8 + A 14 9=0 at h186
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h3 + 1 * h47 + 1 * h48 + 1 * h93 + -1 * h120 + -1 * h140 + -1 * h141 + 1 * h186

private theorem entry_14_09 (A : Mat) (h : Certificate A) :
    A 14 9=connection ℝ (decode A) 14 9 := by
  have h120 := h 120
  change A 14 0 + A 14 9=0 at h120
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h150 := h 150
  change -A 14 0 + -A 14 1 + -A 14 6=0 at h150
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h120 + -1 * h126 + 1 * h150

private theorem entry_14_10 (A : Mat) (h : Certificate A) :
    A 14 10=connection ℝ (decode A) 14 10 := by
  have h18 := h 18
  change A 1 4 + -A 4 1=0 at h18
  have h56 := h 56
  change -A 4 6 + -A 6 4=0 at h56
  have h60 := h 60
  change -A 4 10 + A 10 4=0 at h60
  have h79 := h 79
  change -A 6 10 + A 10 6=0 at h79
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h145 := h 145
  change -A 10 4 + -A 10 6=0 at h145
  have h148 := h 148
  change -A 6 4 + -A 6 10=0 at h148
  have h201 := h 201
  change -A 4 1 + -A 4 6 + -A 4 10 + -A 14 1 + -A 14 6 + -A 14 10=0 at h201
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h18 + 1 * h56 + 1 * h60 + 1 * h79 + 1 * h126 + 1 * h145 + -1 * h148 + -1 * h201

private theorem entry_14_11 (A : Mat) (h : Certificate A) :
    A 14 11=connection ℝ (decode A) 14 11 := by
  have h17 := h 17
  change A 1 3 + A 3 1=0 at h17
  have h45 := h 45
  change A 3 6 + -A 6 3=0 at h45
  have h50 := h 50
  change A 3 11 + -A 11 3=0 at h50
  have h80 := h 80
  change -A 6 11 + -A 11 6=0 at h80
  have h126 := h 126
  change -A 14 1 + -A 14 6=0 at h126
  have h139 := h 139
  change A 11 3 + A 11 6=0 at h139
  have h142 := h 142
  change A 6 3 + A 6 11=0 at h142
  have h202 := h 202
  change A 3 1 + A 3 6 + A 3 11 + -A 14 1 + -A 14 6 + -A 14 11=0 at h202
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h17 + 1 * h45 + 1 * h50 + 1 * h80 + 1 * h126 + 1 * h139 + 1 * h142 + -1 * h202

private theorem entry_14_12 (A : Mat) (h : Certificate A) :
    A 14 12=connection ℝ (decode A) 14 12 := by
  have h31 := h 31
  change -A 2 4 + -A 4 2=0 at h31
  have h55 := h 55
  change -A 4 5 + A 5 4=0 at h55
  have h62 := h 62
  change -A 4 12 + -A 12 4=0 at h62
  have h72 := h 72
  change A 5 12 + -A 12 5=0 at h72
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h144 := h 144
  change A 12 4 + A 12 5=0 at h144
  have h149 := h 149
  change A 5 4 + A 5 12=0 at h149
  have h207 := h 207
  change A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12=0 at h207
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h31 + 1 * h55 + 1 * h62 + 1 * h72 + -1 * h132 + 1 * h144 + -1 * h149 + 1 * h207

private theorem entry_14_13 (A : Mat) (h : Certificate A) :
    A 14 13=connection ℝ (decode A) 14 13 := by
  have h30 := h 30
  change -A 2 3 + A 3 2=0 at h30
  have h44 := h 44
  change A 3 5 + A 5 3=0 at h44
  have h52 := h 52
  change A 3 13 + A 13 3=0 at h52
  have h73 := h 73
  change A 5 13 + A 13 5=0 at h73
  have h132 := h 132
  change A 14 2 + A 14 5=0 at h132
  have h138 := h 138
  change -A 13 3 + -A 13 5=0 at h138
  have h143 := h 143
  change -A 5 3 + -A 5 13=0 at h143
  have h208 := h 208
  change -A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13=0 at h208
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination 1 * h30 + 1 * h44 + 1 * h52 + 1 * h73 + -1 * h132 + 1 * h138 + 1 * h143 + 1 * h208

private theorem entry_14_14 (A : Mat) (h : Certificate A) :
    A 14 14=connection ℝ (decode A) 14 14 := by
  have h119 := h 119
  change -2*A 14 14=0 at h119
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
  norm_num [coefficients,decode,Fin.sum_univ_succ]
  linear_combination (-1/2 : ℝ) * h119

theorem recover (A : Mat) (h : Certificate A) : A=connection ℝ (decode A) := by
  ext r c
  fin_cases r <;> fin_cases c
  · exact entry_00_00 A h
  · exact entry_00_01 A h
  · exact entry_00_02 A h
  · exact entry_00_03 A h
  · exact entry_00_04 A h
  · exact entry_00_05 A h
  · exact entry_00_06 A h
  · exact entry_00_07 A h
  · exact entry_00_08 A h
  · exact entry_00_09 A h
  · exact entry_00_10 A h
  · exact entry_00_11 A h
  · exact entry_00_12 A h
  · exact entry_00_13 A h
  · exact entry_00_14 A h
  · exact entry_01_00 A h
  · exact entry_01_01 A h
  · exact entry_01_02 A h
  · exact entry_01_03 A h
  · exact entry_01_04 A h
  · exact entry_01_05 A h
  · exact entry_01_06 A h
  · exact entry_01_07 A h
  · exact entry_01_08 A h
  · exact entry_01_09 A h
  · exact entry_01_10 A h
  · exact entry_01_11 A h
  · exact entry_01_12 A h
  · exact entry_01_13 A h
  · exact entry_01_14 A h
  · exact entry_02_00 A h
  · exact entry_02_01 A h
  · exact entry_02_02 A h
  · exact entry_02_03 A h
  · exact entry_02_04 A h
  · exact entry_02_05 A h
  · exact entry_02_06 A h
  · exact entry_02_07 A h
  · exact entry_02_08 A h
  · exact entry_02_09 A h
  · exact entry_02_10 A h
  · exact entry_02_11 A h
  · exact entry_02_12 A h
  · exact entry_02_13 A h
  · exact entry_02_14 A h
  · exact entry_03_00 A h
  · exact entry_03_01 A h
  · exact entry_03_02 A h
  · exact entry_03_03 A h
  · exact entry_03_04 A h
  · exact entry_03_05 A h
  · exact entry_03_06 A h
  · exact entry_03_07 A h
  · exact entry_03_08 A h
  · exact entry_03_09 A h
  · exact entry_03_10 A h
  · exact entry_03_11 A h
  · exact entry_03_12 A h
  · exact entry_03_13 A h
  · exact entry_03_14 A h
  · exact entry_04_00 A h
  · exact entry_04_01 A h
  · exact entry_04_02 A h
  · exact entry_04_03 A h
  · exact entry_04_04 A h
  · exact entry_04_05 A h
  · exact entry_04_06 A h
  · exact entry_04_07 A h
  · exact entry_04_08 A h
  · exact entry_04_09 A h
  · exact entry_04_10 A h
  · exact entry_04_11 A h
  · exact entry_04_12 A h
  · exact entry_04_13 A h
  · exact entry_04_14 A h
  · exact entry_05_00 A h
  · exact entry_05_01 A h
  · exact entry_05_02 A h
  · exact entry_05_03 A h
  · exact entry_05_04 A h
  · exact entry_05_05 A h
  · exact entry_05_06 A h
  · exact entry_05_07 A h
  · exact entry_05_08 A h
  · exact entry_05_09 A h
  · exact entry_05_10 A h
  · exact entry_05_11 A h
  · exact entry_05_12 A h
  · exact entry_05_13 A h
  · exact entry_05_14 A h
  · exact entry_06_00 A h
  · exact entry_06_01 A h
  · exact entry_06_02 A h
  · exact entry_06_03 A h
  · exact entry_06_04 A h
  · exact entry_06_05 A h
  · exact entry_06_06 A h
  · exact entry_06_07 A h
  · exact entry_06_08 A h
  · exact entry_06_09 A h
  · exact entry_06_10 A h
  · exact entry_06_11 A h
  · exact entry_06_12 A h
  · exact entry_06_13 A h
  · exact entry_06_14 A h
  · exact entry_07_00 A h
  · exact entry_07_01 A h
  · exact entry_07_02 A h
  · exact entry_07_03 A h
  · exact entry_07_04 A h
  · exact entry_07_05 A h
  · exact entry_07_06 A h
  · exact entry_07_07 A h
  · exact entry_07_08 A h
  · exact entry_07_09 A h
  · exact entry_07_10 A h
  · exact entry_07_11 A h
  · exact entry_07_12 A h
  · exact entry_07_13 A h
  · exact entry_07_14 A h
  · exact entry_08_00 A h
  · exact entry_08_01 A h
  · exact entry_08_02 A h
  · exact entry_08_03 A h
  · exact entry_08_04 A h
  · exact entry_08_05 A h
  · exact entry_08_06 A h
  · exact entry_08_07 A h
  · exact entry_08_08 A h
  · exact entry_08_09 A h
  · exact entry_08_10 A h
  · exact entry_08_11 A h
  · exact entry_08_12 A h
  · exact entry_08_13 A h
  · exact entry_08_14 A h
  · exact entry_09_00 A h
  · exact entry_09_01 A h
  · exact entry_09_02 A h
  · exact entry_09_03 A h
  · exact entry_09_04 A h
  · exact entry_09_05 A h
  · exact entry_09_06 A h
  · exact entry_09_07 A h
  · exact entry_09_08 A h
  · exact entry_09_09 A h
  · exact entry_09_10 A h
  · exact entry_09_11 A h
  · exact entry_09_12 A h
  · exact entry_09_13 A h
  · exact entry_09_14 A h
  · exact entry_10_00 A h
  · exact entry_10_01 A h
  · exact entry_10_02 A h
  · exact entry_10_03 A h
  · exact entry_10_04 A h
  · exact entry_10_05 A h
  · exact entry_10_06 A h
  · exact entry_10_07 A h
  · exact entry_10_08 A h
  · exact entry_10_09 A h
  · exact entry_10_10 A h
  · exact entry_10_11 A h
  · exact entry_10_12 A h
  · exact entry_10_13 A h
  · exact entry_10_14 A h
  · exact entry_11_00 A h
  · exact entry_11_01 A h
  · exact entry_11_02 A h
  · exact entry_11_03 A h
  · exact entry_11_04 A h
  · exact entry_11_05 A h
  · exact entry_11_06 A h
  · exact entry_11_07 A h
  · exact entry_11_08 A h
  · exact entry_11_09 A h
  · exact entry_11_10 A h
  · exact entry_11_11 A h
  · exact entry_11_12 A h
  · exact entry_11_13 A h
  · exact entry_11_14 A h
  · exact entry_12_00 A h
  · exact entry_12_01 A h
  · exact entry_12_02 A h
  · exact entry_12_03 A h
  · exact entry_12_04 A h
  · exact entry_12_05 A h
  · exact entry_12_06 A h
  · exact entry_12_07 A h
  · exact entry_12_08 A h
  · exact entry_12_09 A h
  · exact entry_12_10 A h
  · exact entry_12_11 A h
  · exact entry_12_12 A h
  · exact entry_12_13 A h
  · exact entry_12_14 A h
  · exact entry_13_00 A h
  · exact entry_13_01 A h
  · exact entry_13_02 A h
  · exact entry_13_03 A h
  · exact entry_13_04 A h
  · exact entry_13_05 A h
  · exact entry_13_06 A h
  · exact entry_13_07 A h
  · exact entry_13_08 A h
  · exact entry_13_09 A h
  · exact entry_13_10 A h
  · exact entry_13_11 A h
  · exact entry_13_12 A h
  · exact entry_13_13 A h
  · exact entry_13_14 A h
  · exact entry_14_00 A h
  · exact entry_14_01 A h
  · exact entry_14_02 A h
  · exact entry_14_03 A h
  · exact entry_14_04 A h
  · exact entry_14_05 A h
  · exact entry_14_06 A h
  · exact entry_14_07 A h
  · exact entry_14_08 A h
  · exact entry_14_09 A h
  · exact entry_14_10 A h
  · exact entry_14_11 A h
  · exact entry_14_12 A h
  · exact entry_14_13 A h
  · exact entry_14_14 A h

theorem decode_connection (w : I → ℝ) : decode (connection ℝ w)=w := by
  ext p
  fin_cases p
  · change (connection ℝ w 1 5)=w 0
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 0 5)=w 1
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change (connection ℝ w 0 6)=w 2
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 0 7)=w 3
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change (connection ℝ w 0 8)=w 4
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change (connection ℝ w 0 1)=w 5
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 0 2)=w 6
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change (connection ℝ w 0 3)=w 7
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 0 4)=w 8
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 1 2)=w 9
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change (connection ℝ w 1 3)=w 10
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 1 4)=w 11
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change (connection ℝ w 2 3)=w 12
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 2 4)=w 13
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]
  · change -(connection ℝ w 3 4)=w 14
    simp only [connection,Matrix.sum_apply,Matrix.smul_apply,generator_entry]
    norm_num [coefficients,Fin.sum_univ_succ]

theorem connection_injective : Function.Injective (connection ℝ) := by
  intro u v h
  have hd := congrArg decode h
  simpa only [decode_connection] using hd

#print axioms recover
#print axioms decode_connection
#print axioms connection_injective
end
end PDTStabilizerRecovery
