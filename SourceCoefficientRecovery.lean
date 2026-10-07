module
public import SourceCoefficientData

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel
open scoped Matrix

theorem coefficient_recovery (c : Coeff) (h : constraints c=0) :
    c=(2*c 0 0) • maxwellCoefficients := by
  have h0 : (-2) * c 1 0=0 := congrFun h 0
  have h1 : (-1) * c 0 3 + (-2) * c 1 1=0 := congrFun h 1
  have h2 : (-1) * c 0 4 + (-2) * c 1 2=0 := congrFun h 2
  have h3 : 1 * c 0 1 + (-2) * c 1 3=0 := congrFun h 3
  have h4 : 1 * c 0 2 + (-2) * c 1 4=0 := congrFun h 4
  have h5 : (-2) * c 1 5=0 := congrFun h 5
  have h6 : (-1) * c 0 8 + (-2) * c 1 6=0 := congrFun h 6
  have h7 : (-1) * c 0 9 + (-1) * c 0 12 + (-2) * c 1 7=0 := congrFun h 7
  have h8 : 2 * c 0 6 + (-2) * c 0 15 + (-2) * c 1 8=0 := congrFun h 8
  have h9 : 1 * c 0 7 + (-1) * c 0 16 + (-2) * c 1 9=0 := congrFun h 9
  have h10 : (-1) * c 0 17 + (-2) * c 1 10=0 := congrFun h 10
  have h11 : (-1) * c 0 13 + (-2) * c 1 11=0 := congrFun h 11
  have h12 : 1 * c 0 7 + (-1) * c 0 16 + (-2) * c 1 12=0 := congrFun h 12
  have h13 : 2 * c 0 11 + (-2) * c 0 18 + (-2) * c 1 13=0 := congrFun h 13
  have h14 : (-1) * c 0 19 + (-2) * c 1 14=0 := congrFun h 14
  have h15 : 1 * c 0 8 + (-2) * c 1 15=0 := congrFun h 15
  have h16 : 1 * c 0 9 + 1 * c 0 12 + (-2) * c 1 16=0 := congrFun h 16
  have h17 : 1 * c 0 10 + (-2) * c 1 17=0 := congrFun h 17
  have h18 : 1 * c 0 13 + (-2) * c 1 18=0 := congrFun h 18
  have h19 : 1 * c 0 14 + (-2) * c 1 19=0 := congrFun h 19
  have h20 : (-2) * c 1 20=0 := congrFun h 20
  have h21 : 1 * c 0 0 + (-1) * c 4 0=0 := congrFun h 21
  have h22 : (-1) * c 1 3 + 1 * c 0 1 + (-1) * c 4 1=0 := congrFun h 22
  have h23 : (-1) * c 1 4 + 1 * c 0 2 + (-1) * c 4 2=0 := congrFun h 23
  have h24 : 1 * c 1 1 + 1 * c 0 3 + (-1) * c 4 3=0 := congrFun h 24
  have h25 : 1 * c 1 2 + 1 * c 0 4 + (-1) * c 4 4=0 := congrFun h 25
  have h26 : 1 * c 0 5 + (-1) * c 4 5=0 := congrFun h 26
  have h27 : (-1) * c 1 8 + 1 * c 0 6 + (-1) * c 4 6=0 := congrFun h 27
  have h28 : (-1) * c 1 9 + (-1) * c 1 12 + 1 * c 0 7 + (-1) * c 4 7=0 := congrFun h 28
  have h29 : 2 * c 1 6 + (-2) * c 1 15 + 1 * c 0 8 + (-1) * c 4 8=0 := congrFun h 29
  have h30 : 1 * c 1 7 + (-1) * c 1 16 + 1 * c 0 9 + (-1) * c 4 9=0 := congrFun h 30
  have h31 : (-1) * c 1 17 + 1 * c 0 10 + (-1) * c 4 10=0 := congrFun h 31
  have h32 : (-1) * c 1 13 + 1 * c 0 11 + (-1) * c 4 11=0 := congrFun h 32
  have h33 : 1 * c 1 7 + (-1) * c 1 16 + 1 * c 0 12 + (-1) * c 4 12=0 := congrFun h 33
  have h34 : 2 * c 1 11 + (-2) * c 1 18 + 1 * c 0 13 + (-1) * c 4 13=0 := congrFun h 34
  have h35 : (-1) * c 1 19 + 1 * c 0 14 + (-1) * c 4 14=0 := congrFun h 35
  have h36 : 1 * c 1 8 + 1 * c 0 15 + (-1) * c 4 15=0 := congrFun h 36
  have h37 : 1 * c 1 9 + 1 * c 1 12 + 1 * c 0 16 + (-1) * c 4 16=0 := congrFun h 37
  have h38 : 1 * c 1 10 + 1 * c 0 17 + (-1) * c 4 17=0 := congrFun h 38
  have h39 : 1 * c 1 13 + 1 * c 0 18 + (-1) * c 4 18=0 := congrFun h 39
  have h40 : 1 * c 1 14 + 1 * c 0 19 + (-1) * c 4 19=0 := congrFun h 40
  have h41 : 1 * c 0 20 + (-1) * c 4 20=0 := congrFun h 41
  have h42 : (-1) * c 5 0=0 := congrFun h 42
  have h43 : (-1) * c 2 3 + (-1) * c 5 1=0 := congrFun h 43
  have h44 : (-1) * c 2 4 + (-1) * c 5 2=0 := congrFun h 44
  have h45 : 1 * c 2 1 + (-1) * c 5 3=0 := congrFun h 45
  have h46 : 1 * c 2 2 + (-1) * c 5 4=0 := congrFun h 46
  have h47 : (-1) * c 5 5=0 := congrFun h 47
  have h48 : (-1) * c 2 8 + (-1) * c 5 6=0 := congrFun h 48
  have h49 : (-1) * c 2 9 + (-1) * c 2 12 + (-1) * c 5 7=0 := congrFun h 49
  have h50 : 2 * c 2 6 + (-2) * c 2 15 + (-1) * c 5 8=0 := congrFun h 50
  have h51 : 1 * c 2 7 + (-1) * c 2 16 + (-1) * c 5 9=0 := congrFun h 51
  have h52 : (-1) * c 2 17 + (-1) * c 5 10=0 := congrFun h 52
  have h53 : (-1) * c 2 13 + (-1) * c 5 11=0 := congrFun h 53
  have h54 : 1 * c 2 7 + (-1) * c 2 16 + (-1) * c 5 12=0 := congrFun h 54
  have h55 : 2 * c 2 11 + (-2) * c 2 18 + (-1) * c 5 13=0 := congrFun h 55
  have h56 : (-1) * c 2 19 + (-1) * c 5 14=0 := congrFun h 56
  have h57 : 1 * c 2 8 + (-1) * c 5 15=0 := congrFun h 57
  have h58 : 1 * c 2 9 + 1 * c 2 12 + (-1) * c 5 16=0 := congrFun h 58
  have h59 : 1 * c 2 10 + (-1) * c 5 17=0 := congrFun h 59
  have h60 : 1 * c 2 13 + (-1) * c 5 18=0 := congrFun h 60
  have h61 : 1 * c 2 14 + (-1) * c 5 19=0 := congrFun h 61
  have h62 : (-1) * c 5 20=0 := congrFun h 62
  have h63 : (-1) * c 6 0=0 := congrFun h 63
  have h64 : (-1) * c 3 3 + (-1) * c 6 1=0 := congrFun h 64
  have h65 : (-1) * c 3 4 + (-1) * c 6 2=0 := congrFun h 65
  have h66 : 1 * c 3 1 + (-1) * c 6 3=0 := congrFun h 66
  have h67 : 1 * c 3 2 + (-1) * c 6 4=0 := congrFun h 67
  have h68 : (-1) * c 6 5=0 := congrFun h 68
  have h69 : (-1) * c 3 8 + (-1) * c 6 6=0 := congrFun h 69
  have h70 : (-1) * c 3 9 + (-1) * c 3 12 + (-1) * c 6 7=0 := congrFun h 70
  have h71 : 2 * c 3 6 + (-2) * c 3 15 + (-1) * c 6 8=0 := congrFun h 71
  have h72 : 1 * c 3 7 + (-1) * c 3 16 + (-1) * c 6 9=0 := congrFun h 72
  have h73 : (-1) * c 3 17 + (-1) * c 6 10=0 := congrFun h 73
  have h74 : (-1) * c 3 13 + (-1) * c 6 11=0 := congrFun h 74
  have h75 : 1 * c 3 7 + (-1) * c 3 16 + (-1) * c 6 12=0 := congrFun h 75
  have h76 : 2 * c 3 11 + (-2) * c 3 18 + (-1) * c 6 13=0 := congrFun h 76
  have h77 : (-1) * c 3 19 + (-1) * c 6 14=0 := congrFun h 77
  have h78 : 1 * c 3 8 + (-1) * c 6 15=0 := congrFun h 78
  have h79 : 1 * c 3 9 + 1 * c 3 12 + (-1) * c 6 16=0 := congrFun h 79
  have h80 : 1 * c 3 10 + (-1) * c 6 17=0 := congrFun h 80
  have h81 : 1 * c 3 13 + (-1) * c 6 18=0 := congrFun h 81
  have h82 : 1 * c 3 14 + (-1) * c 6 19=0 := congrFun h 82
  have h83 : (-1) * c 6 20=0 := congrFun h 83
  have h84 : (-1) * c 4 3 + 2 * c 1 1=0 := congrFun h 84
  have h85 : (-1) * c 4 4 + 2 * c 1 2=0 := congrFun h 85
  have h86 : 1 * c 4 1 + 2 * c 1 3=0 := congrFun h 86
  have h87 : 1 * c 4 2 + 2 * c 1 4=0 := congrFun h 87
  have h88 : (-1) * c 4 17 + 2 * c 1 10=0 := congrFun h 88
  have h89 : (-1) * c 4 19 + 2 * c 1 14=0 := congrFun h 89
  have h90 : 1 * c 4 10 + 2 * c 1 17=0 := congrFun h 90
  have h91 : 1 * c 4 14 + 2 * c 1 19=0 := congrFun h 91
  have h92 : 1 * c 2 0=0 := congrFun h 92
  have h93 : 1 * c 2 5=0 := congrFun h 93
  have h94 : (-1) * c 5 8 + 1 * c 2 6=0 := congrFun h 94
  have h95 : (-1) * c 5 9 + (-1) * c 5 12 + 1 * c 2 7=0 := congrFun h 95
  have h96 : 2 * c 5 6 + (-2) * c 5 15 + 1 * c 2 8=0 := congrFun h 96
  have h97 : 1 * c 5 7 + (-1) * c 5 16 + 1 * c 2 9=0 := congrFun h 97
  have h98 : (-1) * c 5 13 + 1 * c 2 11=0 := congrFun h 98
  have h99 : 1 * c 5 7 + (-1) * c 5 16 + 1 * c 2 12=0 := congrFun h 99
  have h100 : 2 * c 5 11 + (-2) * c 5 18 + 1 * c 2 13=0 := congrFun h 100
  have h101 : 1 * c 5 8 + 1 * c 2 15=0 := congrFun h 101
  have h102 : 1 * c 5 9 + 1 * c 5 12 + 1 * c 2 16=0 := congrFun h 102
  have h103 : 1 * c 5 13 + 1 * c 2 18=0 := congrFun h 103
  have h104 : 1 * c 2 20=0 := congrFun h 104
  have h105 : 1 * c 3 0=0 := congrFun h 105
  have h106 : 1 * c 3 5=0 := congrFun h 106
  have h107 : (-1) * c 6 8 + 1 * c 3 6=0 := congrFun h 107
  have h108 : (-1) * c 6 9 + (-1) * c 6 12 + 1 * c 3 7=0 := congrFun h 108
  have h109 : 2 * c 6 6 + (-2) * c 6 15 + 1 * c 3 8=0 := congrFun h 109
  have h110 : 1 * c 6 7 + (-1) * c 6 16 + 1 * c 3 9=0 := congrFun h 110
  have h111 : (-1) * c 6 13 + 1 * c 3 11=0 := congrFun h 111
  have h112 : 1 * c 6 7 + (-1) * c 6 16 + 1 * c 3 12=0 := congrFun h 112
  have h113 : 2 * c 6 11 + (-2) * c 6 18 + 1 * c 3 13=0 := congrFun h 113
  have h114 : 1 * c 6 8 + 1 * c 3 15=0 := congrFun h 114
  have h115 : 1 * c 6 9 + 1 * c 6 12 + 1 * c 3 16=0 := congrFun h 115
  have h116 : 1 * c 6 13 + 1 * c 3 18=0 := congrFun h 116
  have h117 : 1 * c 3 20=0 := congrFun h 117
  have h118 : (-1) * c 7 3=0 := congrFun h 118
  have h119 : (-1) * c 7 4=0 := congrFun h 119
  have h120 : 1 * c 7 1=0 := congrFun h 120
  have h121 : 1 * c 7 2=0 := congrFun h 121
  have h122 : (-1) * c 7 8=0 := congrFun h 122
  have h123 : (-1) * c 7 9 + (-1) * c 7 12=0 := congrFun h 123
  have h124 : 2 * c 7 6 + (-2) * c 7 15=0 := congrFun h 124
  have h125 : 1 * c 7 7 + (-1) * c 7 16=0 := congrFun h 125
  have h126 : (-1) * c 7 17=0 := congrFun h 126
  have h127 : (-1) * c 7 13=0 := congrFun h 127
  have h128 : 2 * c 7 11 + (-2) * c 7 18=0 := congrFun h 128
  have h129 : (-1) * c 7 19=0 := congrFun h 129
  have h130 : 1 * c 7 10=0 := congrFun h 130
  have h131 : 1 * c 7 14=0 := congrFun h 131
  have h132 : (-1) * c 8 3=0 := congrFun h 132
  have h133 : (-1) * c 8 4=0 := congrFun h 133
  have h134 : 1 * c 8 1=0 := congrFun h 134
  have h135 : 1 * c 8 2=0 := congrFun h 135
  have h136 : (-1) * c 8 8=0 := congrFun h 136
  have h137 : (-1) * c 8 9 + (-1) * c 8 12=0 := congrFun h 137
  have h138 : 2 * c 8 6 + (-2) * c 8 15=0 := congrFun h 138
  have h139 : 1 * c 8 7 + (-1) * c 8 16=0 := congrFun h 139
  have h140 : (-1) * c 8 17=0 := congrFun h 140
  have h141 : (-1) * c 8 13=0 := congrFun h 141
  have h142 : 2 * c 8 11 + (-2) * c 8 18=0 := congrFun h 142
  have h143 : (-1) * c 8 19=0 := congrFun h 143
  have h144 : 1 * c 8 10=0 := congrFun h 144
  have h145 : 1 * c 8 14=0 := congrFun h 145
  have h146 : (-1) * c 9 3=0 := congrFun h 146
  have h147 : (-1) * c 9 4=0 := congrFun h 147
  have h148 : 1 * c 9 1=0 := congrFun h 148
  have h149 : 1 * c 9 2=0 := congrFun h 149
  have h150 : (-1) * c 9 8=0 := congrFun h 150
  have h151 : (-1) * c 9 9 + (-1) * c 9 12=0 := congrFun h 151
  have h152 : 2 * c 9 6 + (-2) * c 9 15=0 := congrFun h 152
  have h153 : 1 * c 9 7 + (-1) * c 9 16=0 := congrFun h 153
  have h154 : (-1) * c 9 17=0 := congrFun h 154
  have h155 : (-1) * c 9 13=0 := congrFun h 155
  have h156 : 2 * c 9 11 + (-2) * c 9 18=0 := congrFun h 156
  have h157 : (-1) * c 9 19=0 := congrFun h 157
  have h158 : 1 * c 9 10=0 := congrFun h 158
  have h159 : 1 * c 9 14=0 := congrFun h 159
  have h160 : 1 * c 0 8 + (-2) * c 2 1=0 := congrFun h 160
  have h161 : (-1) * c 0 5 + 1 * c 0 12 + (-2) * c 2 2=0 := congrFun h 161
  have h162 : (-2) * c 0 0 + 2 * c 0 15 + (-2) * c 2 3=0 := congrFun h 162
  have h163 : 1 * c 0 16 + (-2) * c 2 4=0 := congrFun h 163
  have h164 : 1 * c 0 7 + (-2) * c 2 10=0 := congrFun h 164
  have h165 : 2 * c 0 11 + (-2) * c 0 20 + (-2) * c 2 14=0 := congrFun h 165
  have h166 : (-1) * c 0 5 + 1 * c 0 12 + (-2) * c 2 17=0 := congrFun h 166
  have h167 : 1 * c 0 13 + (-2) * c 2 19=0 := congrFun h 167
  have h168 : 1 * c 1 8 + (-1) * c 5 1=0 := congrFun h 168
  have h169 : (-1) * c 1 5 + 1 * c 1 12 + (-1) * c 5 2=0 := congrFun h 169
  have h170 : (-2) * c 1 0 + 2 * c 1 15 + (-1) * c 5 3=0 := congrFun h 170
  have h171 : 1 * c 1 16 + (-1) * c 5 4=0 := congrFun h 171
  have h172 : 2 * c 1 11 + (-2) * c 1 20 + (-1) * c 5 14=0 := congrFun h 172
  have h173 : (-1) * c 1 5 + 1 * c 1 12 + (-1) * c 5 17=0 := congrFun h 173
  have h174 : 1 * c 1 13 + (-1) * c 5 19=0 := congrFun h 174
  have h175 : 1 * c 2 3 + 1 * c 0 0 + (-1) * c 7 0=0 := congrFun h 175
  have h176 : 1 * c 2 2 + 1 * c 2 17 + 1 * c 0 5 + (-1) * c 7 5=0 := congrFun h 176
  have h177 : 1 * c 0 6 + (-1) * c 7 6=0 := congrFun h 177
  have h178 : (-1) * c 2 10 + 1 * c 0 7 + (-1) * c 7 7=0 := congrFun h 178
  have h179 : 1 * c 0 9 + (-1) * c 7 9=0 := congrFun h 179
  have h180 : (-1) * c 2 14 + 1 * c 0 11 + (-1) * c 7 11=0 := congrFun h 180
  have h181 : 1 * c 2 14 + 1 * c 0 20 + (-1) * c 7 20=0 := congrFun h 181
  have h182 : 1 * c 3 3 + (-1) * c 8 0=0 := congrFun h 182
  have h183 : 1 * c 3 2 + 1 * c 3 17 + (-1) * c 8 5=0 := congrFun h 183
  have h184 : (-1) * c 8 6=0 := congrFun h 184
  have h185 : (-1) * c 3 10 + (-1) * c 8 7=0 := congrFun h 185
  have h186 : (-1) * c 3 1 + (-1) * c 8 8=0 := congrFun h 186
  have h187 : (-1) * c 8 9=0 := congrFun h 187
  have h188 : (-1) * c 3 14 + (-1) * c 8 11=0 := congrFun h 188
  have h189 : (-1) * c 3 2 + (-1) * c 3 17 + (-1) * c 8 12=0 := congrFun h 189
  have h190 : (-1) * c 3 19 + (-1) * c 8 13=0 := congrFun h 190
  have h191 : (-1) * c 3 3 + (-1) * c 8 15=0 := congrFun h 191
  have h192 : (-1) * c 3 4 + (-1) * c 8 16=0 := congrFun h 192
  have h193 : (-1) * c 8 18=0 := congrFun h 193
  have h194 : 1 * c 3 14 + (-1) * c 8 20=0 := congrFun h 194
  have h195 : (-1) * c 6 10=0 := congrFun h 195
  have h196 : (-1) * c 9 5 + 1 * c 9 12=0 := congrFun h 196
  have h197 : (-2) * c 9 0 + 2 * c 9 15=0 := congrFun h 197
  have h198 : 1 * c 9 16=0 := congrFun h 198
  have h199 : 2 * c 9 11 + (-2) * c 9 20=0 := congrFun h 199
  have h200 : 2 * c 0 0 + 2 * c 0 18 + 2 * c 3 4=0 := congrFun h 200
  have h201 : 1 * c 1 13 + 1 * c 6 2=0 := congrFun h 201
  have h202 : 1 * c 1 16 + 1 * c 6 3=0 := congrFun h 202
  have h203 : 1 * c 1 8 + 1 * c 6 17=0 := congrFun h 203
  have h204 : 1 * c 3 4 + 1 * c 0 0 + 1 * c 9 0=0 := congrFun h 204
  have h205 : 1 * c 3 1 + 1 * c 3 19 + 1 * c 0 5 + 1 * c 9 5=0 := congrFun h 205
  have h206 : 1 * c 0 11 + 1 * c 9 11=0 := congrFun h 206
  have h207 : 1 * c 0 0 + 1 * c 4 0 + 1 * c 7 0 + (-1) * c 9 0=0 := congrFun h 207
  have h208 : 1 * c 0 5 + 1 * c 4 5 + 1 * c 7 5 + (-1) * c 9 5=0 := congrFun h 208
  ext t m
  fin_cases t <;> fin_cases m
  · change c 0 0=(2*c 0 0)*(1/2 : ℝ)
    ring
  · change c 0 1=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h3 + (2/3 : ℝ) * h22 + (2/3 : ℝ) * h86
  · change c 0 2=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h4 + (2/3 : ℝ) * h23 + (2/3 : ℝ) * h87
  · change c 0 3=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h1 + (2/3 : ℝ) * h24 + (-2/3 : ℝ) * h84
  · change c 0 4=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h2 + (2/3 : ℝ) * h25 + (-2/3 : ℝ) * h85
  · change c 0 5=(2*c 0 0)*0
    linear_combination (1/4 : ℝ) * h26 + (-1/2 : ℝ) * h46 + (-1/2 : ℝ) * h66 + (1/4 : ℝ) * h136 + (-1/4 : ℝ) * h141 + (-1/8 : ℝ) * h161 + (1/8 : ℝ) * h166 + (1/2 : ℝ) * h171 + (1/4 : ℝ) * h176 + (-1/4 : ℝ) * h186 + (1/4 : ℝ) * h190 + (-1/2 : ℝ) * h202 + (1/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 0 6=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h8 + (-1) * h43 + (1/2 : ℝ) * h162 + 1 * h168
  · change c 0 7=(2*c 0 0)*0
    linear_combination (-1) * h5 + 1 * h12 + (-2) * h44 + 1 * h163 + 2 * h169
  · change c 0 8=(2*c 0 0)*0
    linear_combination (-2) * h0 + 2 * h15 + (-2) * h45 + (-1) * h160 + 2 * h170
  · change c 0 9=(2*c 0 0)*0
    linear_combination 1 * h16 + (-1/4 : ℝ) * h26 + (-3/2 : ℝ) * h46 + (1/2 : ℝ) * h66 + (-1/4 : ℝ) * h136 + (1/4 : ℝ) * h141 + (-7/8 : ℝ) * h161 + (-1/8 : ℝ) * h166 + (3/2 : ℝ) * h171 + (-1/4 : ℝ) * h176 + (1/4 : ℝ) * h186 + (-1/4 : ℝ) * h190 + (1/2 : ℝ) * h202 + (-1/4 : ℝ) * h205 + (-1/4 : ℝ) * h208
  · change c 0 10=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h17 + (2/3 : ℝ) * h31 + (2/3 : ℝ) * h90
  · change c 0 11=(2*c 0 0)*(-1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + 1 * h65 + (1/2 : ℝ) * h200 + 1 * h201
  · change c 0 12=(2*c 0 0)*0
    linear_combination (1/4 : ℝ) * h26 + (3/2 : ℝ) * h46 + (3/2 : ℝ) * h66 + (-7/4 : ℝ) * h136 + (-1/4 : ℝ) * h141 + (7/8 : ℝ) * h161 + (1/8 : ℝ) * h166 + (-3/2 : ℝ) * h171 + (1/4 : ℝ) * h176 + (7/4 : ℝ) * h186 + (1/4 : ℝ) * h190 + (3/2 : ℝ) * h202 + (1/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 0 13=(2*c 0 0)*0
    linear_combination (-2) * h11 + 2 * h20 + 2 * h56 + (-1) * h167 + (-2) * h172
  · change c 0 14=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h19 + (2/3 : ℝ) * h35 + (2/3 : ℝ) * h91
  · change c 0 15=(2*c 0 0)*(-1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h162 + (1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 0 16=(2*c 0 0)*0
    linear_combination 1 * h5 + (-1) * h12 + 2 * h59 + 1 * h164 + (-2) * h173
  · change c 0 17=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h10 + (2/3 : ℝ) * h38 + (-2/3 : ℝ) * h88
  · change c 0 18=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h200 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 0 19=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h14 + (2/3 : ℝ) * h40 + (-2/3 : ℝ) * h89
  · change c 0 20=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1) * h61 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (-1/2 : ℝ) * h165 + (1/2 : ℝ) * h168 + 1 * h174 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h200 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 1 0=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h0
  · change c 1 1=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h1 + (-1/3 : ℝ) * h24 + (1/3 : ℝ) * h84
  · change c 1 2=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h2 + (-1/3 : ℝ) * h25 + (1/3 : ℝ) * h85
  · change c 1 3=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h3 + (1/3 : ℝ) * h22 + (1/3 : ℝ) * h86
  · change c 1 4=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h4 + (1/3 : ℝ) * h23 + (1/3 : ℝ) * h87
  · change c 1 5=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h5
  · change c 1 6=(2*c 0 0)*0
    linear_combination 1 * h0 + (-1/2 : ℝ) * h6 + (-1) * h15 + 1 * h45 + (1/2 : ℝ) * h160 + (-1) * h170
  · change c 1 7=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h7 + (-1/2 : ℝ) * h16 + (-1) * h66 + 1 * h136 + (-1) * h186 + (-1) * h202
  · change c 1 8=(2*c 0 0)*1
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + (1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 1 9=(2*c 0 0)*0
    linear_combination (-1) * h5 + (-1/2 : ℝ) * h9 + 1 * h12 + (-1) * h44 + (-1) * h59 + (1/2 : ℝ) * h163 + (-1/2 : ℝ) * h164 + 1 * h169 + 1 * h173
  · change c 1 10=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h10 + (-1/3 : ℝ) * h38 + (1/3 : ℝ) * h88
  · change c 1 11=(2*c 0 0)*0
    linear_combination (1/2 : ℝ) * h11 + (-1) * h20 + (-1) * h56 + (1/2 : ℝ) * h167 + 1 * h172
  · change c 1 12=(2*c 0 0)*0
    linear_combination (-1) * h5 + (1/2 : ℝ) * h12 + (-1) * h44 + (-1) * h59 + (1/2 : ℝ) * h163 + (-1/2 : ℝ) * h164 + 1 * h169 + 1 * h173
  · change c 1 13=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (1/2 : ℝ) * h43 + 1 * h65 + (1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + 1 * h201 + (1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 1 14=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h14 + (-1/3 : ℝ) * h40 + (1/3 : ℝ) * h89
  · change c 1 15=(2*c 0 0)*0
    linear_combination (-1) * h0 + (1/2 : ℝ) * h15 + (-1) * h45 + (-1/2 : ℝ) * h160 + 1 * h170
  · change c 1 16=(2*c 0 0)*0
    linear_combination 1 * h66 + (-1) * h136 + 1 * h186 + 1 * h202
  · change c 1 17=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h17 + (1/3 : ℝ) * h31 + (1/3 : ℝ) * h90
  · change c 1 18=(2*c 0 0)*0
    linear_combination (-1) * h11 + (-1/2 : ℝ) * h18 + 1 * h20 + 1 * h56 + (-1/2 : ℝ) * h167 + (-1) * h172
  · change c 1 19=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h19 + (1/3 : ℝ) * h35 + (1/3 : ℝ) * h91
  · change c 1 20=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h20
  · change c 2 0=(2*c 0 0)*0
    linear_combination 1 * h92
  · change c 2 1=(2*c 0 0)*0
    linear_combination (-1) * h0 + 1 * h15 + (-1) * h45 + (-1) * h160 + 1 * h170
  · change c 2 2=(2*c 0 0)*0
    linear_combination 1 * h46 + 1 * h66 + (-1) * h136 + (-1) * h171 + 1 * h186 + 1 * h202
  · change c 2 3=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 2 4=(2*c 0 0)*0
    linear_combination (1/2 : ℝ) * h5 + (-1/2 : ℝ) * h12 + 1 * h59 + (-1/2 : ℝ) * h163 + (1/2 : ℝ) * h164 + (-1) * h173
  · change c 2 5=(2*c 0 0)*0
    linear_combination 1 * h93
  · change c 2 6=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h50 + (1/3 : ℝ) * h94 + (2/3 : ℝ) * h101
  · change c 2 7=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h51 + (1/3 : ℝ) * h54 + (1/3 : ℝ) * h95 + (2/3 : ℝ) * h102
  · change c 2 8=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h48 + (2/3 : ℝ) * h57 + (-1/3 : ℝ) * h96
  · change c 2 9=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h49 + (1/3 : ℝ) * h58 + (1/3 : ℝ) * h97 + (-2/3 : ℝ) * h99
  · change c 2 10=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h5 + (1/2 : ℝ) * h12 + (-1) * h44 + (1/2 : ℝ) * h163 + (-1/2 : ℝ) * h164 + 1 * h169
  · change c 2 11=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h55 + (1/3 : ℝ) * h98 + (2/3 : ℝ) * h103
  · change c 2 12=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h49 + (1/3 : ℝ) * h58 + (-2/3 : ℝ) * h97 + (1/3 : ℝ) * h99
  · change c 2 13=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h53 + (2/3 : ℝ) * h60 + (-1/3 : ℝ) * h100
  · change c 2 14=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (1/2 : ℝ) * h43 + 1 * h61 + 1 * h65 + (1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (-1) * h174 + (1/2 : ℝ) * h175 + (1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + 1 * h201 + (1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 2 15=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h50 + (2/3 : ℝ) * h94 + (1/3 : ℝ) * h101
  · change c 2 16=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h51 + (-1/3 : ℝ) * h54 + (2/3 : ℝ) * h95 + (1/3 : ℝ) * h102
  · change c 2 17=(2*c 0 0)*0
    linear_combination 1 * h46 + 1 * h66 + (-1) * h136 + (1/2 : ℝ) * h161 + (-1/2 : ℝ) * h166 + (-1) * h171 + 1 * h186 + 1 * h202
  · change c 2 18=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h55 + (2/3 : ℝ) * h98 + (1/3 : ℝ) * h103
  · change c 2 19=(2*c 0 0)*0
    linear_combination (-1) * h11 + 1 * h20 + 1 * h56 + (-1) * h167 + (-1) * h172
  · change c 2 20=(2*c 0 0)*0
    linear_combination 1 * h104
  · change c 3 0=(2*c 0 0)*0
    linear_combination 1 * h105
  · change c 3 1=(2*c 0 0)*0
    linear_combination 1 * h136 + (-1) * h186
  · change c 3 2=(2*c 0 0)*0
    linear_combination 1 * h73 + 1 * h137 + (-1) * h187 + (-1) * h189 + (-1) * h195
  · change c 3 3=(2*c 0 0)*0
    linear_combination (1/2 : ℝ) * h138 + 1 * h184 + (-1) * h191
  · change c 3 4=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (1/2 : ℝ) * h43 + (1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + (1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 3 5=(2*c 0 0)*0
    linear_combination 1 * h106
  · change c 3 6=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h71 + (1/3 : ℝ) * h107 + (2/3 : ℝ) * h114
  · change c 3 7=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h72 + (1/3 : ℝ) * h75 + (1/3 : ℝ) * h108 + (2/3 : ℝ) * h115
  · change c 3 8=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h69 + (2/3 : ℝ) * h78 + (-1/3 : ℝ) * h109
  · change c 3 9=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h70 + (1/3 : ℝ) * h79 + (1/3 : ℝ) * h110 + (-2/3 : ℝ) * h112
  · change c 3 10=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (1/2 : ℝ) * h43 + (1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 3 11=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h76 + (1/3 : ℝ) * h111 + (2/3 : ℝ) * h116
  · change c 3 12=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h70 + (1/3 : ℝ) * h79 + (-2/3 : ℝ) * h110 + (1/3 : ℝ) * h112
  · change c 3 13=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h74 + (2/3 : ℝ) * h81 + (-1/3 : ℝ) * h113
  · change c 3 14=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h142 + (-1) * h188 + 1 * h193
  · change c 3 15=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h71 + (2/3 : ℝ) * h107 + (1/3 : ℝ) * h114
  · change c 3 16=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h72 + (-1/3 : ℝ) * h75 + (2/3 : ℝ) * h108 + (1/3 : ℝ) * h115
  · change c 3 17=(2*c 0 0)*0
    linear_combination (-1) * h73 + 1 * h195
  · change c 3 18=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h76 + (2/3 : ℝ) * h111 + (1/3 : ℝ) * h116
  · change c 3 19=(2*c 0 0)*0
    linear_combination 1 * h141 + (-1) * h190
  · change c 3 20=(2*c 0 0)*0
    linear_combination 1 * h117
  · change c 4 0=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1) * h21
  · change c 4 1=(2*c 0 0)*0
    linear_combination (2/3 : ℝ) * h3 + (-2/3 : ℝ) * h22 + (1/3 : ℝ) * h86
  · change c 4 2=(2*c 0 0)*0
    linear_combination (2/3 : ℝ) * h4 + (-2/3 : ℝ) * h23 + (1/3 : ℝ) * h87
  · change c 4 3=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h1 + (-2/3 : ℝ) * h24 + (-1/3 : ℝ) * h84
  · change c 4 4=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h2 + (-2/3 : ℝ) * h25 + (-1/3 : ℝ) * h85
  · change c 4 5=(2*c 0 0)*0
    linear_combination (-3/4 : ℝ) * h26 + (-1/2 : ℝ) * h46 + (-1/2 : ℝ) * h66 + (1/4 : ℝ) * h136 + (-1/4 : ℝ) * h141 + (-1/8 : ℝ) * h161 + (1/8 : ℝ) * h166 + (1/2 : ℝ) * h171 + (1/4 : ℝ) * h176 + (-1/4 : ℝ) * h186 + (1/4 : ℝ) * h190 + (-1/2 : ℝ) * h202 + (1/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 4 6=(2*c 0 0)*(-1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h8 + (1/2 : ℝ) * h21 + (-1) * h27 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h162 + (1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 4 7=(2*c 0 0)*0
    linear_combination 1 * h5 + (1/2 : ℝ) * h9 + (-1/2 : ℝ) * h12 + (-1) * h28 + 2 * h59 + 1 * h164 + (-2) * h173
  · change c 4 8=(2*c 0 0)*0
    linear_combination 2 * h0 + (-1) * h6 + (-1) * h15 + (-1) * h29 + 2 * h45 + 1 * h160 + (-2) * h170
  · change c 4 9=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h7 + (1/2 : ℝ) * h16 + (-1/4 : ℝ) * h26 + (-1) * h30 + (-3/2 : ℝ) * h46 + (-3/2 : ℝ) * h66 + (7/4 : ℝ) * h136 + (1/4 : ℝ) * h141 + (-7/8 : ℝ) * h161 + (-1/8 : ℝ) * h166 + (3/2 : ℝ) * h171 + (-1/4 : ℝ) * h176 + (-7/4 : ℝ) * h186 + (-1/4 : ℝ) * h190 + (-3/2 : ℝ) * h202 + (-1/4 : ℝ) * h205 + (-1/4 : ℝ) * h208
  · change c 4 10=(2*c 0 0)*0
    linear_combination (2/3 : ℝ) * h17 + (-2/3 : ℝ) * h31 + (1/3 : ℝ) * h90
  · change c 4 11=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + (-1/2 : ℝ) * h21 + (-1) * h32 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h200 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 4 12=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h7 + (-1/2 : ℝ) * h16 + (1/4 : ℝ) * h26 + (-1) * h33 + (3/2 : ℝ) * h46 + (-1/2 : ℝ) * h66 + (1/4 : ℝ) * h136 + (-1/4 : ℝ) * h141 + (7/8 : ℝ) * h161 + (1/8 : ℝ) * h166 + (-3/2 : ℝ) * h171 + (1/4 : ℝ) * h176 + (-1/4 : ℝ) * h186 + (1/4 : ℝ) * h190 + (-1/2 : ℝ) * h202 + (1/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 4 13=(2*c 0 0)*0
    linear_combination 1 * h11 + 1 * h18 + (-2) * h20 + (-1) * h34 + (-2) * h56 + 1 * h167 + 2 * h172
  · change c 4 14=(2*c 0 0)*0
    linear_combination (2/3 : ℝ) * h19 + (-2/3 : ℝ) * h35 + (1/3 : ℝ) * h91
  · change c 4 15=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1) * h36 + (-1) * h43 + (1/2 : ℝ) * h162 + 1 * h168
  · change c 4 16=(2*c 0 0)*0
    linear_combination (-1) * h5 + (-1/2 : ℝ) * h9 + (1/2 : ℝ) * h12 + (-1) * h37 + (-2) * h44 + 1 * h163 + 2 * h169
  · change c 4 17=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h10 + (-2/3 : ℝ) * h38 + (-1/3 : ℝ) * h88
  · change c 4 18=(2*c 0 0)*(-1/2 : ℝ)
    linear_combination (-1) * h39 + 1 * h65 + (1/2 : ℝ) * h200 + 1 * h201
  · change c 4 19=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h14 + (-2/3 : ℝ) * h40 + (-1/3 : ℝ) * h89
  · change c 4 20=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + (-1/2 : ℝ) * h21 + (-1) * h41 + (-1/2 : ℝ) * h43 + (-1) * h61 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (-1/2 : ℝ) * h165 + (1/2 : ℝ) * h168 + 1 * h174 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h200 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 5 0=(2*c 0 0)*0
    linear_combination (-1) * h42
  · change c 5 1=(2*c 0 0)*1
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + (1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 5 2=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h5 + (1/2 : ℝ) * h12 + (-1) * h44 + (-1) * h59 + (1/2 : ℝ) * h163 + (-1/2 : ℝ) * h164 + 1 * h173
  · change c 5 3=(2*c 0 0)*0
    linear_combination (-1) * h0 + 1 * h15 + (-2) * h45 + (-1) * h160 + 1 * h170
  · change c 5 4=(2*c 0 0)*0
    linear_combination 1 * h66 + (-1) * h136 + (-1) * h171 + 1 * h186 + 1 * h202
  · change c 5 5=(2*c 0 0)*0
    linear_combination (-1) * h47
  · change c 5 6=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h48 + (-2/3 : ℝ) * h57 + (1/3 : ℝ) * h96
  · change c 5 7=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h49 + (-2/3 : ℝ) * h58 + (1/3 : ℝ) * h97 + (1/3 : ℝ) * h99
  · change c 5 8=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h50 + (-2/3 : ℝ) * h94 + (2/3 : ℝ) * h101
  · change c 5 9=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h51 + (2/3 : ℝ) * h54 + (-1/3 : ℝ) * h95 + (1/3 : ℝ) * h102
  · change c 5 10=(2*c 0 0)*0
    linear_combination (-1) * h46 + (-1) * h52 + (-1) * h66 + 1 * h136 + (-1/2 : ℝ) * h161 + (1/2 : ℝ) * h166 + 1 * h171 + (-1) * h186 + (-1) * h202
  · change c 5 11=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h53 + (-2/3 : ℝ) * h60 + (1/3 : ℝ) * h100
  · change c 5 12=(2*c 0 0)*0
    linear_combination (2/3 : ℝ) * h51 + (-1/3 : ℝ) * h54 + (-1/3 : ℝ) * h95 + (1/3 : ℝ) * h102
  · change c 5 13=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h55 + (-2/3 : ℝ) * h98 + (2/3 : ℝ) * h103
  · change c 5 14=(2*c 0 0)*0
    linear_combination 1 * h11 + (-1) * h20 + (-2) * h56 + 1 * h167 + 1 * h172
  · change c 5 15=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h48 + (-1/3 : ℝ) * h57 + (-1/3 : ℝ) * h96
  · change c 5 16=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h49 + (-1/3 : ℝ) * h58 + (-1/3 : ℝ) * h97 + (-1/3 : ℝ) * h99
  · change c 5 17=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h5 + (1/2 : ℝ) * h12 + (-1) * h44 + (-1) * h59 + (1/2 : ℝ) * h163 + (-1/2 : ℝ) * h164 + 1 * h169
  · change c 5 18=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h53 + (-1/3 : ℝ) * h60 + (-1/3 : ℝ) * h100
  · change c 5 19=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (1/2 : ℝ) * h43 + 1 * h65 + (1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (-1) * h174 + (1/2 : ℝ) * h175 + (1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + 1 * h201 + (1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 5 20=(2*c 0 0)*0
    linear_combination (-1) * h62
  · change c 6 0=(2*c 0 0)*0
    linear_combination (-1) * h63
  · change c 6 1=(2*c 0 0)*0
    linear_combination (-1) * h64 + (-1/2 : ℝ) * h138 + (-1) * h184 + 1 * h191
  · change c 6 2=(2*c 0 0)*1
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1) * h65 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 6 3=(2*c 0 0)*0
    linear_combination (-1) * h66 + 1 * h136 + (-1) * h186
  · change c 6 4=(2*c 0 0)*0
    linear_combination (-1) * h67 + 1 * h73 + 1 * h137 + (-1) * h187 + (-1) * h189 + (-1) * h195
  · change c 6 5=(2*c 0 0)*0
    linear_combination (-1) * h68
  · change c 6 6=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h69 + (-2/3 : ℝ) * h78 + (1/3 : ℝ) * h109
  · change c 6 7=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h70 + (-2/3 : ℝ) * h79 + (1/3 : ℝ) * h110 + (1/3 : ℝ) * h112
  · change c 6 8=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h71 + (-2/3 : ℝ) * h107 + (2/3 : ℝ) * h114
  · change c 6 9=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h72 + (2/3 : ℝ) * h75 + (-1/3 : ℝ) * h108 + (1/3 : ℝ) * h115
  · change c 6 10=(2*c 0 0)*0
    linear_combination (-1) * h195
  · change c 6 11=(2*c 0 0)*0
    linear_combination (-1/3 : ℝ) * h74 + (-2/3 : ℝ) * h81 + (1/3 : ℝ) * h113
  · change c 6 12=(2*c 0 0)*0
    linear_combination (2/3 : ℝ) * h72 + (-1/3 : ℝ) * h75 + (-1/3 : ℝ) * h108 + (1/3 : ℝ) * h115
  · change c 6 13=(2*c 0 0)*0
    linear_combination (1/3 : ℝ) * h76 + (-2/3 : ℝ) * h111 + (2/3 : ℝ) * h116
  · change c 6 14=(2*c 0 0)*0
    linear_combination (-1) * h77 + (-1) * h141 + 1 * h190
  · change c 6 15=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h69 + (-1/3 : ℝ) * h78 + (-1/3 : ℝ) * h109
  · change c 6 16=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h70 + (-1/3 : ℝ) * h79 + (-1/3 : ℝ) * h110 + (-1/3 : ℝ) * h112
  · change c 6 17=(2*c 0 0)*(-1)
    linear_combination (1/2 : ℝ) * h21 + (1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (-1/2 : ℝ) * h168 + (1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 6 18=(2*c 0 0)*0
    linear_combination (-2/3 : ℝ) * h74 + (-1/3 : ℝ) * h81 + (-1/3 : ℝ) * h113
  · change c 6 19=(2*c 0 0)*0
    linear_combination (-1) * h82 + (-1/2 : ℝ) * h142 + (-1) * h188 + 1 * h193
  · change c 6 20=(2*c 0 0)*0
    linear_combination (-1) * h83
  · change c 7 0=(2*c 0 0)*(-1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (1/2 : ℝ) * h207
  · change c 7 1=(2*c 0 0)*0
    linear_combination 1 * h120
  · change c 7 2=(2*c 0 0)*0
    linear_combination 1 * h121
  · change c 7 3=(2*c 0 0)*0
    linear_combination (-1) * h118
  · change c 7 4=(2*c 0 0)*0
    linear_combination (-1) * h119
  · change c 7 5=(2*c 0 0)*0
    linear_combination (1/4 : ℝ) * h26 + (3/2 : ℝ) * h46 + (3/2 : ℝ) * h66 + (-7/4 : ℝ) * h136 + (-1/4 : ℝ) * h141 + (3/8 : ℝ) * h161 + (-3/8 : ℝ) * h166 + (-3/2 : ℝ) * h171 + (-3/4 : ℝ) * h176 + (7/4 : ℝ) * h186 + (1/4 : ℝ) * h190 + (3/2 : ℝ) * h202 + (1/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 7 6=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h8 + (-1) * h43 + (1/2 : ℝ) * h162 + 1 * h168 + (-1) * h177
  · change c 7 7=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h5 + (1/2 : ℝ) * h12 + (-1) * h44 + (1/2 : ℝ) * h163 + (1/2 : ℝ) * h164 + 1 * h169 + (-1) * h178
  · change c 7 8=(2*c 0 0)*0
    linear_combination (-1) * h122
  · change c 7 9=(2*c 0 0)*0
    linear_combination 1 * h16 + (-1/4 : ℝ) * h26 + (-3/2 : ℝ) * h46 + (1/2 : ℝ) * h66 + (-1/4 : ℝ) * h136 + (1/4 : ℝ) * h141 + (-7/8 : ℝ) * h161 + (-1/8 : ℝ) * h166 + (3/2 : ℝ) * h171 + (-1/4 : ℝ) * h176 + (-1) * h179 + (1/4 : ℝ) * h186 + (-1/4 : ℝ) * h190 + (1/2 : ℝ) * h202 + (-1/4 : ℝ) * h205 + (-1/4 : ℝ) * h208
  · change c 7 10=(2*c 0 0)*0
    linear_combination 1 * h130
  · change c 7 11=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1) * h61 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + 1 * h174 + (-1/2 : ℝ) * h175 + (-1) * h180 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h200 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 7 12=(2*c 0 0)*0
    linear_combination (-1) * h16 + (1/4 : ℝ) * h26 + (3/2 : ℝ) * h46 + (-1/2 : ℝ) * h66 + (-1) * h123 + (1/4 : ℝ) * h136 + (-1/4 : ℝ) * h141 + (7/8 : ℝ) * h161 + (1/8 : ℝ) * h166 + (-3/2 : ℝ) * h171 + (1/4 : ℝ) * h176 + 1 * h179 + (-1/4 : ℝ) * h186 + (1/4 : ℝ) * h190 + (-1/2 : ℝ) * h202 + (1/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 7 13=(2*c 0 0)*0
    linear_combination (-1) * h127
  · change c 7 14=(2*c 0 0)*0
    linear_combination 1 * h131
  · change c 7 15=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h8 + (-1) * h43 + (-1/2 : ℝ) * h124 + (1/2 : ℝ) * h162 + 1 * h168 + (-1) * h177
  · change c 7 16=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h5 + (1/2 : ℝ) * h12 + (-1) * h44 + (-1) * h125 + (1/2 : ℝ) * h163 + (1/2 : ℝ) * h164 + 1 * h169 + (-1) * h178
  · change c 7 17=(2*c 0 0)*0
    linear_combination (-1) * h126
  · change c 7 18=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1) * h61 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h128 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + 1 * h174 + (-1/2 : ℝ) * h175 + (-1) * h180 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h200 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 7 19=(2*c 0 0)*0
    linear_combination (-1) * h129
  · change c 7 20=(2*c 0 0)*(-1/2 : ℝ)
    linear_combination (1/2 : ℝ) * h13 + 1 * h65 + (-1/2 : ℝ) * h165 + (-1) * h181 + (1/2 : ℝ) * h200 + 1 * h201
  · change c 8 0=(2*c 0 0)*0
    linear_combination (1/2 : ℝ) * h138 + (-1) * h182 + 1 * h184 + (-1) * h191
  · change c 8 1=(2*c 0 0)*0
    linear_combination 1 * h134
  · change c 8 2=(2*c 0 0)*0
    linear_combination 1 * h135
  · change c 8 3=(2*c 0 0)*0
    linear_combination (-1) * h132
  · change c 8 4=(2*c 0 0)*0
    linear_combination (-1) * h133
  · change c 8 5=(2*c 0 0)*0
    linear_combination 1 * h137 + (-1) * h183 + (-1) * h187 + (-1) * h189
  · change c 8 6=(2*c 0 0)*0
    linear_combination (-1) * h184
  · change c 8 7=(2*c 0 0)*1
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 8 8=(2*c 0 0)*0
    linear_combination (-1) * h136
  · change c 8 9=(2*c 0 0)*0
    linear_combination (-1) * h187
  · change c 8 10=(2*c 0 0)*0
    linear_combination 1 * h144
  · change c 8 11=(2*c 0 0)*0
    linear_combination (1/2 : ℝ) * h142 + (-1) * h193
  · change c 8 12=(2*c 0 0)*0
    linear_combination (-1) * h137 + 1 * h187
  · change c 8 13=(2*c 0 0)*0
    linear_combination (-1) * h141
  · change c 8 14=(2*c 0 0)*0
    linear_combination 1 * h145
  · change c 8 15=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h138 + (-1) * h184
  · change c 8 16=(2*c 0 0)*1
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (-1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (-1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 8 17=(2*c 0 0)*0
    linear_combination (-1) * h140
  · change c 8 18=(2*c 0 0)*0
    linear_combination (-1) * h193
  · change c 8 19=(2*c 0 0)*0
    linear_combination (-1) * h143
  · change c 8 20=(2*c 0 0)*0
    linear_combination (-1/2 : ℝ) * h142 + (-1) * h188 + 1 * h193 + (-1) * h194
  · change c 9 0=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 9 1=(2*c 0 0)*0
    linear_combination 1 * h148
  · change c 9 2=(2*c 0 0)*0
    linear_combination 1 * h149
  · change c 9 3=(2*c 0 0)*0
    linear_combination (-1) * h146
  · change c 9 4=(2*c 0 0)*0
    linear_combination (-1) * h147
  · change c 9 5=(2*c 0 0)*0
    linear_combination (-1/4 : ℝ) * h26 + (1/2 : ℝ) * h46 + (1/2 : ℝ) * h66 + (-5/4 : ℝ) * h136 + (-3/4 : ℝ) * h141 + (1/8 : ℝ) * h161 + (-1/8 : ℝ) * h166 + (-1/2 : ℝ) * h171 + (-1/4 : ℝ) * h176 + (5/4 : ℝ) * h186 + (3/4 : ℝ) * h190 + (1/2 : ℝ) * h202 + (3/4 : ℝ) * h205 + (-1/4 : ℝ) * h208
  · change c 9 6=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h152 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h197 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 9 7=(2*c 0 0)*0
    linear_combination 1 * h153 + 1 * h198
  · change c 9 8=(2*c 0 0)*0
    linear_combination (-1) * h150
  · change c 9 9=(2*c 0 0)*0
    linear_combination (1/4 : ℝ) * h26 + (-1/2 : ℝ) * h46 + (-1/2 : ℝ) * h66 + (5/4 : ℝ) * h136 + (3/4 : ℝ) * h141 + (-1) * h151 + (-1/8 : ℝ) * h161 + (1/8 : ℝ) * h166 + (1/2 : ℝ) * h171 + (1/4 : ℝ) * h176 + (-5/4 : ℝ) * h186 + (-3/4 : ℝ) * h190 + (-1) * h196 + (-1/2 : ℝ) * h202 + (-3/4 : ℝ) * h205 + (1/4 : ℝ) * h208
  · change c 9 10=(2*c 0 0)*0
    linear_combination 1 * h158
  · change c 9 11=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h13 + (-1) * h65 + (-1/2 : ℝ) * h200 + (-1) * h201 + 1 * h206
  · change c 9 12=(2*c 0 0)*0
    linear_combination (-1/4 : ℝ) * h26 + (1/2 : ℝ) * h46 + (1/2 : ℝ) * h66 + (-5/4 : ℝ) * h136 + (-3/4 : ℝ) * h141 + (1/8 : ℝ) * h161 + (-1/8 : ℝ) * h166 + (-1/2 : ℝ) * h171 + (-1/4 : ℝ) * h176 + (5/4 : ℝ) * h186 + (3/4 : ℝ) * h190 + 1 * h196 + (1/2 : ℝ) * h202 + (3/4 : ℝ) * h205 + (-1/4 : ℝ) * h208
  · change c 9 13=(2*c 0 0)*0
    linear_combination (-1) * h155
  · change c 9 14=(2*c 0 0)*0
    linear_combination 1 * h159
  · change c 9 15=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h21 + (-1/2 : ℝ) * h43 + (-1/2 : ℝ) * h80 + (-1/2 : ℝ) * h139 + (1/2 : ℝ) * h168 + (-1/2 : ℝ) * h175 + (-1/2 : ℝ) * h185 + (1/2 : ℝ) * h192 + (1/2 : ℝ) * h197 + (-1/2 : ℝ) * h203 + (1/2 : ℝ) * h204 + (-1/2 : ℝ) * h207
  · change c 9 16=(2*c 0 0)*0
    linear_combination 1 * h198
  · change c 9 17=(2*c 0 0)*0
    linear_combination (-1) * h154
  · change c 9 18=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h13 + (-1) * h65 + (-1/2 : ℝ) * h156 + (-1/2 : ℝ) * h200 + (-1) * h201 + 1 * h206
  · change c 9 19=(2*c 0 0)*0
    linear_combination (-1) * h157
  · change c 9 20=(2*c 0 0)*(1/2 : ℝ)
    linear_combination (-1/2 : ℝ) * h13 + (-1) * h65 + (-1/2 : ℝ) * h199 + (-1/2 : ℝ) * h200 + (-1) * h201 + 1 * h206

#print axioms coefficient_recovery
end
end PDTQuadraticSource
