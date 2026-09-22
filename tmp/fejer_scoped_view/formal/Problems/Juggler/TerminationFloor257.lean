import Problems.Juggler.Termination

namespace Problems.Juggler

/-!
# Residual floors 257 and 261

Every positive integer strictly below 257 reaches 1, and the
two extra odd seeds 257 and 259 raise the floor to 261.
Evens below 2809 already reduce to {1,…,52}.
This is a finite certificate, not a halt theorem.
Combined with cycleMin_finance the floor 261 excludes the
cheap leftovers 57 and 76, so the named leftover is 84.
-/

theorem reachesOne_n53 : ReachesOne 53 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n55 : ReachesOne 55 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n57 : ReachesOne 57 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n59 : ReachesOne 59 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n61 : ReachesOne 61 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n63 : ReachesOne 63 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n65 : ReachesOne 65 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n67 : ReachesOne 67 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n69 : ReachesOne 69 :=
  ⟨14, by decide +kernel⟩

theorem reachesOne_n71 : ReachesOne 71 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n73 : ReachesOne 73 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n75 : ReachesOne 75 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n77 : ReachesOne 77 :=
  ⟨19, by decide +kernel⟩

theorem reachesOne_n79 : ReachesOne 79 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n81 : ReachesOne 81 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n83 : ReachesOne 83 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n85 : ReachesOne 85 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n87 : ReachesOne 87 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n89 : ReachesOne 89 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n91 : ReachesOne 91 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n93 : ReachesOne 93 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n95 : ReachesOne 95 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n97 : ReachesOne 97 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n99 : ReachesOne 99 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n101 : ReachesOne 101 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n103 : ReachesOne 103 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n105 : ReachesOne 105 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n107 : ReachesOne 107 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n109 : ReachesOne 109 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n111 : ReachesOne 111 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n113 : ReachesOne 113 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n115 : ReachesOne 115 :=
  ⟨19, by decide +kernel⟩

theorem reachesOne_n117 : ReachesOne 117 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n119 : ReachesOne 119 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n121 : ReachesOne 121 :=
  ⟨11, by decide +kernel⟩

theorem reachesOne_n123 : ReachesOne 123 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n125 : ReachesOne 125 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n127 : ReachesOne 127 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n129 : ReachesOne 129 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n131 : ReachesOne 131 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n133 : ReachesOne 133 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n135 : ReachesOne 135 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n137 : ReachesOne 137 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n139 : ReachesOne 139 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n141 : ReachesOne 141 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n143 : ReachesOne 143 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n145 : ReachesOne 145 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n147 : ReachesOne 147 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n149 : ReachesOne 149 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n151 : ReachesOne 151 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n153 : ReachesOne 153 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n155 : ReachesOne 155 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n157 : ReachesOne 157 :=
  ⟨10, by decide +kernel⟩

theorem reachesOne_n159 : ReachesOne 159 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n161 : ReachesOne 161 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n163 : ReachesOne 163 :=
  ⟨43, by decide +kernel⟩

theorem reachesOne_n165 : ReachesOne 165 :=
  ⟨27, by decide +kernel⟩

theorem reachesOne_n167 : ReachesOne 167 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n169 : ReachesOne 169 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n171 : ReachesOne 171 :=
  ⟨8, by decide +kernel⟩

theorem reachesOne_n173 : ReachesOne 173 :=
  ⟨32, by decide +kernel⟩

theorem reachesOne_n175 : ReachesOne 175 :=
  ⟨24, by decide +kernel⟩

theorem reachesOne_n177 : ReachesOne 177 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n179 : ReachesOne 179 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n181 : ReachesOne 181 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n183 : ReachesOne 183 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n185 : ReachesOne 185 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n187 : ReachesOne 187 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n189 : ReachesOne 189 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n191 : ReachesOne 191 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n193 : ReachesOne 193 :=
  ⟨73, by decide +kernel⟩

theorem reachesOne_n195 : ReachesOne 195 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n197 : ReachesOne 197 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n199 : ReachesOne 199 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n201 : ReachesOne 201 :=
  ⟨15, by decide +kernel⟩

theorem reachesOne_n203 : ReachesOne 203 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n205 : ReachesOne 205 :=
  ⟨18, by decide +kernel⟩

theorem reachesOne_n207 : ReachesOne 207 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n209 : ReachesOne 209 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n211 : ReachesOne 211 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n213 : ReachesOne 213 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n215 : ReachesOne 215 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n217 : ReachesOne 217 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n219 : ReachesOne 219 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n221 : ReachesOne 221 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n223 : ReachesOne 223 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n225 : ReachesOne 225 :=
  ⟨16, by decide +kernel⟩

theorem reachesOne_n227 : ReachesOne 227 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n229 : ReachesOne 229 :=
  ⟨32, by decide +kernel⟩

theorem reachesOne_n231 : ReachesOne 231 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n233 : ReachesOne 233 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n235 : ReachesOne 235 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n237 : ReachesOne 237 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n239 : ReachesOne 239 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n241 : ReachesOne 241 :=
  ⟨40, by decide +kernel⟩

theorem reachesOne_n243 : ReachesOne 243 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n245 : ReachesOne 245 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n247 : ReachesOne 247 :=
  ⟨13, by decide +kernel⟩

theorem reachesOne_n249 : ReachesOne 249 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n251 : ReachesOne 251 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n253 : ReachesOne 253 :=
  ⟨7, by decide +kernel⟩

theorem reachesOne_n255 : ReachesOne 255 :=
  ⟨7, by decide +kernel⟩

/-- Every positive residual strictly below 257 is ReachesOne.
This is a finite certificate, not a halt theorem. Combined with
cycleMin_finance it excludes cycle length 19. -/
theorem reachesOne_of_lt_two_hundred_fifty_seven {y : ℕ}
    (hpos : 1 ≤ y) (hy : y < 257) : ReachesOne y := by
  cases Nat.mod_two_eq_zero_or_one y with
  | inl heven =>
      exact even_lt_sq_fifty_three_reachesOne heven hpos
        (lt_trans hy (by norm_num : (257 : ℕ) < 2809))
  | inr hodd =>
      interval_cases y <;> first
        | exact reachesOne_one
        | exact three_reachesOne
        | exact five_reachesOne
        | exact seven_reachesOne
        | exact nine_reachesOne
        | exact eleven_reachesOne
        | exact thirteen_reachesOne
        | exact fifteen_reachesOne
        | exact seventeen_reachesOne
        | exact nineteen_reachesOne
        | exact twentyone_reachesOne
        | exact twentythree_reachesOne
        | exact twentyfive_reachesOne
        | exact twentyseven_reachesOne
        | exact twentynine_reachesOne
        | exact thirtyone_reachesOne
        | exact thirtythree_reachesOne
        | exact thirtyfive_reachesOne
        | exact thirtyseven_reachesOne
        | exact thirtynine_reachesOne
        | exact fortyone_reachesOne
        | exact fortythree_reachesOne
        | exact fortyfive_reachesOne
        | exact fortyseven_reachesOne
        | exact fortynine_reachesOne
        | exact fiftyone_reachesOne
        | exact reachesOne_n53
        | exact reachesOne_n55
        | exact reachesOne_n57
        | exact reachesOne_n59
        | exact reachesOne_n61
        | exact reachesOne_n63
        | exact reachesOne_n65
        | exact reachesOne_n67
        | exact reachesOne_n69
        | exact reachesOne_n71
        | exact reachesOne_n73
        | exact reachesOne_n75
        | exact reachesOne_n77
        | exact reachesOne_n79
        | exact reachesOne_n81
        | exact reachesOne_n83
        | exact reachesOne_n85
        | exact reachesOne_n87
        | exact reachesOne_n89
        | exact reachesOne_n91
        | exact reachesOne_n93
        | exact reachesOne_n95
        | exact reachesOne_n97
        | exact reachesOne_n99
        | exact reachesOne_n101
        | exact reachesOne_n103
        | exact reachesOne_n105
        | exact reachesOne_n107
        | exact reachesOne_n109
        | exact reachesOne_n111
        | exact reachesOne_n113
        | exact reachesOne_n115
        | exact reachesOne_n117
        | exact reachesOne_n119
        | exact reachesOne_n121
        | exact reachesOne_n123
        | exact reachesOne_n125
        | exact reachesOne_n127
        | exact reachesOne_n129
        | exact reachesOne_n131
        | exact reachesOne_n133
        | exact reachesOne_n135
        | exact reachesOne_n137
        | exact reachesOne_n139
        | exact reachesOne_n141
        | exact reachesOne_n143
        | exact reachesOne_n145
        | exact reachesOne_n147
        | exact reachesOne_n149
        | exact reachesOne_n151
        | exact reachesOne_n153
        | exact reachesOne_n155
        | exact reachesOne_n157
        | exact reachesOne_n159
        | exact reachesOne_n161
        | exact reachesOne_n163
        | exact reachesOne_n165
        | exact reachesOne_n167
        | exact reachesOne_n169
        | exact reachesOne_n171
        | exact reachesOne_n173
        | exact reachesOne_n175
        | exact reachesOne_n177
        | exact reachesOne_n179
        | exact reachesOne_n181
        | exact reachesOne_n183
        | exact reachesOne_n185
        | exact reachesOne_n187
        | exact reachesOne_n189
        | exact reachesOne_n191
        | exact reachesOne_n193
        | exact reachesOne_n195
        | exact reachesOne_n197
        | exact reachesOne_n199
        | exact reachesOne_n201
        | exact reachesOne_n203
        | exact reachesOne_n205
        | exact reachesOne_n207
        | exact reachesOne_n209
        | exact reachesOne_n211
        | exact reachesOne_n213
        | exact reachesOne_n215
        | exact reachesOne_n217
        | exact reachesOne_n219
        | exact reachesOne_n221
        | exact reachesOne_n223
        | exact reachesOne_n225
        | exact reachesOne_n227
        | exact reachesOne_n229
        | exact reachesOne_n231
        | exact reachesOne_n233
        | exact reachesOne_n235
        | exact reachesOne_n237
        | exact reachesOne_n239
        | exact reachesOne_n241
        | exact reachesOne_n243
        | exact reachesOne_n245
        | exact reachesOne_n247
        | exact reachesOne_n249
        | exact reachesOne_n251
        | exact reachesOne_n253
        | exact reachesOne_n255
        | omega

/-- A positive non-ReachesOne value cannot lie in {1,…,256}. -/
theorem non_reachesOne_ge_two_hundred_fifty_seven {n : ℕ}
    (hn : 1 ≤ n) (hfail : ¬ReachesOne n) : 257 ≤ n := by
  by_contra h
  exact hfail (reachesOne_of_lt_two_hundred_fifty_seven hn (Nat.not_le.mp h))

theorem reachesOne_n257 : ReachesOne 257 :=
  ⟨5, by decide +kernel⟩

theorem reachesOne_n259 : ReachesOne 259 :=
  ⟨5, by decide +kernel⟩

/-- Every positive residual strictly below 261 is ReachesOne.
Two extra odd seeds; evens below 261 already reduce via
`even_lt_sq_fifty_three`. Combined with cycleMin_finance this
excludes the cheap leftovers 57 and 76, so the named leftover
is the record near-convergent 84. -/
theorem reachesOne_of_lt_two_hundred_sixty_one {y : ℕ}
    (hpos : 1 ≤ y) (hy : y < 261) : ReachesOne y := by
  rcases Nat.lt_or_ge y 257 with h257 | h257
  · exact reachesOne_of_lt_two_hundred_fifty_seven hpos h257
  · cases Nat.mod_two_eq_zero_or_one y with
    | inl heven =>
        exact even_lt_sq_fifty_three_reachesOne heven hpos
          (lt_trans hy (by norm_num : (261 : ℕ) < 2809))
    | inr hodd =>
        have hsplit : y = 257 ∨ y = 259 := by omega
        rcases hsplit with h | h
        · simpa [h] using reachesOne_n257
        · simpa [h] using reachesOne_n259

/-- A positive non-ReachesOne value cannot lie in {1,…,260}. -/
theorem non_reachesOne_ge_two_hundred_sixty_one {n : ℕ}
    (hn : 1 ≤ n) (hfail : ¬ReachesOne n) : 261 ≤ n := by
  by_contra h
  exact hfail (reachesOne_of_lt_two_hundred_sixty_one hn (Nat.not_le.mp h))

end Problems.Juggler
