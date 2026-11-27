import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_650_aux


def rot (s word : Nat) : Nat :=
  ((word <<< (s % 17)) ||| (word >>> (17 - s % 17))) % 2 ^ 17

def step (word : Nat) : Nat :=
  (List.range 17).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17))).toNat <<< b)) 0

def fstep (w : Nat) : Nat :=
  (w % 2 ^ 17) ^^^ ((rot 16 (w % 2 ^ 17) ^^^ (2 ^ 17 - 1)) &&& rot 15 (w % 2 ^ 17))

def outputG (st : Nat → Nat) (w : Nat) : Nat :=
  ((List.range 4).foldl (fun x t =>
    st (x ^^^ rot 1 x ^^^ rot (17 - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (17 + (t + 1)) % 2 ^ 17)) (rot 1 w)) >>> 8

def cstateG (st : Nat → Nat) (key name : Nat) : Nat :=
  (List.range 4).foldl (fun state j =>
    st (state ^^^ rot 2 state ^^^ rot (17 - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (17 + (4 + (j + 1))) % 2 ^ 17))
    (rot 3 key ^^^ name)

def fout (w : Nat) : Nat := outputG fstep w

def fcs (key name : Nat) : Nat := cstateG fstep key name

def cnt (n m a : Nat) : Nat :=
  ((List.range n).filter (fun i => m.testBit i && a.testBit i)).length

def par (m a : Nat) : Bool :=
  ((List.range 17).filter (fun i => m.testBit i && a.testBit i)).length % 2 == 1

theorem foldl_bits (B : Nat → Bool) (n i : Nat) :
    ((List.range n).foldl (fun acc b => acc ||| ((B b).toNat <<< b)) 0).testBit i
      = (decide (i < n) && B i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih,
      Nat.testBit_shiftLeft]
    rcases lt_trichotomy i n with h | h | h
    · have h1 : ¬ n ≤ i := by omega
      have h2 : i < n + 1 := by omega
      simp [h, h1, h2]
    · subst h
      cases hB : B i <;> simp
    · have h1 : ¬ i < n := by omega
      have h2 : ¬ i < n + 1 := by omega
      obtain ⟨j, hj⟩ : ∃ j, i - n = j + 1 := ⟨i - n - 1, by omega⟩
      cases hB : B n <;> simp [h1, h2, hj, Nat.testBit_succ]

theorem rot_bit (s v i : Nat) (hs' : s < 17) (hv : v < 2 ^ 17) (hi : i < 17) :
    (rot s v).testBit i = v.testBit ((i + 17 - s) % 17) := by
  have hmod : s % 17 = s := Nat.mod_eq_of_lt hs'
  have hhi : ∀ j, 17 ≤ j → v.testBit j = false := by
    intro j hj
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))
  unfold rot
  rw [hmod, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s ≤ i
  · have e1 : (i + 17 - s) % 17 = i - s := by omega
    have e2 := hhi (17 - s + i) (by omega)
    simp [hi, h, e1, e2]
  · have e1 : (i + 17 - s) % 17 = 17 - s + i := by omega
    simp [hi, h, e1]

theorem step_eq (w : Nat) : step w = fstep w := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hv : w % 2 ^ 17 < 2 ^ 17 := Nat.mod_lt _ (by norm_num)
  unfold step fstep
  rw [foldl_bits (fun b => xor (w.testBit b)
    (!(w.testBit ((b + 1) % 17)) && w.testBit ((b + 2) % 17))) 17 i]
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor]
  by_cases hi : i < 17
  · rw [rot_bit 16 _ i (by norm_num) hv hi, rot_bit 15 _ i (by norm_num) hv hi]
    have e1 : (i + 17 - 16) % 17 = (i + 1) % 17 := by omega
    have e2 : (i + 17 - 15) % 17 = (i + 2) % 17 := by omega
    have m1 : (2 ^ 17 - 1 : Nat).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      simp [hi]
    rw [e1, e2, m1]
    simp only [Nat.testBit_mod_two_pow]
    have a1 : (i + 1) % 17 < 17 := Nat.mod_lt _ (by norm_num)
    have a2 : (i + 2) % 17 < 17 := Nat.mod_lt _ (by norm_num)
    simp [hi, a1, a2]
  · have hhi : ∀ x : Nat, x < 2 ^ 17 → x.testBit i = false := fun x hx =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have r1 : (rot 15 (w % 2 ^ 17)).testBit i = false :=
      hhi _ (by unfold rot; exact Nat.mod_lt _ (by norm_num))
    rw [hhi _ hv, r1]
    simp [hi]

theorem step_eq' : step = fstep := funext step_eq

theorem cnt_xor (n m a b : Nat) : cnt n m (a ^^^ b) % 2 = (cnt n m a + cnt n m b) % 2 := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    unfold cnt at ih ⊢
    simp only [Nat.testBit_xor] at ih
    simp only [List.range_succ, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil, Nat.testBit_xor]
    cases h1 : m.testBit n <;> cases h2 : a.testBit n <;> cases h3 : b.testBit n <;> simp <;> omega

theorem bool_par (x y z : Nat) (h : z % 2 = (x + y) % 2) :
    (z % 2 == 1) = xor (x % 2 == 1) (y % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
  rcases Nat.mod_two_eq_zero_or_one z with hz | hz <;>
  first
  | (exfalso; omega)
  | simp [hx, hy, hz]

theorem par_xor (m a b : Nat) : par m (a ^^^ b) = xor (par m a) (par m b) :=
  bool_par _ _ _ (cnt_xor 17 m a b)

def scanR (f : Nat → Bool) (base : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => f (base + n) && scanR f base n

theorem scanR_spec (f : Nat → Bool) (base : Nat) :
    ∀ n, scanR f base n = true → ∀ w, base ≤ w → w < base + n → f w = true := by
  intro n
  induction n with
  | zero => intro _ w h1 h2; omega
  | succ n ih =>
    intro h w h1 h2
    simp only [scanR, Bool.and_eq_true] at h
    by_cases hw : w = base + n
    · rw [hw]; exact h.1
    · exact ih h.2 w h1 (by omega)

def O : List Nat :=
  [600, 1664, 1679, 2013, 3861, 4589, 4814, 4898, 5278, 6040, 6178, 6240, 6995, 8903, 9681, 9748,
    9915, 10978, 11632, 11824, 12075, 12520, 13521, 15024, 15296, 15655, 16477, 16757, 16909,
    17856, 17898, 18343, 19140, 19400, 19776, 20112, 20370, 20900, 21159, 21259, 21596, 22768,
    22859, 23272, 25026, 25826, 26534, 26739, 26759, 27159, 27997, 28860, 28994, 30241, 30484,
    31133, 31948, 31998, 32661, 32663, 33044, 33090, 33183, 33518, 34823, 36669, 37350, 37494,
    40762, 41286, 41853, 42390, 42433, 42686, 43470, 44336, 44338, 44804, 44807, 45313, 45805,
    46833, 47926, 48987, 49759, 50405, 51043, 51223, 51256, 51297, 51443, 52160, 53526, 53668,
    53819, 53913, 53996, 54725, 54770, 54894, 55068, 55337, 55893, 56022, 56400, 56402, 57135,
    57217, 57336, 59433, 60642, 61836, 62296, 62429, 62932, 64261, 64939, 64944, 65676, 66245,
    66489, 66490, 68211, 68840, 69580, 69581, 69582, 71418, 71845, 71866, 72741, 73474, 73603,
    74872, 75728, 75842, 76159, 76509, 76714, 76740, 77905, 78182, 78249, 78883, 80936, 81356,
    81358, 81699, 82531, 83167, 83557, 85649, 85830, 86101, 86179, 87528, 88375, 88679, 90063,
    90184, 90569, 90780, 91543, 91857, 92256, 92297, 93301, 93398, 94488, 95016, 95197, 95349,
    96655, 97705, 98342, 98493, 98718, 98936, 99731, 100075, 100782, 101505, 102141, 102143,
    102857, 102859, 102887, 103265, 104153, 104222, 104373, 104891, 105199, 105433, 105540,
    106110, 106480, 106541, 106910, 107389, 107519, 107617, 108194, 109517, 110377, 111057,
    111804, 111895, 112246, 112249, 112833, 113200, 113359, 114004, 114113, 114230, 115329,
    115330, 115959, 116435, 116584, 116851, 117147, 117172, 117478, 117748, 118598, 118946,
    119285, 119286, 119371, 121023, 121205, 121597, 121599, 122724, 123471, 125265, 125342,
    125763, 126992, 127141, 127400, 127685, 127992, 128597, 129216, 129787, 129850]

def ZC : List (Nat × Nat) :=
  [(1241, 1049), (1659, 1296), (2313, 540), (3011, 815), (3241, 220), (3395, 12), (4906, 1715),
    (5098, 761), (8753, 898), (9546, 375), (9795, 64), (11251, 239), (11386, 199), (12371, 1130),
    (13203, 152), (13489, 420), (15560, 2049), (16411, 2), (19528, 853), (19883, 1021), (23130,
    244), (24384, 122), (26907, 82), (27952, 155), (28923, 40), (32834, 462), (33816, 2547),
    (34530, 734), (35672, 421), (38410, 2869), (38817, 314), (40265, 87), (40931, 1911), (41354,
    57), (41665, 113), (42641, 670), (44251, 12), (44872, 304), (47066, 952), (47312, 796),
    (48585, 220), (48744, 2575), (50091, 990), (50138, 2267), (52274, 718), (57898, 26), (59025,
    64), (59880, 1568), (60275, 134), (62113, 342), (62403, 45), (64171, 559), (64584, 58),
    (65104, 558), (66136, 273), (66954, 2712), (66993, 354), (67123, 3419), (68680, 514), (69009,
    180), (69704, 1847), (70443, 1882), (71177, 371), (72314, 509), (73579, 438), (74250, 461),
    (74505, 875), (74985, 28), (75107, 398), (75169, 623), (76896, 84), (77130, 370), (79491,
    972), (80835, 788), (80946, 742), (81451, 6292), (81779, 61), (84179, 1023), (84194, 179),
    (84721, 317), (85643, 45), (85754, 148), (86545, 257), (87240, 40), (87563, 282), (89443,
    162), (90488, 6), (91938, 276), (92706, 608), (93657, 720), (94873, 856), (95128, 1413),
    (96241, 875), (96753, 169), (96760, 902), (99770, 1771), (100216, 1732), (101203, 26),
    (102067, 1130), (103224, 1141), (103499, 930), (104265, 1700), (104497, 87), (104714, 1947),
    (106697, 2742), (108089, 356), (110082, 786), (110130, 2582), (110738, 534), (111915, 1106),
    (113010, 1800), (113321, 1077), (113833, 1861), (114056, 76), (115323, 1025), (115936, 792),
    (115970, 454), (119210, 1191), (119322, 46), (120345, 400), (124624, 480), (124944, 359),
    (126874, 440), (127040, 23), (129762, 131)]

def chk1 (w : Nat) : Bool := !(fout w == 0) || O.contains w

def good (w : Nat) : Bool :=
  match ZC.lookup w with
  | some c => decide (c < 131072) && decide (fcs w c < 256) &&
      O.all (fun o => !decide (fcs o c < 256))
  | none => false

def chk2 (w : Nat) : Bool :=
  w.testBit 2 || !decide (fcs w 0 < 256) || good w || (w == 11632)

theorem ca_0 : scanR chk1 0 8192 = true := by decide +kernel

theorem ca_1 : scanR chk1 8192 8192 = true := by decide +kernel

theorem ca_2 : scanR chk1 16384 8192 = true := by decide +kernel

theorem ca_3 : scanR chk1 24576 8192 = true := by decide +kernel

theorem ca_4 : scanR chk1 32768 8192 = true := by decide +kernel

theorem ca_5 : scanR chk1 40960 8192 = true := by decide +kernel

theorem ca_6 : scanR chk1 49152 8192 = true := by decide +kernel

theorem ca_7 : scanR chk1 57344 8192 = true := by decide +kernel

theorem ca_8 : scanR chk1 65536 8192 = true := by decide +kernel

theorem ca_9 : scanR chk1 73728 8192 = true := by decide +kernel

theorem ca_10 : scanR chk1 81920 8192 = true := by decide +kernel

theorem ca_11 : scanR chk1 90112 8192 = true := by decide +kernel

theorem ca_12 : scanR chk1 98304 8192 = true := by decide +kernel

theorem ca_13 : scanR chk1 106496 8192 = true := by decide +kernel

theorem ca_14 : scanR chk1 114688 8192 = true := by decide +kernel

theorem ca_15 : scanR chk1 122880 8192 = true := by decide +kernel

theorem all_chk1 (w : Nat) (hw : w < 131072) : chk1 w = true := by
  by_cases h0 : w < 8192
  · exact scanR_spec chk1 0 8192 ca_0 w (by omega) (by omega)
  by_cases h1 : w < 16384
  · exact scanR_spec chk1 8192 8192 ca_1 w (by omega) (by omega)
  by_cases h2 : w < 24576
  · exact scanR_spec chk1 16384 8192 ca_2 w (by omega) (by omega)
  by_cases h3 : w < 32768
  · exact scanR_spec chk1 24576 8192 ca_3 w (by omega) (by omega)
  by_cases h4 : w < 40960
  · exact scanR_spec chk1 32768 8192 ca_4 w (by omega) (by omega)
  by_cases h5 : w < 49152
  · exact scanR_spec chk1 40960 8192 ca_5 w (by omega) (by omega)
  by_cases h6 : w < 57344
  · exact scanR_spec chk1 49152 8192 ca_6 w (by omega) (by omega)
  by_cases h7 : w < 65536
  · exact scanR_spec chk1 57344 8192 ca_7 w (by omega) (by omega)
  by_cases h8 : w < 73728
  · exact scanR_spec chk1 65536 8192 ca_8 w (by omega) (by omega)
  by_cases h9 : w < 81920
  · exact scanR_spec chk1 73728 8192 ca_9 w (by omega) (by omega)
  by_cases h10 : w < 90112
  · exact scanR_spec chk1 81920 8192 ca_10 w (by omega) (by omega)
  by_cases h11 : w < 98304
  · exact scanR_spec chk1 90112 8192 ca_11 w (by omega) (by omega)
  by_cases h12 : w < 106496
  · exact scanR_spec chk1 98304 8192 ca_12 w (by omega) (by omega)
  by_cases h13 : w < 114688
  · exact scanR_spec chk1 106496 8192 ca_13 w (by omega) (by omega)
  by_cases h14 : w < 122880
  · exact scanR_spec chk1 114688 8192 ca_14 w (by omega) (by omega)
  exact scanR_spec chk1 122880 8192 ca_15 w (by omega) (by omega)

theorem cb_0 : scanR chk2 0 8192 = true := by decide +kernel

theorem cb_1 : scanR chk2 8192 8192 = true := by decide +kernel

theorem cb_2 : scanR chk2 16384 8192 = true := by decide +kernel

theorem cb_3 : scanR chk2 24576 8192 = true := by decide +kernel

theorem cb_4 : scanR chk2 32768 8192 = true := by decide +kernel

theorem cb_5 : scanR chk2 40960 8192 = true := by decide +kernel

theorem cb_6 : scanR chk2 49152 8192 = true := by decide +kernel

theorem cb_7 : scanR chk2 57344 8192 = true := by decide +kernel

theorem cb_8 : scanR chk2 65536 8192 = true := by decide +kernel

theorem cb_9 : scanR chk2 73728 8192 = true := by decide +kernel

theorem cb_10 : scanR chk2 81920 8192 = true := by decide +kernel

theorem cb_11 : scanR chk2 90112 8192 = true := by decide +kernel

theorem cb_12 : scanR chk2 98304 8192 = true := by decide +kernel

theorem cb_13 : scanR chk2 106496 8192 = true := by decide +kernel

theorem cb_14 : scanR chk2 114688 8192 = true := by decide +kernel

theorem cb_15 : scanR chk2 122880 8192 = true := by decide +kernel

theorem all_chk2 (w : Nat) (hw : w < 131072) : chk2 w = true := by
  by_cases h0 : w < 8192
  · exact scanR_spec chk2 0 8192 cb_0 w (by omega) (by omega)
  by_cases h1 : w < 16384
  · exact scanR_spec chk2 8192 8192 cb_1 w (by omega) (by omega)
  by_cases h2 : w < 24576
  · exact scanR_spec chk2 16384 8192 cb_2 w (by omega) (by omega)
  by_cases h3 : w < 32768
  · exact scanR_spec chk2 24576 8192 cb_3 w (by omega) (by omega)
  by_cases h4 : w < 40960
  · exact scanR_spec chk2 32768 8192 cb_4 w (by omega) (by omega)
  by_cases h5 : w < 49152
  · exact scanR_spec chk2 40960 8192 cb_5 w (by omega) (by omega)
  by_cases h6 : w < 57344
  · exact scanR_spec chk2 49152 8192 cb_6 w (by omega) (by omega)
  by_cases h7 : w < 65536
  · exact scanR_spec chk2 57344 8192 cb_7 w (by omega) (by omega)
  by_cases h8 : w < 73728
  · exact scanR_spec chk2 65536 8192 cb_8 w (by omega) (by omega)
  by_cases h9 : w < 81920
  · exact scanR_spec chk2 73728 8192 cb_9 w (by omega) (by omega)
  by_cases h10 : w < 90112
  · exact scanR_spec chk2 81920 8192 cb_10 w (by omega) (by omega)
  by_cases h11 : w < 98304
  · exact scanR_spec chk2 90112 8192 cb_11 w (by omega) (by omega)
  by_cases h12 : w < 106496
  · exact scanR_spec chk2 98304 8192 cb_12 w (by omega) (by omega)
  by_cases h13 : w < 114688
  · exact scanR_spec chk2 106496 8192 cb_13 w (by omega) (by omega)
  by_cases h14 : w < 122880
  · exact scanR_spec chk2 114688 8192 cb_14 w (by omega) (by omega)
  exact scanR_spec chk2 122880 8192 cb_15 w (by omega) (by omega)


theorem hO (w : Nat) (hw : w < 131072) (h0 : fout w = 0) : w ∈ O := by
  have h := all_chk1 w hw
  unfold chk1 at h
  rw [h0] at h
  simpa using h

theorem good_spec (w : Nat) (h : good w = true) :
    ∃ c, c < 2 ^ 17 ∧ fcs w c < 256 ∧ ∀ o ∈ O, ¬ fcs o c < 256 := by
  unfold good at h
  split at h
  · rename_i c _
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    exact ⟨c, by norm_num; exact h.1.1, h.1.2, h.2⟩
  · simp at h

theorem hZ (w : Nat) (hw : w < 131072) (hb : w.testBit 2 = false) (hp : fcs w 0 < 256) :
    w = 11632 ∨ ∃ c, c < 2 ^ 17 ∧ fcs w c < 256 ∧ ∀ o ∈ O, ¬ fcs o c < 256 := by
  have h := all_chk2 w hw
  unfold chk2 at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · rw [hb] at h
    simp at h
  · exact absurd hp h
  · exact Or.inr (good_spec w h)
  · exact Or.inl h

theorem hOb : ∀ o ∈ O, o.testBit 2 = true → ¬ fcs o 0 < 256 := by decide +kernel

theorem e0 : fout 11632 = 0 ∧ fcs 11632 0 < 256 := by decide +kernel

theorem t0 : fout (11632 ^^^ 12) = 203 := by decide +kernel

theorem t1 : (48808 : Nat).testBit 2 = false ∧ fout (48808 ^^^ 12) = 203 ∧ fcs 48808 379 < 256 ∧
    ∀ o ∈ O, ¬ fcs o 379 < 256 := by decide +kernel

theorem t2 : (80232 : Nat).testBit 2 = false ∧ fout (80232 ^^^ 12) = 203 ∧ fcs 80232 358 < 256 ∧
    ∀ o ∈ O, ¬ fcs o 358 < 256 := by decide +kernel

theorem t3 : (109232 : Nat).testBit 2 = false ∧ fout (109232 ^^^ 12) = 203 ∧ fcs 109232 2502 < 256 ∧
    ∀ o ∈ O, ¬ fcs o 2502 < 256 := by decide +kernel

theorem tx : (11632 ^^^ 12 : Nat) = (48808 ^^^ 12) ^^^ (80232 ^^^ 12) ^^^ (109232 ^^^ 12) := by
  decide +kernel

theorem xor3 (f : Bool → Bool) (b1 b2 b3 : Bool) (h : f (xor (xor b1 b2) b3) = true) :
    f b1 = true ∨ f b2 = true ∨ f b3 = true := by
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true] at h <;> simp [h]

theorem main : let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
let columnPass := fun (key name : Nat) =>
  ((List.range 4).foldl (fun state j =>
    step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (k + (4 + (j + 1))) % 2 ^ k))
    (rot 3 key ^^^ name)) < 2 ^ 8
let keys := List.range (2 ^ k)
let edge := fun (column : Nat) => ∃ w ∈ keys, output w = 0 ∧ columnPass w column
let parity := fun (mask word : Nat) =>
  ((List.range k).filter (fun i => mask.testBit i && word.testBit i)).length % 2 == 1
∀ (query : Nat → Fin (2 ^ k)) (lookup : Nat → Bool → Bool),
  let predicted := fun (column : Nat) =>
    ∃ w ∈ keys,
      (if w.testBit 2 then output w = 0
       else
         let probe := w ^^^ 12
         let y := output probe
         lookup y (parity (query y).val probe) = true) ∧ columnPass w column
  edge 0 ∧ (¬predicted 0 ∨ ∃ c : Fin (2 ^ k), ¬edge c.val ∧ predicted c.val) := by
  intro k rot' step' output columnPass keys edge parity query lookup predicted
  have hout : ∀ w, output w = fout w := by
    intro w
    show outputG step w = outputG fstep w
    rw [step_eq']
  have hcp : ∀ key name, columnPass key name ↔ fcs key name < 256 := by
    intro key name
    show cstateG step key name < 2 ^ 8 ↔ cstateG fstep key name < 256
    rw [step_eq']
    norm_num
  have hk : ∀ w, w ∈ keys ↔ w < 131072 := by
    intro w
    show w ∈ List.range (2 ^ 17) ↔ _
    rw [List.mem_range]
    norm_num
  have hedge : ∀ c, edge c → ∃ o ∈ O, fcs o c < 256 := by
    rintro c ⟨w, hw, h0, hp⟩
    exact ⟨w, hO w ((hk w).1 hw) (by rw [← hout]; exact h0), (hcp w c).1 hp⟩
  have hpred : ∀ (w c : Nat), w < 131072 → c < 2 ^ 17 → w.testBit 2 = false →
      lookup (fout (w ^^^ 12)) (par (query (fout (w ^^^ 12))).val (w ^^^ 12)) = true →
      fcs w c < 256 → (∀ o ∈ O, ¬ fcs o c < 256) →
      ∃ c : Fin (2 ^ k), ¬edge c.val ∧ predicted c.val := by
    intro w c hw hc hb hl hwc hnon
    have hbn : ¬ (w.testBit 2 = true) := by
      rw [hb]
      simp
    refine ⟨⟨c, hc⟩, ?_, ?_⟩
    · intro he
      obtain ⟨o, ho, hoc⟩ := hedge c he
      exact hnon o ho hoc
    · show ∃ w, w ∈ keys ∧ (if w.testBit 2 = true then output w = 0 else
        lookup (output (w ^^^ 12)) (parity (query (output (w ^^^ 12))).val (w ^^^ 12)) = true) ∧
        columnPass w c
      refine ⟨w, (hk w).2 hw, ?_, (hcp w c).2 hwc⟩
      rw [if_neg hbn, hout]
      exact hl
  have hedge0 : edge 0 := by
    show ∃ w, w ∈ keys ∧ output w = 0 ∧ columnPass w 0
    exact ⟨11632, (hk _).2 (by norm_num), by rw [hout]; exact e0.1, (hcp _ _).2 e0.2⟩
  refine ⟨hedge0, ?_⟩
  by_cases hp0 : predicted 0
  swap
  · exact Or.inl hp0
  right
  obtain ⟨w, hw, hcond, hpass⟩ := hp0
  have hwlt := (hk w).1 hw
  have hpass' := (hcp w 0).1 hpass
  by_cases hb : w.testBit 2 = true
  · rw [if_pos hb] at hcond
    exfalso
    exact hOb w (hO w hwlt (by rw [← hout]; exact hcond)) hb hpass'
  · rw [if_neg hb] at hcond
    have hb' : w.testBit 2 = false := by simpa using hb
    have hl : lookup (fout (w ^^^ 12)) (par (query (fout (w ^^^ 12))).val (w ^^^ 12)) = true := by
      rw [← hout]
      exact hcond
    rcases hZ w hwlt hb' hpass' with h11 | ⟨c, hc, hwc, hnon⟩
    · rw [h11, t0, tx, par_xor _ ((48808 ^^^ 12) ^^^ (80232 ^^^ 12)) (109232 ^^^ 12),
        par_xor _ (48808 ^^^ 12) (80232 ^^^ 12)] at hl
      rcases xor3 (lookup 203) _ _ _ hl with h | h | h
      · exact hpred 48808 379 (by norm_num) (by norm_num) t1.1 (by rw [t1.2.1]; exact h)
          t1.2.2.1 t1.2.2.2
      · exact hpred 80232 358 (by norm_num) (by norm_num) t2.1 (by rw [t2.2.1]; exact h)
          t2.2.2.1 t2.2.2.2
      · exact hpred 109232 2502 (by norm_num) (by norm_num) t3.1 (by rw [t3.2.1]; exact h)
          t3.2.2.1 t3.2.2.2
    · exact hpred w c hwlt hc hb' hl hwc hnon

end PEqualNP.Outside.L_lib_650_aux

theorem PEqualNP.Outside.L_lib_650 : (let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
let columnPass := fun (key name : Nat) =>
  ((List.range 4).foldl (fun state j =>
    step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (k + (4 + (j + 1))) % 2 ^ k))
    (rot 3 key ^^^ name)) < 2 ^ 8
let keys := List.range (2 ^ k)
let edge := fun (column : Nat) => ∃ w ∈ keys, output w = 0 ∧ columnPass w column
let parity := fun (mask word : Nat) =>
  ((List.range k).filter (fun i => mask.testBit i && word.testBit i)).length % 2 == 1
∀ (query : Nat → Fin (2 ^ k)) (lookup : Nat → Bool → Bool),
  let predicted := fun (column : Nat) =>
    ∃ w ∈ keys,
      (if w.testBit 2 then output w = 0
       else
         let probe := w ^^^ 12
         let y := output probe
         lookup y (parity (query y).val probe) = true) ∧ columnPass w column
  edge 0 ∧ (¬predicted 0 ∨ ∃ c : Fin (2 ^ k), ¬edge c.val ∧ predicted c.val)) := by
  exact PEqualNP.Outside.L_lib_650_aux.main
