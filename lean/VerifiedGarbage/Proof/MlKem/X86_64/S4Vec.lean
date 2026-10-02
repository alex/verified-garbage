import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the vector sampling

Four iterations of `SampleNTT`'s loop, from fewer than 249 coefficients,
append the candidates less than `q` of their 12 bytes (`sampleAfter_four`).
The code computes the eight candidates in the doublewords of `ymm0`
(`cand_dword`) and their mask in `eax` (`vcand_ok`), and stores the
doublewords that the table's entry for the mask selects (`vput_ok`): those of
the candidates less than `q`, in order (`setBits_bsum`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- Candidate `k < 8` of the four chunks of `out` from byte `p`: `d₁` (`k`
even) or `d₂` (`k` odd) of chunk `k / 2`. -/
def cand4 (out : Nat → Byte) (p k : Nat) : Nat :=
  if k % 2 = 0 then (out (p + 3 * (k / 2))).toNat + 256 * ((out (p + 3 * (k / 2) + 1)).toNat % 16)
  else (out (p + 3 * (k / 2) + 1)).toNat / 16 + 16 * (out (p + 3 * (k / 2) + 2)).toNat

/-- The candidates less than `q` of the four chunks from byte `p`, as coefficients. -/
def acc4 (out : Nat → Byte) (p : Nat) : List Zq :=
  ((List.range 8).filter fun k => decide (cand4 out p k < q)).map fun k => ofNat (cand4 out p k)

/-- The coefficients a chunk adds, if there is room for two. -/
def pair (c₀ c₁ c₂ : Byte) : List Zq :=
  (if c₀.toNat + 256 * (c₁.toNat % 16) < q then [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else []) ++
    (if c₁.toNat / 16 + 16 * c₂.toNat < q then [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else [])

theorem pair_length (c₀ c₁ c₂ : Byte) : (pair c₀ c₁ c₂).length ≤ 2 := by
  unfold pair; split <;> split <;> simp

theorem sampleStepCap_room {a : List Zq} (h : a.length + 2 ≤ n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a ++ pair c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep pair
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]
  dsimp only
  split <;> split <;> simp_all <;> omega

theorem fm2 {α : Type} (p : Nat → Bool) (f : Nat → α) (k : Nat) :
    ([k, k + 1].filter p).map f = (if p k then [f k] else []) ++ (if p (k + 1) then [f (k + 1)] else []) := by
  simp only [List.filter_cons, List.filter_nil]
  cases p k <;> cases p (k + 1) <;> rfl

theorem acc4_eq (out : Nat → Byte) (p : Nat) : acc4 out p =
    pair (out p) (out (p + 1)) (out (p + 2)) ++ pair (out (p + 3)) (out (p + 4)) (out (p + 5)) ++
      pair (out (p + 6)) (out (p + 7)) (out (p + 8)) ++ pair (out (p + 9)) (out (p + 10)) (out (p + 11)) := by
  rw [acc4, show List.range 8 = [0, 0 + 1] ++ [2, 2 + 1] ++ [4, 4 + 1] ++ [6, 6 + 1] from rfl]
  simp only [List.filter_append, List.map_append, fm2, decide_eq_true_eq, pair, cand4]
  simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, ite_true, Nat.add_zero, Nat.add_assoc,
    Nat.zero_add, show (1 % 2 = 0) = False from by decide, ite_false, List.append_assoc, decide_eq_true_eq]

theorem sampleAfter_four {a : List Zq} {out : Nat → Byte} {t : Nat}
    (h : (sampleAfter a out t).length + 8 ≤ n) :
    sampleAfter a out (t + 4) = sampleAfter a out t ++ acc4 out (3 * t) := by
  have p0 := pair_length (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))
  have p1 := pair_length (out (3 * (t + 1))) (out (3 * (t + 1) + 1)) (out (3 * (t + 1) + 2))
  have p2 := pair_length (out (3 * (t + 2))) (out (3 * (t + 2) + 1)) (out (3 * (t + 2) + 2))
  rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_succ, sampleAfter_succ,
    sampleStepCap_room (a := sampleAfter a out t) (by omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _) (by simp only [List.length_append]; omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _) (by simp only [List.length_append]; omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _ ++ _) (by simp only [List.length_append]; omega),
    acc4_eq]
  simp only [List.append_assoc, show 3 * (t + 1) = 3 * t + 3 by omega, show 3 * (t + 2) = 3 * t + 6 by omega,
    show 3 * (t + 3) = 3 * t + 9 by omega, Nat.add_assoc, Nat.reduceAdd]

end VG.Proof.MlKem

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Spec.MlKem

/-- The coefficients `L ++ A` are stored after a write of eight doublewords `V` at
`a[|L|]`, whose first `|A|` doublewords are `A`. -/
theorem stored_write8 {m : Mem} {aP : Addr} {L A : List Zq} (h : Stored m aP L) (hl : L.length + 8 ≤ 256)
    (hA : A.length ≤ 8) (V : BitVec 256)
    (hV : ∀ i < A.length, V.extractLsb' (32 * i) 32 = BitVec.ofNat 32 (A.getD i 0).val) :
    Stored (m.writeW (coeffAddr aP L.length) V) aP (L ++ A) := by
  intro k hk
  rw [List.length_append] at hk
  rw [coeffAt_eq]
  by_cases hkL : k < L.length
  · rw [readW_writeW_off m aP V (d := 4 * k) (e := 4 * L.length) (n := 4) (by omega) (by omega) (by omega),
      show (L ++ A).getD k 0 = L.getD k 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hkL]]
    exact h k hkL
  · have e := readW_writeW_inside m (coeffAddr aP L.length) V (k := 4 * (k - L.length)) (n := 4) (by omega)
      (by decide)
    rw [coeffAddr, Offset.add_add, show 4 * L.length + 4 * (k - L.length) = 4 * k by omega] at e
    rw [e, show 8 * (4 * (k - L.length)) = 32 * (k - L.length) by omega, hV _ (by omega),
      show (L ++ A).getD k 0 = A.getD (k - L.length) 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show L.length ≤ k by omega)]]

end VG.Proof.MlKem.X86_64

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64
open VG.Impl.MlKem.X86_64.Sample4 (vcand vput tabE aV setBits)
open VG.Proof.Sha3.X86_64 (WP.cons Upd)

def shuf0 : BitVec 128 := 0x80800504808004038080020180800100#128
def shuf1 : BitVec 128 := 0x80800b0a80800a098080080780800706#128
def shV : BitVec 128 := 0x00000004000000000000000400000000#128
def maskV : BitVec 128 := 0x00000fff00000fff00000fff00000fff#128

/-- The first byte of candidate `k`'s pair: `3 (k / 2) + k % 2`. -/
abbrev cb (k : Nat) : Nat := 3 * (k / 2) + k % 2

/-- Candidate `k` of the bytes `b`. -/
def candN (b : Nat → Nat) (k : Nat) : Nat :=
  if k % 2 = 0 then b (cb k) + 256 * (b (cb k + 1) % 16) else b (cb k) / 16 + 16 * b (cb k + 1)

theorem gb {f : Nat → BitVec 8} {a b c d : Nat} (h1 : a = c) (h2 : b = d) :
    (f a).getLsbD b = (f c).getLsbD d := by subst h1 h2; rfl

theorem toNat_dword_ofBytes (f : Nat → BitVec 8) {j : Nat} (hj : j < 4) :
    (dword (ofBytes f) j).toNat = (f (4 * j)).toNat + 256 * (f (4 * j + 1)).toNat +
      65536 * (f (4 * j + 2)).toNat + 16777216 * (f (4 * j + 3)).toNat := by
  have e : dword (ofBytes f) j = f (4 * j + 3) ++ f (4 * j + 2) ++ f (4 * j + 1) ++ f (4 * j) := by
    apply BitVec.eq_of_getLsbD_eq; intro m hm
    rw [getLsbD_dword_ofBytes _ hj hm]
    simp only [BitVec.getLsbD_append]
    have h8 := Nat.mod_lt m (show 8 > 0 by decide)
    by_cases a : m < 8
    · simp only [a, ite_true]; exact gb (by omega) (by omega)
    by_cases b : m - 8 < 8
    · simp only [a, b, ite_true, ite_false]; exact gb (by omega) (by omega)
    by_cases c : m - 8 - 8 < 8
    · simp only [a, b, c, ite_true, ite_false]; exact gb (by omega) (by omega)
    · simp only [a, b, c, ite_false]; exact gb (by omega) (by omega)
  rw [e]
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 2)).isLt, ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 1)).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j)).isLt]
  simp only [Nat.shiftLeft_eq]
  have := (f (4 * j)).isLt; have := (f (4 * j + 1)).isLt; have := (f (4 * j + 2)).isLt
  have := (f (4 * j + 3)).isLt
  omega

theorem pshufb_shuf0 (a : BitVec 128) : XBinOp.eval .pshufb a shuf0 =
    ofBytes fun i => if i % 4 < 2 then byte a (cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_shuf1 (a : BitVec 128) : XBinOp.eval .pshufb a shuf1 =
    ofBytes fun i => if i % 4 < 2 then byte a (6 + cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- The `vpshufb` mask of lane `l`. -/
abbrev shuf (l : Nat) : BitVec 128 := if l = 0 then shuf0 else shuf1

/-- The candidates in lane `l` of `ymm0`, from `a`, the 16 bytes in both. -/
abbrev candV (a : BitVec 128) (l : Nat) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb a (shuf l)) shV) maskV

theorem toNat_and_fff (x : BitVec 32) : (x &&& 0xfff#32).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_and, show (0xfff#32).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem cand_dword (a : BitVec 128) {l j : Nat} (hl : l < 2) (hj : j < 4) :
    dword (candV a l) j = BitVec.ofNat 32 (candN (fun i => (byte a i).toNat) (4 * l + j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_pand, (show ∀ i < 4, dword maskV i = 0xfff#32 by decide) j hj, toNat_and_fff]
  have hb : ∀ i, (byte a i).toNat < 256 := fun i => (byte a i).isLt
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [shuf, VVarOp.eval, pshufb_shuf0, pshufb_shuf1, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, ↓reduceIte, show (dword shV 0).toNat = 0 from rfl, show (dword shV 1).toNat = 4 from rfl,
    show (dword shV 2).toNat = 0 from rfl, show (dword shV 3).toNat = 4 from rfl, Nat.reduceLT,
    BitVec.toNat_ushiftRight,
    toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
    candN, cb, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceEqDiff, Nat.add_zero] <;>
  omega

def qV4 : BitVec 128 := 0x00000d0100000d0100000d0100000d01#128
def sign0 : BitVec 128 := 0x0f0b0703808080808080808080808080#128
def sign1 : BitVec 128 := 0x8080808080808080808080800f0b0703#128

theorem pshufb_sign0 (a : BitVec 128) : XBinOp.eval .pshufb a sign0 =
    ofBytes fun i => if 12 ≤ i then byte a (4 * (i - 12) + 3) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_sign1 (a : BitVec 128) : XBinOp.eval .pshufb a sign1 =
    ofBytes fun i => if i < 4 then byte a (4 * i + 3) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- `∑ i < n, f i · 2ⁱ`. -/
def bsum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum f n + (f n).toNat * 2 ^ n

theorem bsum_lt (f : Nat → Bool) : ∀ n, bsum f n < 2 ^ n
  | 0 => by simp [bsum]
  | n + 1 => by
    have := bsum_lt f n
    simp only [bsum, Nat.pow_succ]
    cases f n <;> simp <;> omega

theorem byteMask_eq (x : BitVec 256) {n : Nat} (hn : n ≤ 64) :
    byteMask x n = BitVec.ofNat 64 (bsum (fun i => x.getLsbD (8 * i + 7)) n) := by
  unfold byteMask
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil, bsum]
    have hl := bsum_lt (fun i => x.getLsbD (8 * i + 7)) n
    have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    cases x.getLsbD (8 * n + 7)
    · simp
    · simp only [ite_true, Bool.toNat_true, Nat.one_mul]
      apply BitVec.eq_of_toNat_eq
      have h2 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have e := Nat.two_pow_add_eq_or_of_lt hl 1
      rw [Nat.mul_one] at e
      rw [BitVec.toNat_or, BitVec.toNat_twoPow, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.or_comm, ← e, Nat.add_comm]

theorem bsum_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : bsum f n = bsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum, bsum, ih fun i hi => h i (by omega), h n (by omega)]

theorem itT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem itF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem byte3_bit7 (X : BitVec 128) (j : Nat) : (byte X (4 * j + 3)).getLsbD 7 = (dword X j).getLsbD 31 := by
  rw [byte, BitVec.getLsbD_extractLsb', getLsbD_dword]
  simp only [show 7 < 8 by decide, show 31 < 32 by decide, decide_true, Bool.true_and]
  exact congrArg _ (by omega)

/-- Bit 7 of byte `i` of the two lanes after the `vpshufb` with the sign masks. -/
theorem sign_bit (X0 X1 : BitVec 128) {i : Nat} (hi : i < 32) :
    (XBinOp.eval .pshufb X1 sign1 ++ XBinOp.eval .pshufb X0 sign0).getLsbD (8 * i + 7) =
      if 12 ≤ i ∧ i < 16 then (dword X0 (i - 12)).getLsbD 31
      else if 16 ≤ i ∧ i < 20 then (dword X1 (i - 16)).getLsbD 31 else false := by
  rw [BitVec.getLsbD_append, pshufb_sign0, pshufb_sign1]
  by_cases h : i < 16
  · have h7 : 8 * i + 7 < 128 := by omega
    rw [itT h7, getLsbD_ofBytes _ h (by decide)]
    by_cases h' : 12 ≤ i
    · rw [itT h', itT (show 12 ≤ i ∧ i < 16 from ⟨h', h⟩), byte3_bit7]
    · rw [itF h', itF (show ¬ (12 ≤ i ∧ i < 16) by omega), itF (show ¬ (16 ≤ i ∧ i < 20) by omega)]; rfl
  · have h7 : ¬ 8 * i + 7 < 128 := by omega
    have hk : i - 16 < 16 := by omega
    rw [itF h7, show 8 * i + 7 - 128 = 8 * (i - 16) + 7 by omega, getLsbD_ofBytes _ hk (by decide),
      itF (show ¬ (12 ≤ i ∧ i < 16) by omega)]
    by_cases h' : i < 20
    · rw [itT (show i - 16 < 4 by omega), itT (show 16 ≤ i ∧ i < 20 from ⟨by omega, h'⟩), byte3_bit7]
    · rw [itF (show ¬ i - 16 < 4 by omega), itF (show ¬ (16 ≤ i ∧ i < 20) by omega)]; rfl

theorem mask_bsum (X0 X1 : BitVec 128) :
    bsum (fun i => (XBinOp.eval .pshufb X1 sign1 ++ XBinOp.eval .pshufb X0 sign0).getLsbD (8 * i + 7)) 32 =
      4096 * bsum (fun k => if k < 4 then (dword X0 k).getLsbD 31 else (dword X1 (k - 4)).getLsbD 31) 8 := by
  rw [bsum_congr fun i hi => sign_bit X0 X1 hi]
  simp only [bsum, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, and_true, and_false,
    ite_true, ite_false, Bool.toNat_false, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.reducePow,
    show ¬ (12 ≤ 0) by decide]
  omega

theorem dword_qV4 {j : Nat} (hj : j < 4) : dword qV4 j = 3329#32 := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

/-- The sign of `c - q`: whether `c < q`. -/
theorem sign_sub_q {c : Nat} (hc : c < 4096) : (BitVec.ofNat 32 c - 3329#32).getLsbD 31 = decide (c < 3329) := by
  rw [BitVec.getLsbD, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  exact decide_eq_decide.mpr (by omega)

theorem ext_app8 (a : Nat → BitVec 32) {i : Nat} (hi : i < 8) :
    (a 7 ++ a 6 ++ a 5 ++ a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0).extractLsb' (32 * i) 32 = a i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [BitVec.getLsbD_append] <;>
  simp (disch := omega) only [itT, itF] <;>
  exact congrArg _ (by omega)

theorem dw8_permDwords (idx x : BitVec 256) {i : Nat} (hi : i < 8) :
    (permDwords idx x).extractLsb' (32 * i) 32 = x.extractLsb' (32 * (idx.extractLsb' (32 * i) 3).toNat) 32 :=
  ext_app8 (fun k => x.extractLsb' (32 * (idx.extractLsb' (32 * k) 3).toNat) 32) hi

def nib0 : BitVec 128 := 0x0000000c000000080000000400000000#128
def nib1 : BitVec 128 := 0x0000001c000000180000001400000010#128

/-- The indices: `E` shifted right by `4 i` in doubleword `i`. -/
abbrev idxV (E : BitVec 32) : BitVec 256 :=
  VVarOp.eval .vpsrlvd (ofDwords E E E E) nib1 ++ VVarOp.eval .vpsrlvd (ofDwords E E E E) nib0

theorem ext_app2 (h l : BitVec 128) {i : Nat} (hi : i < 8) :
    (h ++ l).extractLsb' (32 * i) 32 = dword (if i < 4 then l else h) (i % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', getLsbD_dword, hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h4 : i < 4
  · rw [itT (show 32 * i + j < 128 by omega), itT h4]; exact congrArg _ (by omega)
  · rw [itF (show ¬ 32 * i + j < 128 by omega), itF h4]; exact congrArg _ (by omega)

theorem nib_dword {l j : Nat} (hl : l < 2) (hj : j < 4) :
    (dword (if l = 0 then nib0 else nib1) j).toNat = 4 * (4 * l + j) := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

theorem idx_toNat (E : BitVec 32) {i : Nat} (hi : i < 8) :
    ((idxV E).extractLsb' (32 * i) 3).toNat = E.toNat / 16 ^ i % 8 := by
  rw [show (idxV E).extractLsb' (32 * i) 3 = ((idxV E).extractLsb' (32 * i) 32).extractLsb' 0 3 by
      rw [extract_extract _ _ _ _ _ (by omega), Nat.add_zero], ext_app2 _ _ hi]
  have hn : ∀ l < 2, ∀ j < 4, dword (VVarOp.eval .vpsrlvd (ofDwords E E E E) (if l = 0 then nib0 else nib1)) j =
      E >>> (4 * (4 * l + j)) := by
    intro l hl j hj
    have e := nib_dword hl hj
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, e,
      itT (show 4 * (4 * l + 0) < 32 by omega), itT (show 4 * (4 * l + 1) < 32 by omega),
      itT (show 4 * (4 * l + 2) < 32 by omega), itT (show 4 * (4 * l + 3) < 32 by omega)]
  have e : dword (if i < 4 then VVarOp.eval .vpsrlvd (ofDwords E E E E) nib0
      else VVarOp.eval .vpsrlvd (ofDwords E E E E) nib1) (i % 4) = E >>> (4 * i) := by
    by_cases h4 : i < 4
    · rw [itT h4]; have := hn 0 (by decide) (i % 4) (by omega); rw [itT rfl] at this
      rw [this]; congr 1; omega
    · rw [itF h4]; have := hn 1 (by decide) (i % 4) (by omega); rw [itF (by decide)] at this
      rw [this]; congr 1; omega
  rw [e, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- `s'` is `s` with the two lanes of `d` set to `v 0` and `v 1` (flags aside). -/
structure LUpd (s s' : State) (d : XReg) (v : Nat → BitVec 128) : Prop where
  val : ∀ l < 2, s'.lane d l = v l
  other : ∀ r, r ≠ d → ∀ l < 2, s'.lane r l = s.lane r l
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LUpd.setV256 (s : State) (d : XReg) (lo hi : BitVec 128) :
    LUpd s (s.setV .l256 d lo hi) d fun l => if l = 0 then lo else hi :=
  ⟨fun l _ => by rw [State.lane_setV256, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV256, ite_eq_right hr],
    rfl, rfl, rfl, rfl⟩

theorem LUpd.setV128 (s : State) (d : XReg) (lo hi : BitVec 128) :
    LUpd s (s.setV .l128 d lo hi) d fun l => if l = 0 then lo else 0 :=
  ⟨fun l _ => by rw [State.lane_setV128, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV128, ite_eq_right hr],
    rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vbin {op : VBinOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => op.sse.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vvar {op : VVarOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => op.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vvar op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vpbcastd {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun _ => let v := dword (s.lane a 0) 0; ofDwords v v v v) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastd .l256 d a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)) rfl (k _ (by
    have h := LUpd.setV256 s d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)
    exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vpermd {d i a : XReg}
    (k : ∀ s', LUpd s s' d (fun l => (permDwords (s.ymm i) (s.ymm a)).extractLsb' (128 * l) 128) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpermd d i a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)) rfl (k _ (by
    have h := LUpd.setV256 s d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vbcast128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', LUpd s s' d (fun _ => s.mem.readW a 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vbroadcasti128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (s.mem.readW a 128) (s.mem.readW a 128))
    (by simp [exec, ha, State.load128, hin]) (k _ ?_)
  have h := LUpd.setV256 s d (s.mem.readW a 128) (s.mem.readW a 128)
  exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr⟩

theorem wp_vld128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.mem.readW a 128 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l128 d (s.mem.readW a 128) 0)
    (by simp [exec, ha, State.load128, hin]) (k _ (LUpd.setV128 s d _ _))

theorem wp_vld256 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', LUpd s s' d (fun l => (s.mem.readW a 256).extractLsb' (128 * l) 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l256 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128)
    ((s.mem.readW a 256).extractLsb' 128 128)) (by simp [exec, ha, State.load256, hin]) (k _ ?_)
  have h := LUpd.setV256 s d ((s.mem.readW a 256).extractLsb' 0 128) ((s.mem.readW a 256).extractLsb' 128 128)
  exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
    h.other, h.gpr, h.mem, h.rd, h.wr⟩

theorem wp_vst256 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

/-- `s'` is `s` with register `d` set to `v`, the vector registers as they were (flags aside). -/
structure GUpd (s s' : State) (d : Reg) (v : BitVec 64) : Prop extends Upd s s' d v where
  lane : ∀ x l, s'.lane x l = s.lane x l

theorem GUpd.setReg (s : State) (d : Reg) (v : BitVec 64) : GUpd s (s.setReg d v) d v :=
  ⟨Upd.setReg s d v, fun _ _ => rfl⟩

theorem GUpd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    GUpd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨Upd.withFlags s cf o zf sf d v, fun _ _ => rfl⟩

theorem wp_vpmovmskb {d : Reg} {r : XReg}
    (k : ∀ s', GUpd s s' d (byteMask (s.ymm r) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.vpmovmskb .l256 d r :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_shr32 {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 31)
    (k : ∀ s', GUpd s s' d ((((s.gpr d).setWidth 32) >>> n).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift32 .shr d n :: is)) s Q := by
  let a := (s.gpr d).setWidth 32
  refine WP.cons (s' := (s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
    (some (a >>> n == 0)) (some (a >>> n).msb)).setReg d ((a >>> n).setWidth 64)) ?_
    (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  simp only [exec, execShift32, h₁, h₂, and_self, ite_true, State.setReg32]
  rfl

theorem wp_add32m {d : Reg} {m : MemOp} {a' : Addr} (ha : s.ea m = a') (hin : InRegions (s.rd ++ s.wr) a' 4)
    (k : ∀ s', GUpd s s' d (((s.gpr d).setWidth 32 + s.mem.readW a' 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .add d (.mem m) :: is)) s Q := by
  let a := (s.gpr d).setWidth 32
  let b := s.mem.readW a' 32
  refine WP.cons (s' := (arithFlags s (a + b) (2 ^ 32 ≤ a.toNat + b.toNat) (addOverflow a b (a + b))).setReg d
    ((a + b).setWidth 64)) ?_ (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  simp [exec, execAlu32, readSrc32, State.load32, ha, hin, State.setReg32, a, b]

theorem wp_addi' {d : Reg} {v : BitVec 32}
    (k : ∀ s', GUpd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.withFlags _ _ _ _ _ _ _))

end


/-! ## The candidates and their mask -/

abbrev sgn (l : Nat) : BitVec 128 := if l = 0 then sign0 else sign1
abbrev nib (l : Nat) : BitVec 128 := if l = 0 then nib0 else nib1

/-- The constants of the vector code in `ymm8` to `ymm13`. -/
structure VC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = shuf l
  c9 : ∀ l < 2, s.lane .xmm9 l = shV
  c10 : ∀ l < 2, s.lane .xmm10 l = maskV
  c11 : ∀ l < 2, s.lane .xmm11 l = qV4
  c12 : ∀ l < 2, s.lane .xmm12 l = sgn l
  c13 : ∀ l < 2, s.lane .xmm13 l = nib l

theorem VC.lupd {s s' : State} (h : VC s) {d : XReg} {v : Nat → BitVec 128} (hu : LUpd s s' d v)
    (hd : d = .xmm0 ∨ d = .xmm1) : VC s' := by
  have e : ∀ r, r = XReg.xmm8 ∨ r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11 ∨ r = .xmm12 ∨ r = .xmm13 →
      ∀ l < 2, s'.lane r l = s.lane r l := fun r hr l hl => hu.other r (by
    rcases hd with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) l hl
  exact ⟨fun l hl => by rw [e _ (by simp) l hl, h.c8 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c9 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c10 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c11 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c12 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c13 l hl]⟩

theorem VC.gupd {s s' : State} (h : VC s) {d : Reg} {v : BitVec 64} (hu : GUpd s s' d v) : VC s' :=
  ⟨fun l hl => by rw [hu.lane, h.c8 l hl], fun l hl => by rw [hu.lane, h.c9 l hl],
    fun l hl => by rw [hu.lane, h.c10 l hl], fun l hl => by rw [hu.lane, h.c11 l hl],
    fun l hl => by rw [hu.lane, h.c12 l hl], fun l hl => by rw [hu.lane, h.c13 l hl]⟩

theorem candN_lt (b : Nat → Nat) (hb : ∀ i, b i < 256) (k : Nat) : candN b k < 4096 := by
  unfold candN; have := hb (cb k); have := hb (cb k + 1); split <;> omega

/-- The mask of the candidates less than `q`. -/
abbrev maskN (b : Nat → Nat) : Nat := bsum (fun k => decide (candN b k < 3329)) 8

theorem vcand_ok {s : State} (hc : VC s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) :
    WP isa (.block vcand) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 (maskN fun i => (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) ∧
      (∀ l < 2, s'.lane .xmm0 l = candV (s.mem.readW (s.gpr .rsi) 128) l) ∧ VC s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  open VG.Proof.MlKem.X86_64 (ea_at add_ofNat_zero) in
  refine wp_vbcast128 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine wp_vbin fun s2 u2 => wp_vvar fun s3 u3 => wp_vbin fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vpmovmskb fun s7 u7 => wp_shr32 (by decide) (by decide) fun s8 u8 => WP.block_nil ?_
  have c1 := hc.lupd u1 (.inl rfl)
  have c2 := c1.lupd u2 (.inl rfl)
  have c3 := c2.lupd u3 (.inl rfl)
  have c4 := c3.lupd u4 (.inl rfl)
  have c5 := c4.lupd u5 (.inr rfl)
  have c6 := c5.lupd u6 (.inr rfl)
  have c7 := c6.gupd u7
  generalize s.mem.readW (s.gpr .rsi) 128 = L at u1 ⊢
  have h4 : ∀ l < 2, s4.lane .xmm0 l = candV L l := fun l hl => by
    rw [u4.val l hl, u3.val l hl, u2.val l hl, u1.val l hl, c1.c8 l hl, c2.c9 l hl, c3.c10 l hl]; rfl
  have h6 : ∀ l < 2, s6.lane .xmm1 l = XBinOp.eval .pshufb (XBinOp.eval .psubd (candV L l) qV4) (sgn l) :=
    fun l hl => by rw [u6.val l hl, u5.val l hl, h4 l hl, c4.c11 l hl, c5.c12 l hl]; rfl
  have h0 : ∀ l < 2, s8.lane .xmm0 l = candV L l := fun l hl => by
    rw [u8.lane, u7.lane, u6.other _ (by decide) l hl, u5.other _ (by decide) l hl, h4 l hl]
  have hb : ∀ i, (byte L i).toNat < 256 := fun i => (byte L i).isLt
  have hm : byteMask (s6.ymm .xmm1) 32 = BitVec.ofNat 64 (4096 * maskN fun i => (byte L i).toNat) := by
    rw [State.ymm_eq, h6 1 (by decide), h6 0 (by decide), byteMask_eq _ (by decide)]
    simp only [sgn, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
    rw [mask_bsum, maskN]
    congr 2
    apply bsum_congr
    intro k hk
    by_cases h : k < 4
    · rw [itT h, dword_psubd _ _ h, dword_qV4 h, cand_dword _ (show 0 < 2 by decide) h,
        sign_sub_q (candN_lt _ hb _), Nat.mul_zero, Nat.zero_add]
    · rw [itF h, dword_psubd _ _ (by omega), dword_qV4 (by omega), cand_dword _ (show 1 < 2 by decide) (by omega),
        sign_sub_q (candN_lt _ hb _), show 4 * 1 + (k - 4) = k by omega]
  have hM : maskN (fun i => (byte L i).toNat) < 2 ^ 8 := bsum_lt _ 8
  refine ⟨?_, h0, c7.gupd u8, by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem],
    by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], fun r hr => ?_⟩
  · rw [u8.gpr, u7.gpr, hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · rw [u8.other r hr, u7.other r hr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]

/-! ## The compaction -/

theorem ymm_halves (x : BitVec 256) : x.extractLsb' 128 128 ++ x.extractLsb' 0 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 128
  · rw [itT h]; simp [h]
  · rw [itF h]; simp only [show j - 128 < 128 by omega, decide_true, Bool.true_and]; exact congrArg _ (by omega)

theorem ea_tabE {s : State} {M : Nat} (h : s.gpr .rax = BitVec.ofNat 64 M) :
    s.ea tabE = s.gpr .rbx + BitVec.ofNat 64 (8 * M) := by
  simp only [State.ea, tabE, h, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ea_tabE4 {s : State} {M : Nat} (h : s.gpr .rax = BitVec.ofNat 64 M) :
    s.ea { tabE with disp := 4 } = s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4) := by
  simp only [State.ea, tabE, h]
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, show BitVec.ofInt 64 4 = 4#64 from rfl]
  omega

theorem ea_aV (s : State) : s.ea aV = s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat) := by
  simp only [State.ea, aV, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- The doublewords stored: candidate `E / 16ⁱ mod 8` in doubleword `i`. -/
theorem vput_ok {s : State} (hc : VC s) {L : BitVec 128} (h0 : ∀ l < 2, s.lane .xmm0 l = candV L l)
    {M : Nat} (hrax : s.gpr .rax = BitVec.ofNat 64 M)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 16)
    (hin4 : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 4)
    (hout : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) 32)
    (hd : ∀ V : BitVec 256, (s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) V).readW
      (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 32 = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 32) :
    WP isa (.block vput) s fun s' =>
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) V ∧
        ∀ i < 8, V.extractLsb' (32 * i) 32 = BitVec.ofNat 32 (candN (fun i => (byte L i).toNat)
          ((dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0).toNat / 16 ^ i % 8))) ∧
      s'.gpr .rdi = (((s.gpr .rdi).setWidth 32 +
        s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 32).setWidth 64) ∧
      s'.gpr .rsi = s.gpr .rsi + 12 ∧ VC s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := by
  refine wp_vld128 (ea_tabE hrax) hin fun s1 u1 => wp_vpbcastd fun s2 u2 => wp_vvar fun s3 u3 => wp_vpermd fun s4 u4 => ?_
  have g4 : s4.gpr = s.gpr := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine wp_vst256 (a := s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (by rw [ea_aV, g4])
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact hout) fun s5 g5 l5 m5 r5 w5 => ?_
  refine wp_add32m (a' := s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) (by rw [← ea_tabE4 hrax]; simp only [State.ea, g5, g4])
    (by rw [r5, w5, u4.rd, u3.rd, u2.rd, u1.rd, u4.wr, u3.wr, u2.wr, u1.wr]; exact hin4) fun s6 u6 =>
    wp_addi' fun s7 u7 => WP.block_nil ?_
  have c4 : VC s4 := ((hc.lupd u1 (.inr rfl)).lupd u2 (.inr rfl)).lupd u3 (.inr rfl) |>.lupd u4 (.inl rfl)
  have c5 : VC s5 := ⟨fun l hl => by rw [l5, c4.c8 l hl], fun l hl => by rw [l5, c4.c9 l hl],
    fun l hl => by rw [l5, c4.c10 l hl], fun l hl => by rw [l5, c4.c11 l hl], fun l hl => by rw [l5, c4.c12 l hl],
    fun l hl => by rw [l5, c4.c13 l hl]⟩
  have hm5 : s5.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (s4.ymm .xmm0) := by
    rw [m5, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨s4.ymm .xmm0, by rw [u7.mem, u6.mem, hm5], fun i hi => ?_⟩, ?_, ?_, (c5.gupd u6).gupd u7,
    by rw [u7.rd, u6.rd, r5, u4.rd, u3.rd, u2.rd, u1.rd], by rw [u7.wr, u6.wr, w5, u4.wr, u3.wr, u2.wr, u1.wr],
    fun r h1 h2 => by rw [u7.other r h2, u6.other r h1, g5, g4]⟩
  · -- the stored doublewords
    have hy4 : s4.ymm .xmm0 = permDwords (s3.ymm .xmm1) (s3.ymm .xmm0) := by
      rw [State.ymm_eq, u4.val 1 (by decide), u4.val 0 (by decide), Nat.mul_one, Nat.mul_zero, ymm_halves]
    have hx3 : s3.ymm .xmm0 = candV L 1 ++ candV L 0 := by
      rw [State.ymm_eq, u3.other .xmm0 (by decide) 1 (by decide), u3.other .xmm0 (by decide) 0 (by decide),
        u2.other .xmm0 (by decide) 1 (by decide), u2.other .xmm0 (by decide) 0 (by decide),
        u1.other .xmm0 (by decide) 1 (by decide), u1.other .xmm0 (by decide) 0 (by decide), h0 1 (by decide),
        h0 0 (by decide)]
    have hi3 : s3.ymm .xmm1 = idxV (dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0) := by
      rw [State.ymm_eq, u3.val 1 (by decide), u3.val 0 (by decide), u2.val 1 (by decide), u2.val 0 (by decide),
        u2.other .xmm13 (by decide) 1 (by decide), u2.other .xmm13 (by decide) 0 (by decide),
        u1.other .xmm13 (by decide) 1 (by decide), u1.other .xmm13 (by decide) 0 (by decide),
        u1.val 0 (by decide), hc.c13 1 (by decide), hc.c13 0 (by decide)]
      rfl
    rw [hy4, dw8_permDwords _ _ hi, hi3, idx_toNat _ hi, hx3]
    have hp : (dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0).toNat / 16 ^ i % 8 < 8 :=
      Nat.mod_lt _ (by decide)
    rw [ext_app2 _ _ hp]
    by_cases h4 : (dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0).toNat / 16 ^ i % 8 < 4
    · rw [itT h4, cand_dword _ (show 0 < 2 by decide) (Nat.mod_lt _ (by decide))]
      congr 2; omega
    · rw [itF h4, cand_dword _ (show 1 < 2 by decide) (Nat.mod_lt _ (by decide))]
      congr 2; omega
  · rw [u7.other _ (by decide), u6.gpr, g5, g4, hm5, hd]
  · rw [u7.gpr, u6.other _ (by decide), g5, g4]; rfl

theorem bsum8_bit (f : Nat → Bool) {k : Nat} (hk : k < 8) : bsum f 8 / 2 ^ k % 2 = (f k).toNat := by
  have h : ∀ j, (f j).toNat ≤ 1 := fun j => Bool.toNat_le _
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
  have h6 := h 6; have h7 := h 7
  simp only [bsum, Nat.reducePow, Nat.zero_add]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow] <;> omega

theorem setBits_bsum (f : Nat → Bool) : setBits (bsum f 8) = (List.range 8).filter f := by
  unfold setBits
  apply List.filter_congr
  intro k hk
  rw [bsum8_bit f (List.mem_range.mp hk)]
  cases f k <;> rfl

end VG.Proof.MlKem.X86_64.S4
