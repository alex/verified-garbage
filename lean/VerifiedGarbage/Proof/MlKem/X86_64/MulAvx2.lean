import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Impl.MlKem.X86_64.MulAvx2

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts_avx2`

Untrusted: everything here is checked by Lean. Each iteration of the loop
loads 32 coefficients of `f` and of `g` (`yload4_ok`) and, in each lane,
does what an iteration of `vg_mlkem_multiply_ntts` does (`Mul.lean`): the
SSE2 code's `deint`, `vbase` and `vinter`, whose proofs hold of each lane
(`ylanes`), on the pairs of coefficients `32i + 8t + 4l + (0 … 3)`, `t <
4`, of lane `l` (`MulY.step`); the stores put each product in its place
(`ystore4`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The SSE2 code of each lane -/

theorem deintS_ok0 (s : State) :
    WP isa (.block (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5)) s fun s' =>
      (s'.xmm .xmm0 = deE (s.xmm .xmm0) (s.xmm .xmm1) (s.xmm .xmm2) (s.xmm .xmm3) ∧
        s'.xmm .xmm4 = deO (s.xmm .xmm0) (s.xmm .xmm1) (s.xmm .xmm2) (s.xmm .xmm3)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] s s' := by
  simp only [deintS]
  vrunm [eval_movdqa]
  exact ⟨⟨rfl, rfl⟩, by xonly⟩

theorem deintS_ok6 (s : State) :
    WP isa (.block (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11)) s fun s' =>
      (s'.xmm .xmm6 = deE (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9) ∧
        s'.xmm .xmm10 = deO (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9)) ∧
      XOnly [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  simp only [deintS]
  vrunm [eval_movdqa]
  exact ⟨⟨rfl, rfl⟩, by xonly⟩

/-- The four values `vinterS` leaves of `X1` and `X2`, in the order of the stores. -/
def interV (X1 X2 : BitVec 128) : List (BitVec 128) :=
  [XBinOp.eval .punpcklwd (XBinOp.eval .punpcklwd X1 X2) 0, XBinOp.eval .punpckhwd (XBinOp.eval .punpcklwd X1 X2) 0,
    XBinOp.eval .punpcklwd (XBinOp.eval .punpckhwd X1 X2) 0, XBinOp.eval .punpckhwd (XBinOp.eval .punpckhwd X1 X2) 0]

theorem vinterS_ok (s : State) :
    WP isa (.block vinterS) s fun s' =>
      (s'.xmm .xmm1 = (interV (s.xmm .xmm1) (s.xmm .xmm2))[0]! ∧
        s'.xmm .xmm5 = (interV (s.xmm .xmm1) (s.xmm .xmm2))[1]! ∧
        s'.xmm .xmm3 = (interV (s.xmm .xmm1) (s.xmm .xmm2))[2]! ∧
        s'.xmm .xmm6 = (interV (s.xmm .xmm1) (s.xmm .xmm2))[3]!) ∧
      XOnly [.xmm1, .xmm3, .xmm4, .xmm5, .xmm6] s s' := by
  simp only [vinterS]
  vrunm [eval_movdqa, pxor_self]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by xonly⟩

theorem lane_deintS0 : laneSseBlock (toY (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5)) =
    some (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5) := by decide +kernel
theorem lane_deintS6 : laneSseBlock (toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11)) =
    some (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11) := by decide +kernel
theorem lane_vbase : laneSseBlock (toY vbase) = some vbase := by decide +kernel
theorem lane_vinterS : laneSseBlock (toY vinterS) = some vinterS := by decide +kernel

/-! ## Loads and stores -/

/-- Four 256-bit loads. -/
theorem yload4_ok {p : Reg} {a b c d : XReg} (hd : [a, b, c, d].Nodup) {s : State}
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 0) 32)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 32) 32)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 64) 32)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 96) 32) :
    WP isa (.block (yload4 p a b c d)) s fun s' =>
      (∀ l < 2, s'.lane a l = s.mem.readW (s.gpr p + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane b l = s.mem.readW (s.gpr p + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane c l = s.mem.readW (s.gpr p + BitVec.ofNat 64 64 + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 96 + BitVec.ofNat 64 (16 * l)) 128) ∧
      YOnly [a, b, c, d] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hd
  obtain ⟨⟨ab, ac, ad⟩, ⟨bc, bd⟩, cd⟩ := hd
  simp only [yload4]
  rw [show ∀ x y z w : Instr, [x, y, z, w] = [x] ++ [y] ++ [z] ++ [w] from fun _ _ _ _ => rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok h0) fun s1 ⟨l1, o1⟩ => ?_
  have r1 : InRegions (s1.rd ++ s1.wr) (s1.gpr p + BitVec.ofNat 64 32) 32 := by
    rw [o1.rd, o1.wr, o1.gpr]; exact h1
  refine WP.mono (yld_ok r1) fun s2 ⟨l2, o2⟩ => ?_
  have r2 : InRegions (s2.rd ++ s2.wr) (s2.gpr p + BitVec.ofNat 64 64) 32 := by
    rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact h2
  refine WP.mono (yld_ok r2) fun s3 ⟨l3, o3⟩ => ?_
  have r3 : InRegions (s3.rd ++ s3.wr) (s3.gpr p + BitVec.ofNat 64 96) 32 := by
    rw [o3.rd, o3.wr, o3.gpr, o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact h3
  refine WP.mono (yld_ok r3) fun s4 ⟨l4, o4⟩ => ⟨fun l hl => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o4.lane _ (by simpa using ad) l hl, o3.lane _ (by simpa using ac) l hl,
      o2.lane _ (by simpa using ab) l hl, l1 l hl]
  · rw [o4.lane _ (by simpa using bd) l hl, o3.lane _ (by simpa using bc) l hl, l2 l hl,
      o1.gpr, o1.mem]
  · rw [o4.lane _ (by simpa using cd) l hl, l3 l hl, o2.gpr, o2.mem, o1.gpr, o1.mem]
  · rw [l4 l hl, o3.gpr, o3.mem, o2.gpr, o2.mem, o1.gpr, o1.mem]
  · exact ((o1.trans o2).trans (o3.trans o4)).mono (by simp)

theorem coeffAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i =
      if j ≤ i ∧ i < j + 8 then x.extractLsb' (8 * (4 * (i - j))) (8 * 4) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_off, show j + (i - j) = i by omega]]
    exact readW_writeW_inside (k := 4 * (i - j)) (n := 4) _ _ _ (by omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Four stores of 32 bytes to coefficients `j, …, j + 31` of the polynomial at `H`. -/
theorem ystore4 (m : Mem) (H : Addr) {j : Nat} (hj : j + 32 ≤ 256) (Y0 Y1 Y2 Y3 : BitVec 256) :
    let m' := (((m.writeW (coeffAddr H j) Y0).writeW (coeffAddr H j + BitVec.ofNat 64 32) Y1).writeW
      (coeffAddr H j + BitVec.ofNat 64 64) Y2).writeW (coeffAddr H j + BitVec.ofNat 64 96) Y3
    (∀ k < 256, k < j ∨ j + 32 ≤ k → coeffAt m' H k = coeffAt m H k) ∧
      (∀ t < 4, ∀ q < 8, coeffAt m' H (j + 8 * t + q) = ([Y0, Y1, Y2, Y3][t]!).extractLsb' (8 * (4 * q)) (8 * 4)) ∧
      Frame [pR H] m m' := by
  intro m'
  have a1 : coeffAddr H j + BitVec.ofNat 64 32 = coeffAddr H (j + 8) := coeffAddr_off H j 8
  have a2 : coeffAddr H j + BitVec.ofNat 64 64 = coeffAddr H (j + 16) := coeffAddr_off H j 16
  have a3 : coeffAddr H j + BitVec.ofNat 64 96 = coeffAddr H (j + 24) := coeffAddr_off H j 24
  simp only [m', a1, a2, a3]
  refine ⟨fun k hk ho => ?_, fun t ht q hq => ?_, ?_⟩
  · rw [coeffAt_write256 _ _ (by omega) _ hk, coeffAt_write256 _ _ (by omega) _ hk,
      coeffAt_write256 _ _ (by omega) _ hk, coeffAt_write256 _ _ (by omega) _ hk]
    simp (disch := omega) only [ite_eq_right]
  · rw [coeffAt_write256 _ _ (by omega) _ (by omega), coeffAt_write256 _ _ (by omega) _ (by omega),
      coeffAt_write256 _ _ (by omega) _ (by omega), coeffAt_write256 _ _ (by omega) _ (by omega)]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      rw [show j + 8 * 0 + q - j = q by omega]; rfl
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      rw [show j + 8 * 1 + q - (j + 8) = q by omega]; rfl
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      rw [show j + 8 * 2 + q - (j + 16) = q by omega]; rfl
    · simp (disch := omega) only [ite_eq_left]
      rw [show j + 8 * 3 + q - (j + 24) = q by omega]; rfl
  · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-! ## The table -/

theorem gIdxY_lt {p : Nat} (hp : p < 128) : gIdxY p < 128 := by unfold gIdxY; omega

theorem gTabY_lt (p : Nat) : gTabY p < 65536 := gTab_lt _

/-- The pair of word `e` of lane `l` in iteration `i`. -/
abbrev pairY (i l e : Nat) : Nat := 16 * i + 4 * (e / 2) + e % 2 + 2 * l

theorem gIdxY_eq {i l e : Nat} (hl : l < 2) (he : e < 8) : gIdxY (16 * i + 8 * l + e) = pairY i l e := by
  unfold gIdxY pairY; omega

namespace MulY

open VG.Proof.MlKem.X86_64.Mul (hP fP gP sP F G)

/-- After `i` groups of 32 coefficients. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr (fP s₀) (32 * i)
  rdx : s.gpr .rdx = coeffAddr (gP s₀) (32 * i)
  rdi : s.gpr .rdi = coeffAddr (hP s₀) (32 * i)
  r8 : s.gpr .r8 = wAddr (sP s₀) (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : YConsts s
  r2 : ∀ l < 2, s.lane .xmm12 l = r2V
  frame : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s.mem
  tab : ∀ k < 128, (wordAt s.mem (sP s₀) k).toNat = gTabY k
  done : ∀ k < 32 * i, (coeffAt s.mem (hP s₀) k).toNat = ((multiplyNTTs (F s₀) (G s₀))[k]!).val

section
variable {s₀ : State} (hp : mulK.pre s₀)
include hp

theorem inRd {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀) {j : Nat} (hj : j + 32 ≤ 256) {t : Nat} (ht : t < 4) :
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr p j + BitVec.ofNat 64 (32 * t)) 32 := by
  rw [show 32 * t = 4 * (8 * t) by omega, coeffAddr_off, hp.1, hp.2.1]
  rcases hp' with rfl | rfl
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega) (by omega)⟩

/-- The doublewords of lane `l` of load `t` from coefficient `j` of `f` or `g`. -/
theorem loadsY {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀)
    {j : Nat} (hj : j + 32 ≤ 256) {t l : Nat} (ht : t < 4) (hl : l < 2) :
    ∀ e < 4, (dword (m.readW (coeffAddr p j + BitVec.ofNat 64 (32 * t + 16 * l)) 128) e).toNat =
      ((polyAt s₀.mem p)[j + 8 * t + 4 * l + e]!).val := fun e he => by
  rw [dword_readW _ _ he, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 32 * t + 16 * l + 4 * e = 4 * (8 * t + 4 * l + e) by omega, coeffAddr_off, ← coeffAt_eq,
    Mul.coeffFG hp hf hp' (by omega)]
  exact congrArg (fun k : Nat => (((polyAt s₀.mem p)[k]!) : Zq).val) (by omega)


/-- The doublewords of lane `l` of load `t` from coefficient `j` of `f` or `g`, as
`deint_lanes` takes them. -/
theorem loadsY' {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀)
    {j : Nat} (hj : j + 32 ≤ 256) {l : Nat} (hl : l < 2) {t : Nat} (ht : t < 4) (off : Nat) (hoff : off = 32 * t)
    (f : Nat → Nat) (hfe : ∀ e < 4, f e = j + 8 * t + 4 * l + e) :
    ∀ e < 4, (dword (m.readW (coeffAddr p j + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) e).toNat =
      ((polyAt s₀.mem p)[f e]!).val := fun e he => by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hoff, loadsY hp hf hp' hj ht hl e he, hfe e he]

/-- The lanes `deint` leaves of the 32 coefficients from `j` of `f` or `g`, in lane `l`. -/
theorem deintY {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀)
    {j : Nat} (hj : j + 32 ≤ 256) {l : Nat} (hl : l < 2) (a : Addr) (ha : a = coeffAddr p j) :
    (∀ e < 8, (word (deE (m.readW (a + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 64 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 96 + BitVec.ofNat 64 (16 * l)) 128)) e).toNat =
        ((polyAt s₀.mem p)[j + 8 * (2 * e / 4) + 4 * l + 2 * e % 4]!).val) ∧
    (∀ e < 8, (word (deO (m.readW (a + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 64 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 96 + BitVec.ofNat 64 (16 * l)) 128)) e).toNat =
        ((polyAt s₀.mem p)[j + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4]!).val) := by
  subst ha
  exact deint_lanes (c := fun k => ((polyAt s₀.mem p)[j + 8 * (k / 4) + 4 * l + k % 4]!).val)
    (loadsY' hp hf hp' hj hl (t := 0) (by decide) 0 rfl (fun e => j + 8 * (e / 4) + 4 * l + e % 4)
      (fun e he => by omega))
    (loadsY' hp hf hp' hj hl (t := 1) (by decide) 32 rfl (fun e => j + 8 * ((4 + e) / 4) + 4 * l + (4 + e) % 4)
      (fun e he => by omega))
    (loadsY' hp hf hp' hj hl (t := 2) (by decide) 64 rfl (fun e => j + 8 * ((8 + e) / 4) + 4 * l + (8 + e) % 4)
      (fun e he => by omega))
    (loadsY' hp hf hp' hj hl (t := 3) (by decide) 96 rfl (fun e => j + 8 * ((12 + e) / 4) + 4 * l + (12 + e) % 4)
      (fun e he => by omega))
    (fun k _ => by have := val_lt ((polyAt s₀.mem p)[j + 8 * (k / 4) + 4 * l + k % 4]!); omega)


omit hp in
/-- A value of the product, from the lanes `vbase` leaves in lane `l`. -/
theorem prod_valY {i l : Nat} (hi : i < 8) (hl : l < 2) {X1 X2 : BitVec 128} {F G : Poly}
    (h1 : Lanes X1 fun e => F[2 * pairY i l e]! * G[2 * pairY i l e]! +
      F[2 * pairY i l e + 1]! * G[2 * pairY i l e + 1]! * gamma (pairY i l e))
    (h2 : Lanes X2 fun e => F[2 * pairY i l e]! * G[2 * pairY i l e + 1]! +
      F[2 * pairY i l e + 1]! * G[2 * pairY i l e]!)
    {t j : Nat} (ht : t < 4) (hj : j < 4) :
    (word (if (4 * t + j) % 2 = 0 then X1 else X2) ((4 * t + j) / 2)).toNat =
      ((multiplyNTTs F G)[32 * i + 8 * t + 4 * l + j]!).val := by
  rw [multiplyNTTs_get F G (by rw [n_eq]; omega)]
  have hP : pairY i l ((4 * t + j) / 2) = 16 * i + 4 * t + j / 2 + 2 * l := by unfold pairY; omega
  split
  · rename_i he
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h1 _ (by omega)]
    dsimp only
    rw [hP, show 2 * (16 * i + 4 * t + j / 2 + 2 * l) = 32 * i + 8 * t + 4 * l + j by omega,
      show (32 * i + 8 * t + 4 * l + j) / 2 = 16 * i + 4 * t + j / 2 + 2 * l by omega]
  · rename_i he
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h2 _ (by omega)]
    dsimp only
    rw [hP, show 2 * (16 * i + 4 * t + j / 2 + 2 * l) = 32 * i + 8 * t + 4 * l + j - 1 by omega,
      show 32 * i + 8 * t + 4 * l + j - 1 + 1 = 32 * i + 8 * t + 4 * l + j by omega]

theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (mulBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have hj : 32 * i + 32 ≤ 256 := by omega
  have rF : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [hrr, hI.rsi]; exact inRd hp (.inl rfl) hj ht
  have rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [hrr, hI.rdx]; exact inRd hp (.inr rfl) hj ht
  simp only [mulBodyY, List.append_assoc]
  -- the loads of `f` and their lanes
  rw [WP.block_append_iff]
  refine WP.mono (yload4_ok (p := .rsi) (a := .xmm0) (b := .xmm1) (c := .xmm2) (d := .xmm3) (by decide)
    (rF 0 (by decide)) (rF 1 (by decide)) (rF 2 (by decide)) (rF 3 (by decide))) fun s1 ⟨A1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS0 (P := fun l t =>
      t.xmm .xmm0 = deE (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l) ∧
      t.xmm .xmm4 = deO (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l))
    fun l _ => deintS_ok0 (s1.proj l)) fun s2 ⟨D2, o2⟩ => ?_
  -- the loads of `g` and their lanes
  have rG' : ∀ t < 4, InRegions (s2.rd ++ s2.wr) (s2.gpr .rdx + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact rG t ht
  rw [WP.block_append_iff]
  refine WP.mono (yload4_ok (p := .rdx) (a := .xmm6) (b := .xmm7) (c := .xmm8) (d := .xmm9) (by decide)
    (rG' 0 (by decide)) (rG' 1 (by decide)) (rG' 2 (by decide)) (rG' 3 (by decide))) fun s3 ⟨A3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS6 (P := fun l t =>
      t.xmm .xmm6 = deE (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l) ∧
      t.xmm .xmm10 = deO (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l))
    fun l _ => deintS_ok6 (s3.proj l)) fun s4 ⟨D4, o4⟩ => ?_
  have o14 := ((o1.trans o2).trans o3).trans o4
  -- the `γ`s
  have hz : InRegions (s4.rd ++ s4.wr) (s4.gpr .r8 + BitVec.ofNat 64 0) 32 := by
    rw [o14.rd, o14.wr, o14.gpr, hrr, hI.r8, hp.1, hp.2.1, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨pR (sP s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok hz) fun s5 ⟨Z5, o5⟩ => ?_
  have o15 := o14.trans o5
  have c5 : YConsts s5 := o15.consts hI.c (by decide) (by decide)
  -- the lanes `vbase` multiplies
  have m4 : s4.mem = s.mem := o14.mem
  have g4 : s4.gpr = s.gpr := o14.gpr
  have idx : ∀ l < 2, ∀ e < 8, 32 * i + 8 * (2 * e / 4) + 4 * l + 2 * e % 4 = 2 * pairY i l e ∧
      32 * i + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4 = 2 * pairY i l e + 1 := fun l _ e _ => by
    unfold pairY; omega
  have LF : ∀ l < 2, Lanes (s5.lane .xmm0 l) (fun e => (F s₀)[2 * pairY i l e]!) ∧
      Lanes (s5.lane .xmm4 l) (fun e => (F s₀)[2 * pairY i l e + 1]!) := fun l hl => by
    have d := deintY hp hI.frame (.inl rfl) hj hl _ hI.rsi
    rw [o5.lane _ (by decide) l hl, o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl,
      o5.lane _ (by decide) l hl, o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl]
    have e0 : s2.lane .xmm0 l = _ := (D2 l hl).1
    have e4 : s2.lane .xmm4 l = _ := (D2 l hl).2
    rw [e0, e4, (A1 l hl).1, (A1 l hl).2.1, (A1 l hl).2.2.1, (A1 l hl).2.2.2]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [d.1 e he, (idx l hl e he).1]
    · rw [d.2 e he, (idx l hl e he).2]
  have LG : ∀ l < 2, Lanes (s5.lane .xmm6 l) (fun e => (G s₀)[2 * pairY i l e]!) ∧
      Lanes (s5.lane .xmm10 l) (fun e => (G s₀)[2 * pairY i l e + 1]!) := fun l hl => by
    have d := deintY hp (hI.frame.trans (by rw [← o1.mem, ← o2.mem]; exact Frame.refl _ _)) (.inr rfl) hj hl
      (s2.gpr .rdx) (by rw [o2.gpr, o1.gpr, hI.rdx])
    rw [o5.lane _ (by decide) l hl, o5.lane _ (by decide) l hl]
    have e6 : s4.lane .xmm6 l = _ := (D4 l hl).1
    have e10 : s4.lane .xmm10 l = _ := (D4 l hl).2
    rw [e6, e10, (A3 l hl).1, (A3 l hl).2.1, (A3 l hl).2.2.1, (A3 l hl).2.2.2]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [d.1 e he, (idx l hl e he).1]
    · rw [d.2 e he, (idx l hl e he).2]
  have LZ : ∀ l < 2, ZLanes (s5.lane .xmm13 l) (fun e => gamma (pairY i l e)) := fun l hl e he => by
    rw [Z5 l hl, m4, g4, hI.r8, word_readW _ _ he, wAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 2 * (16 * i) + (0 + (16 * l + 2 * e)) = 2 * (16 * i + 8 * l + e) by omega, ← wAddr, ← wordAt,
      hI.tab _ (by omega), gTabY, gIdxY_eq hl he, gTab_eq]
  have R5 : ∀ l < 2, s5.lane .xmm12 l = r2V := fun l hl => by rw [o15.lane _ (by decide) l hl, hI.r2 l hl]
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_vbase (P := fun l t =>
      Lanes (t.xmm .xmm1) (fun e => (F s₀)[2 * pairY i l e]! * (G s₀)[2 * pairY i l e]! +
        (F s₀)[2 * pairY i l e + 1]! * (G s₀)[2 * pairY i l e + 1]! * gamma (pairY i l e)) ∧
      Lanes (t.xmm .xmm2) (fun e => (F s₀)[2 * pairY i l e]! * (G s₀)[2 * pairY i l e + 1]! +
        (F s₀)[2 * pairY i l e + 1]! * (G s₀)[2 * pairY i l e]!))
    fun l hl => WP.mono (vbase_ok (c5 l hl) (R5 l hl) (LF l hl).1 (LF l hl).2 (LG l hl).1 (LG l hl).2 (LZ l hl))
      fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩) fun s6 ⟨V6, o6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_vinterS (P := fun l t =>
      t.xmm .xmm1 = (interV (s6.lane .xmm1 l) (s6.lane .xmm2 l))[0]! ∧
        t.xmm .xmm5 = (interV (s6.lane .xmm1 l) (s6.lane .xmm2 l))[1]! ∧
        t.xmm .xmm3 = (interV (s6.lane .xmm1 l) (s6.lane .xmm2 l))[2]! ∧
        t.xmm .xmm6 = (interV (s6.lane .xmm1 l) (s6.lane .xmm2 l))[3]!)
    fun l _ => vinterS_ok (s6.proj l)) fun s7 ⟨I7, o7⟩ => ?_
  have o17 := (o15.trans o6).trans o7
  have hw7 : ∀ t < 4, InRegions s7.wr (s7.gpr .rdi + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [o17.wr, o17.gpr, hI.wr, hI.rdi, hp.2.1, show 32 * t = 4 * (8 * t) by omega, coeffAddr_off]
    exact ⟨pR (hP s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) := by decide
  have w0 : InRegions s7.wr (s7.gpr .rdi) 32 := by simpa using hw7 0 (by decide)
  have w1 : InRegions s7.wr (s7.gpr .rdi + BitVec.ofNat 64 32) 32 := hw7 1 (by decide)
  have w2 : InRegions s7.wr (s7.gpr .rdi + BitVec.ofNat 64 64) 32 := hw7 2 (by decide)
  have w3 : InRegions s7.wr (s7.gpr .rdi + BitVec.ofNat 64 96) 32 := hw7 3 (by decide)
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, w0, w1, w2, w3,
    State.setMem_ymm, State.setMem_setMem, sx128, sx32]
  -- the values stored
  have Y7 : ∀ t < 4, ∀ l < 2, ∀ j' < 4,
      (([s7.ymm .xmm1, s7.ymm .xmm5, s7.ymm .xmm3, s7.ymm .xmm6][t]!).extractLsb' (8 * (4 * (4 * l + j'))) (8 * 4)).toNat =
        ((multiplyNTTs (F s₀) (G s₀))[32 * i + 8 * t + 4 * l + j']!).val := fun t ht l hl j' hj' => by
    have e : ([s7.ymm .xmm1, s7.ymm .xmm5, s7.ymm .xmm3, s7.ymm .xmm6][t]!).extractLsb' (8 * (4 * (4 * l + j')))
        (8 * 4) = dword ((interV (s6.lane .xmm1 l) (s6.lane .xmm2 l))[t]!) j' := by
      rw [show 4 * (4 * l + j') = 16 * l + 4 * j' by omega]
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] <;> rw [extract_ymm _ _ hl hj']
      exacts [congrArg (dword · j') (I7 l hl).1, congrArg (dword · j') (I7 l hl).2.1,
        congrArg (dword · j') (I7 l hl).2.2.1, congrArg (dword · j') (I7 l hl).2.2.2]
    have iv := inter_val (s6.lane .xmm1 l) (s6.lane .xmm2 l) (k := 4 * t + j') (by omega)
    rw [show (4 * t + j') / 4 = t by omega, show (4 * t + j') % 4 = j' by omega] at iv
    rw [e]
    exact iv.trans (prod_valY hi hl (V6 l hl).1 (V6 l hl).2 ht hj')
  have rdi7 : s7.gpr .rdi = coeffAddr (hP s₀) (32 * i) := by rw [o17.gpr, hI.rdi]
  obtain ⟨out, inr, f8⟩ := ystore4 s7.mem (hP s₀) hj (s7.ymm .xmm1) (s7.ymm .xmm5) (s7.ymm .xmm3) (s7.ymm .xmm6)
  rw [← rdi7] at out inr f8
  have tS : ∀ k < 128, wordAt ((((s7.mem.writeW (s7.gpr .rdi) (s7.ymm .xmm1)).writeW (s7.gpr .rdi + 32#64)
      (s7.ymm .xmm5)).writeW (s7.gpr .rdi + 64#64) (s7.ymm .xmm3)).writeW (s7.gpr .rdi + 96#64)
      (s7.ymm .xmm6)) (sP s₀) k = wordAt s.mem (sP s₀) k := fun k hk => by
    rw [wordAt, f8.readW (r := pR (sP s₀)) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.2.2.2.2.1.symm) (by decide), o17.mem]; rfl
  refine ⟨?_, by rw [o17.gpr], by rw [o17.gpr]⟩
  constructor
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, setReg_mem, setFlags_mem, State.setMem_gpr, State.setMem_rd,
    State.setMem_wr, State.setMem_mem, reduceCtorEq, ite_true, ite_false]
  case rsi => rw [o17.gpr, hI.rsi, coeffAddr_off, Nat.mul_succ]
  case rdx => rw [o17.gpr, hI.rdx, coeffAddr_off, Nat.mul_succ]
  case rdi => rw [rdi7, coeffAddr_off, Nat.mul_succ]
  case r8 => rw [o17.gpr, hI.r8, show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ]
  case rd => rw [o17.rd, hI.rd]
  case wr => rw [o17.wr, hI.wr]
  case c =>
    refine lanes_gpr (s := s7) ?_ o17 hI.c (by decide) (by decide)
    intro r l; simp only [lane_setReg, lane_setFlags, State.setMem_lane]
  case r2 =>
    intro l hl
    simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    rw [← hI.r2 l hl]; exact o17.lane _ (by decide) l hl
  case frame => exact hI.frame.trans (by rw [← o17.mem]; exact f8.mono (by simp))
  case tab => exact fun k hk => by rw [tS k hk]; exact hI.tab k hk
  case done =>
    intro k hk
    by_cases hk' : k < 32 * i
    · rw [out k (by omega) (.inl hk'), o17.mem]; exact hI.done k hk'
    · obtain ⟨t, l, j', ht, hl, hj', rfl⟩ : ∃ t l j', t < 4 ∧ l < 2 ∧ j' < 4 ∧ k = 32 * i + 8 * t + 4 * l + j' :=
        ⟨(k - 32 * i) / 8, (k - 32 * i) % 8 / 4, (k - 32 * i) % 4, by omega, by omega, by omega, by omega⟩
      rw [show 32 * i + 8 * t + 4 * l + j' = 32 * i + 8 * t + (4 * l + j') by omega, inr t ht _ (by omega),
        ← show 32 * i + 8 * t + 4 * l + j' = 32 * i + 8 * t + (4 * l + j') by omega]
      exact Y7 t ht l hl j' hj'

omit hp in
theorem consts_ok (s : State) :
    WP isa (.block (yconsts ++ yconst .xmm12 0x05490549 ++ ([.mov .r8 (.reg .r10)] : List Instr))) s fun s' =>
      YConsts s' ∧ (∀ l < 2, s'.lane .xmm12 l = r2V) ∧ s'.gpr .r8 = s.gpr .r10 ∧ s'.mem = s.mem ∧
        s'.mxcsr = s.mxcsr ∧ Keep [.rax, .r8] s s' := by
  simp only [yconsts]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨q1, k1, m1, x1, o1⟩ => ?_
  refine WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨q2, k2, m2, x2, o2⟩ => ?_
  refine WP.mono (yconst_ok .xmm12 _ s2) fun s3 ⟨q3, k3, m3, x3, o3⟩ => ?_
  vrunm
  refine ⟨fun l hl => ⟨?_, ?_⟩, fun l hl => ?_, ?_, by rw [m3, m2, m1], by rw [x3, x2, x1], ?_⟩
  · simp only [State.proj_xmm, lane_setReg]
    rw [o3 _ (by decide) l hl, o2 _ (by decide) l hl, q1 l hl]; decide
  · simp only [State.proj_xmm, lane_setReg]
    rw [o3 _ (by decide) l hl, q2 l hl]; decide
  · simp only [lane_setReg]; rw [q3 l hl]; decide
  · rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_setReg_of_ne _ _ hr.2, k3.gpr (by simpa using hr.1), k2.gpr (by simpa using hr.1),
        k1.gpr (by simpa using hr.1)], by rw [RegUpd.rd_setReg, k3.2.1, k2.2.1, k1.2.1],
      by rw [RegUpd.wr_setReg, k3.2.2, k2.2.2, k1.2.2]⟩

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTsAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧
    mulK.post s₀ s' := by
  have hw : pR (sP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa Impl.MlKem.X86_64.multiplyNTTsAvx2 s₀ fun s' => ∃ s3,
      (PolyIs s3.mem (hP s₀) (multiplyNTTs (F s₀) (G s₀)) ∧ Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s3.mem) ∧
      Frame [mxR (sP s₀)] s3.mem s'.mem ∧ Keep [] s3 s' := by
    unfold Impl.MlKem.X86_64.multiplyNTTsAvx2
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r10 = sP s₀ ∧ s1.mem = s₀.mem ∧
      Keep [.r10] s₀ s1) (by
        vrunm
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h10, hm1, k1⟩ => ?_)
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9] (by decide) h10
      (by rw [k1.2.2]; exact hw) ?_ fun s2 k2 f2 => ?_
    · decide +kernel
    have k12 := k1.trans k2
    have h10' : s2.gpr .r10 = sP s₀ := by rw [k2.gpr (by decide), h10]
    refine WP.seq ?_
    simp only [mulProY, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wordTab_gen gTabY gTabY_lt (by decide) h10' (by rw [k12.2.2]; exact hw))
      fun s3 ⟨ht, f3, k3, _, _⟩ => ?_
    rw [← List.append_assoc]
    refine WP.mono (consts_ok s3) fun s4 ⟨hc4, hr4, h84, hm4, _, k4⟩ => ?_
    have h84' : s4.gpr .r8 = sP s₀ := by rw [h84, k3.gpr (by decide), h10']
    have k14 := (k12.trans k3).trans k4
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (Inv s₀) (fun s g hy _ => ?_)
      fun i hi s hI => step hp hi hI) fun s5 hI => ?_)
    · have k := k14.trans g.keep
      have hl : ∀ r l, s.lane r l = s4.lane r l := fun r l => by
        simp only [State.lane]; rw [g.xmm, hy]
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, ?_, fun _ h => absurd h (by omega)⟩
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [g.keep.gpr (by decide), h84']; exact (add_ofNat_zero _).symm
      · exact fun l hl' => ⟨by rw [State.proj_xmm, hl]; exact (hc4 l hl').q,
          by rw [State.proj_xmm, hl]; exact (hc4 l hl').qinv⟩
      · exact fun l hl' => by rw [hl]; exact hr4 l hl'
      · rw [g.mem, hm4, ← hm1]
        refine (frame_fs (fP := hP s₀) f2 ?_).trans (frame_fs f3 ?_) <;>
          intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
        exacts [.inr (mx_sub _), .inr (pR_sub_tab _)]
      · intro k hk; rw [g.mem, hm4]; exact ht k hk
    · vrunm
      exact ⟨polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega), hI.frame⟩
  obtain ⟨t, s', he, ⟨s3, ⟨hP', hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.2.2.2.2.1.sub_right (mx_sub _)) hP'

end

end MulY

theorem mulY_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTsAvx2 s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  MulY.correct hs

theorem mulY_ct : ConstantTime isa mulK.pre mulK.pub Impl.MlKem.X86_64.multiplyNTTsAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2])
    (by taint_decide)

theorem mulY_verified :
    Verified X86_64.target Impl.MlKem.X86_64.multiplyNTTsAvx2 (Spec.MlKem.mulContract X86_64.abi) :=
  Verified.of_correct mulY_correct mulY_ct (by
    mlkem_implies [Spec.MlKem.mulContract, Spec.MlKem.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlKem.X86_64
