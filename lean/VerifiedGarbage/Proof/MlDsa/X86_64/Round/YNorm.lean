import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec

/-!
# ML-DSA on x86-64: `vg_mldsa_norm_lt_avx2`

With the bound clamped to `b ≤ q` (which changes no result, `good_clamp`),
each doubleword of `ymm10` keeps its top bit while every coefficient it has
seen is good (`Good b a`: `a < b` or `q - a < b`, `nlL_msb`); at the end the
top bits of the 32 bytes are all set exactly when every coefficient is good
(`allOnes_bsum`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes ifp ifn)
open VG.Impl.MlKem.X86_64 (xb xmov toY)
open VG.Proof.MlDsa.X86_64.Arith (dword_psubd dword_pand dword_psrad)
open VG.Proof.MlKem.X86_64.S4 (bsum bsum_lt byteMask_eq)
open VG.Proof.MlDsa.X86_64.Arith (bc)

/-! ## A doubleword -/

/-- The top bit of a difference of doublewords below `2³¹`: whether it borrows. -/
theorem msb_sub32 {u v : BitVec 32} (hu : u.toNat < 2 ^ 31) (hv : v.toNat < 2 ^ 31) :
    (u - v).msb = decide (u.toNat < v.toNat) := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
  by_cases h : u.toNat < v.toNat
  · rw [decide_eq_true h, decide_eq_true_iff]; omega
  · rw [decide_eq_false h, decide_eq_false_iff_not]; omega

/-- What `nlX` ORs into a doubleword: `(a - b) | ((q - b) - a)`. -/
def nlL (a b c : BitVec 32) : BitVec 32 := (a - b) ||| (c - a)

theorem nlL_msb {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat ≤ q) :
    (nlL a b (BitVec.ofNat 32 (q - b.toNat))).msb = decide (Good b.toNat a.toNat) := by
  rw [q_eq] at ha hb
  have hc : (BitVec.ofNat 32 (q - b.toNat)).toNat = q - b.toNat := by rw [BitVec.toNat_ofNat, q_eq]; omega
  rw [nlL, BitVec.msb_or, msb_sub32 (by omega) (by omega), msb_sub32 (by rw [hc, q_eq]; omega) (by omega), hc]
  simp only [Good, Bool.decide_or, q_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  omega

/-- Clamping the bound to `q` changes no coefficient's goodness. -/
theorem good_clamp {B a : Nat} (ha : a < q) : Good (min B q) a ↔ Good B a := by
  simp only [Good]
  constructor
  · rintro (h | h) <;> [left; right] <;> omega
  · intro h
    by_cases hB : B ≤ q
    · rw [Nat.min_eq_left hB]; exact h
    · rw [Nat.min_eq_right (by omega)]; left; exact ha

/-! ## The mask -/

theorem bsum_allOnes (f : Nat → Bool) : ∀ n, bsum f n = 2 ^ n - 1 ↔ ∀ i < n, f i = true
  | 0 => by simp [bsum]
  | n + 1 => by
    have hl := bsum_lt f n
    have ih := bsum_allOnes f n
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [bsum, Nat.pow_succ]
    generalize 2 ^ n = N at hl ih h1 ⊢
    constructor
    · intro h i hi
      have hfn : f n = true := by
        cases e : f n
        · simp only [e, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h; omega
        · rfl
      rw [hfn] at h
      simp only [Bool.toNat_true, Nat.one_mul] at h
      rcases (by omega : i < n ∨ i = n) with hi | rfl
      · exact (ih.mp (by omega)) i hi
      · exact hfn
    · intro h
      rw [ih.mpr fun i hi => h i (by omega), h n (by omega)]
      simp only [Bool.toNat_true, Nat.one_mul]
      omega

/-- A bit of a 256-bit register, in its lanes and doublewords. -/
theorem ymm_bit (s : State) (r : XReg) {i : Nat} (hi : i < 32) :
    (s.ymm r).getLsbD (8 * i + 7) = (dword (s.lane r (i / 16)) (i % 16 / 4)).getLsbD (8 * (i % 4) + 7) := by
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    show 8 * (i % 4) + 7 < 32 by omega, decide_true, Bool.true_and]
  by_cases h : i < 16
  · rw [ite_eq_left (show 8 * i + 7 < 128 by omega), ite_eq_left (show i / 16 = 0 by omega),
      show 32 * (i % 16 / 4) + (8 * (i % 4) + 7) = 8 * i + 7 by omega]
  · rw [ite_eq_right (show ¬ 8 * i + 7 < 128 by omega), ite_eq_right (show ¬ i / 16 = 0 by omega),
      show 32 * (i % 16 / 4) + (8 * (i % 4) + 7) = 8 * i + 7 - 128 by omega]

/-- A doubleword spread from its top bit. -/
theorem bit_of_spread {d : BitVec 32} (h : d = 0 ∨ d = BitVec.allOnes 32) {j : Nat} (hj : j < 32) :
    d.getLsbD j = d.msb := by
  rcases h with rfl | rfl
  · simp
  · rw [BitVec.msb_allOnes (by decide), BitVec.getLsbD_allOnes]; simp [hj]

/-! ## The code on a register -/

theorem nlX_ok (s : State) :
    WP isa (.block nlX) s fun s' => (∀ e < 4, dword (s'.xmm .xmm10) e =
      dword (s.xmm .xmm10) e &&& nlL (dword (s.xmm .xmm0) e) (dword (s.xmm .xmm8) e) (dword (s.xmm .xmm9) e)) ∧
      XOnly [.xmm1, .xmm2, .xmm10] s s' := by
  simp only [nlX, xmov, xb]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨fun e he => ?_, by xonly⟩
  simp only [dword_pand, dword_por, dword_psubd _ _ he]
  rfl

theorem lane_nlX : laneSseBlock (toY nlX) = some nlX := by decide +kernel

/-- `rax`'s low doubleword in each doubleword of `ymm r`. -/
theorem ybc_ok (r : XReg) (s : State) :
    WP isa (.block (ybcast r)) s fun s' =>
      (∀ l < 2, s'.lane r l = bc ((s.gpr .rax).setWidth 32)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧ ∀ r' ≠ r, ∀ l < 2, s'.lane r' l = s.lane r' l := by
  apply WP.of_runBlock
  simp only [ybcast, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, rfl, fun r' hr' l hl => ?_⟩
  · rw [State.lane_setV256, ifp rfl]
    have : dword ((s.setV .l128 r ((0 : BitVec 64) ++ s.gpr .rax) 0).xmm r) 0 = (s.gpr .rax).setWidth 32 := by
      rw [RegUpd.xmm_setV, ifp rfl]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [dword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_append, ifp (by omega), BitVec.getLsbD_setWidth]
      simp [show i < 64 by omega, hi]
    rcases lane01 hl with rfl | rfl <;> simp only [ite_true, ite_false, this, Nat.one_ne_zero] <;> rfl
  · rw [State.lane_setV256, ifn hr', State.lane_setV128, ifn hr']

end VG.Proof.MlDsa.X86_64.Round

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Round (Good nlL nlL_msb nlX_ok lane_nlX bc_ofDwords)
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok ifp ifn ptr_step add_ofNat_zero lane_setReg lane_setFlags)
open VG.Spec.MlDsa (q n coeffAt Reduced)

namespace YNormL

/-- After `i` vectors of eight: the top bit of doubleword `e` of lane `l` of
`ymm10` is whether coefficients `8j + 4l + e`, `j < i`, are good. -/
structure Inv (s₀ : State) (b : BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  c8 : ∀ l < 2, s.lane .xmm8 l = bc b
  c9 : ∀ l < 2, s.lane .xmm9 l = bc (BitVec.ofNat 32 (q - b.toNat))
  acc : ∀ l < 2, ∀ e < 4, (dword (s.lane .xmm10 l) e).msb = true ↔
    ∀ j < i, Good b.toNat (coeffAt s₀.mem (s₀.gpr .rdi) (8 * j + 4 * l + e)).toNat

theorem step {s₀ : State} (hrd : pR (s₀.gpr .rdi) ∈ s₀.rd) (hr : Reduced s₀.mem (s₀.gpr .rdi)) {b : BitVec 32}
    (hb : b.toNat ≤ q) {i : Nat} (hi : i < 32) {s : State} (hI : Inv s₀ b i s) :
    WP isa (.block (nlBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ b (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hr' : pR (s₀.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hI.rd]; exact List.mem_append_left _ hrd
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  rw [nlBodyY, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 hr' j0)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_nlX (P := fun l t => ∀ e < 4, dword (t.xmm .xmm10) e =
      dword ((s1.proj l).xmm .xmm10) e &&& nlL (dword ((s1.proj l).xmm .xmm0) e) (dword ((s1.proj l).xmm .xmm8) e)
        (dword ((s1.proj l).xmm .xmm9) e)) fun l hl => nlX_ok _) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o1.trans o3
  vrund
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_, fun l hl e he => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [o13.wr, hI.wr]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; rw [o13.mem, hI.mem]
  · simp only [lane_setReg, lane_setFlags]; rw [o13.lane _ (by decide) l hl, hI.c8 l hl]
  · simp only [lane_setReg, lane_setFlags]; rw [o13.lane _ (by decide) l hl, hI.c9 l hl]
  · simp only [lane_setReg, lane_setFlags]
    have hx : dword ((s1.proj l).xmm .xmm0) e = coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e) := by
      rw [State.proj_xmm, L1 l hl, e1, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hI.mem]
    have h8 : dword ((s1.proj l).xmm .xmm8) e = b := by
      rw [State.proj_xmm, o1.lane _ (by decide) l hl, hI.c8 l hl]; exact bc_ofDwords _ e he
    have h9 : dword ((s1.proj l).xmm .xmm9) e = BitVec.ofNat 32 (q - b.toNat) := by
      rw [State.proj_xmm, o1.lane _ (by decide) l hl, hI.c9 l hl]; exact bc_ofDwords _ e he
    have h10 : (s1.proj l).xmm .xmm10 = s.lane .xmm10 l := by rw [State.proj_xmm, o1.lane _ (by decide) l hl]
    rw [← State.proj_xmm, B3 l hl e he, BitVec.msb_and, Bool.and_eq_true, hx, h8, h9, h10,
      nlL_msb (by rw [← VG.Proof.MlDsa.Round.n_eq] at *; exact hr _ (by rw [VG.Proof.MlDsa.Round.n_eq]; omega)) hb,
      decide_eq_true_iff, hI.acc l hl e he]
    refine ⟨fun ⟨h₁, h₂⟩ j hj => ?_, fun h => ⟨fun j hj => h j (by omega), h i (by omega)⟩⟩
    rcases (by omega : j < i ∨ j = i) with hj | rfl
    exacts [h₁ j hj, h₂]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

end YNormL

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of XOnly YOnly ylanes yconst_ok ifp ifn)
open VG.Proof.MlDsa.X86_64.Arith (bc dword_psrad sshiftRight31)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Proof.MlKem.X86_64.S4 (bsum byteMask_eq)

theorem sw3264 (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 y) = y := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]; have := y.isLt; omega

/-- The bound, clamped to `q`. -/
theorem nlPro_ok (s₀ : State) :
    WP isa nlPro s₀ fun s₂ => (s₂.mem = s₀.mem ∧ ((s₂.gpr .rsi).setWidth 32).toNat = min (arg32 s₀ .rsi) q) ∧
        Keep [.rsi] s₀ s₂ := by
  unfold nlPro
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => (s₁.cf = some (decide (((s₀.gpr .rsi).setWidth 32).toNat < q)) ∧
      s₁.mem = s₀.mem ∧ s₁.gpr .rsi = BitVec.setWidth 64 ((s₀.gpr .rsi).setWidth 32)) ∧ Keep [.rsi] s₀ s₁)
    (by refine WP.keep _ ?_ (by decide); xrun; rfl)
    fun s₁ ⟨⟨hc, hm, hsi⟩, hk⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from hc) (fun h => ?_) (fun h => ?_)
  · rw [decide_eq_true_iff] at h
    refine WP.mono (Q := fun s₂ => s₂ = s₁) (by vrund) fun s₂ e => ?_
    subst e
    refine ⟨⟨hm, ?_⟩, hk⟩
    rw [hsi, sw3264, Nat.min_eq_left (by unfold arg32; omega)]
  · rw [decide_eq_false_iff_not] at h
    refine WP.mono (Q := fun (s₂ : State) => (s₂.gpr .rsi = BitVec.setWidth 64 qImm ∧ s₂.mem = s₁.mem) ∧
      Keep [.rsi] s₁ s₂) (by refine WP.keep _ ?_ (by decide); xrun) fun s₂ ⟨⟨h1, h2⟩, k2⟩ => ?_
    refine ⟨⟨h2.trans hm, ?_⟩, (hk.trans k2).mono (by simp)⟩
    rw [h1, Nat.min_eq_right (by unfold arg32; omega)]; rfl

theorem qsub_eq {x : BitVec 32} (hx : x.toNat ≤ q) : qImm - x = BitVec.ofNat 32 (q - x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show qImm.toNat = q from rfl]
  rw [q_eq] at hx ⊢; omega

/-- The constants of the loop: `b`, `q - b` and all ones. -/
theorem nlConsts_ok (s : State) (hb : ((s.gpr .rsi).setWidth 32).toNat ≤ q) :
    WP isa (.block nlConsts) s fun s' =>
      (∀ l < 2, s'.lane .xmm8 l = bc ((s.gpr .rsi).setWidth 32) ∧
        s'.lane .xmm9 l = bc (BitVec.ofNat 32 (q - ((s.gpr .rsi).setWidth 32).toNat)) ∧
        s'.lane .xmm10 l = bc (BitVec.allOnes 32)) ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  simp only [nlConsts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => (s1.gpr .rax = BitVec.setWidth 64 ((s.gpr .rsi).setWidth 32) ∧
      s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr ∧ ∀ r l, s1.lane r l = s.lane r l) ∧ Keep [.rax] s s1)
    (by refine WP.keep _ ?_ (by decide); xrun; exact ⟨rfl, fun _ _ => rfl⟩) fun s1 ⟨⟨a1, m1, x1, l1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ybc_ok .xmm8 s1) fun s2 ⟨c2, g2, m2, r2, w2, x2, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s3 : State) => (s3.gpr .rax = BitVec.setWidth 64 (qImm - (s2.gpr .rsi).setWidth 32) ∧
      s3.mem = s2.mem ∧ s3.mxcsr = s2.mxcsr ∧ ∀ r l, s3.lane r l = s2.lane r l) ∧ Keep [.rax] s2 s3)
    (by refine WP.keep _ ?_ (by decide); xrun; exact ⟨rfl, fun _ _ => rfl⟩) fun s3 ⟨⟨a3, m3, x3, l3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ybc_ok .xmm9 s3) fun s4 ⟨c4, g4, m4, r4, w4, x4, o4⟩ => ?_
  refine WP.mono (yconst_ok .xmm10 _ s4) fun s5 ⟨c5, k5, m5, x5, o5⟩ => ?_
  have e2 : s2.gpr .rsi = s.gpr .rsi := by rw [g2, k1.gpr (by decide)]
  refine ⟨fun l hl => ⟨?_, ?_, ?_⟩, ?_, by rw [m5, m4, m3, m2, m1], by rw [x5, x4, x3, x2, x1]⟩
  · rw [o5 _ (by decide) l hl, o4 _ (by decide) l hl, l3, c2 l hl, a1, sw3264]
  · rw [o5 _ (by decide) l hl, c4 l hl, a3, e2, sw3264, qsub_eq hb]
  · rw [c5 l hl]; rfl
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [k5.gpr hr, g4, k3.gpr hr, g2, k1.gpr hr]
    · rw [k5.2.1, r4, k3.2.1, r2, k1.2.1]
    · rw [k5.2.2, w4, k3.2.2, w2, k1.2.2]

theorem lane_psrad : laneSseBlock (toY [.xop (.shift .psrad .xmm10 31)]) = some [.xop (.shift .psrad .xmm10 31)] := by
  decide +kernel

/-- Whether every doubleword of `ymm10` has its top bit set. -/
def allMsb (s : State) : Bool := (List.range 2).all fun l => (List.range 4).all fun e => (dword (s.lane .xmm10 l) e).msb

/-- The end: 1 if every doubleword of `ymm10` has its top bit set, and 0 otherwise. -/
theorem nlEnd_ok (s : State) :
    WP isa (.block nlEnd) s fun s' =>
      ((s'.gpr .rax).setWidth 32 = if allMsb s = true then 1 else 0) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  rw [nlEnd, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ylanes lane_psrad (rs := [.xmm10]) (P := fun l t => ∀ e < 4,
    dword (t.xmm .xmm10) e = (dword ((s.proj l).xmm .xmm10) e).sshiftRight (min (31 : BitVec 8).toNat 32))
    fun l hl => by vrun; exact ⟨fun e he => dword_psrad _ _ he, by xonly⟩) fun s1 ⟨B1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s2 : State) => s2.gpr = (s1.setReg .rax (byteMask (s1.ymm .xmm10) 32)).gpr ∧
    s2.mem = s1.mem ∧ s2.rd = s1.rd ∧ s2.wr = s1.wr) (by vrund; exact ⟨rfl, rfl, rfl, rfl⟩) fun s2 ⟨g2, m2, r2, w2⟩ => ?_
  xrun
  have hf : ∀ i < 32, (s1.ymm .xmm10).getLsbD (8 * i + 7) = (dword (s.lane .xmm10 (i / 16)) (i % 16 / 4)).msb :=
    fun i hi => by
      have hl : i / 16 < 2 := by omega
      have he : i % 16 / 4 < 4 := by omega
      have hd := B1 (i / 16) hl (i % 16 / 4) he
      rw [State.proj_xmm, State.proj_xmm, sshiftRight31] at hd
      rw [ymm_bit _ _ hi, hd]
      split
      · rename_i h
        rw [BitVec.msb_eq_decide]; simp [h]
      · rename_i h
        rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.getLsbD_allOnes, BitVec.msb_eq_decide]
        simp only [decide_eq_true (show 8 * (i % 4) + 7 < 32 by omega)]
        rw [decide_eq_true (by omega)]
  have hall : allMsb s = true ↔ ∀ i < 32, (s1.ymm .xmm10).getLsbD (8 * i + 7) = true := by
    simp only [allMsb, List.all_eq_true, List.mem_range]
    constructor
    · intro h i hi; rw [hf i hi]; exact h _ (by omega) _ (by omega)
    · intro h l hl e he
      have := h (16 * l + 4 * e) (by omega)
      rwa [hf _ (by omega), show (16 * l + 4 * e) / 16 = l by omega, show (16 * l + 4 * e) % 16 / 4 = e by omega]
        at this
  have hb := VG.Proof.MlKem.X86_64.S4.bsum_lt (fun i => (s1.ymm .xmm10).getLsbD (8 * i + 7)) 32
  have hax : s2.gpr .rax = BitVec.ofNat 64 (bsum (fun i => (s1.ymm .xmm10).getLsbD (8 * i + 7)) 32) := by
    rw [g2, RegUpd.gpr_setReg_self, byteMask_eq _ (by decide)]
  refine ⟨?_, by rw [m2, o1.mem], by rw [r2, o1.rd], by rw [w2, o1.wr], fun r hr => ?_⟩
  · rw [hax]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    have e1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [e1]
    by_cases h : allMsb s = true
    · rw [ite_eq_left h, (bsum_allOnes _ 32).mpr (hall.mp h)]; rfl
    · rw [ite_eq_right h]
      have : bsum (fun i => (s1.ymm .xmm10).getLsbD (8 * i + 7)) 32 ≠ 2 ^ 32 - 1 := fun e =>
        h (hall.mpr ((bsum_allOnes _ 32).mp e))
      show _ = 0
      omega
  · rw [ite_eq_right hr, ite_eq_right hr, g2, RegUpd.gpr_setReg_of_ne _ _ hr, o1.gpr]

section
variable {s₀ : State} (hp : normLtK.pre s₀)
include hp

theorem normLtY_wp : WP isa normLtAvx2 s₀ fun s' =>
    ((s'.gpr .rax).setWidth 32 = if normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi then 1 else 0) ∧
      Frame [] s₀.mem s'.mem := by
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2
  have hrd : pR (s₀.gpr .rdi) ∈ s₀.rd := by rw [hp.1]; simp
  unfold normLtAvx2
  refine WP.seq (WP.mono (nlPro_ok s₀) fun s₂ ⟨⟨hm2, hb2⟩, k2⟩ => ?_)
  have hbq : ((s₂.gpr .rsi).setWidth 32).toNat ≤ q := by rw [hb2]; exact Nat.min_le_right _ _
  refine WP.seq (WP.mono (nlConsts_ok s₂ hbq) fun s₃ ⟨hc, k3, m3, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoopY (N := 32) (by decide) (by decide)
    (Arith.YNormL.Inv s₀ ((s₂.gpr .rsi).setWidth 32)) (fun u o hy _ => ⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl e he => ?_⟩) fun i hi u hI => Arith.YNormL.step hrd hr hbq hi hI) fun s₄ hI => ?_)
  · rw [o.keep.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), Nat.mul_zero,
      VG.Proof.MlKem.X86_64.add_ofNat_zero]
  · rw [o.keep.2.1, k3.2.1, k2.2.1]
  · rw [o.keep.2.2, k3.2.2, k2.2.2]
  · rw [o.mem, m3, hm2]
  · simp only [State.lane]; rw [o.xmm, hy]; exact (hc l hl).1
  · simp only [State.lane]; rw [o.xmm, hy]; exact (hc l hl).2.1
  · have : u.lane .xmm10 l = bc (BitVec.allOnes 32) := by simp only [State.lane]; rw [o.xmm, hy]; exact (hc l hl).2.2
    rw [this, show dword (bc (BitVec.allOnes 32)) e = BitVec.allOnes 32 from bc_ofDwords _ e he]
    exact iff_of_true (by decide) fun j hj => absurd hj (Nat.not_lt_zero j)
  refine WP.mono (nlEnd_ok s₄) fun s' ⟨hv, hm', _, _, _⟩ => ⟨?_, ?_⟩
  · have hnorm : normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi ↔ allMsb s₄ = true := by
      rw [normRq_lt]
      simp only [allMsb, List.all_eq_true, List.mem_range]
      constructor
      · intro h l hl e he
        rw [(hI.acc l hl e he)]
        intro j hj
        have hk : 8 * j + 4 * l + e < 256 := by omega
        have := h _ hk
        rw [normZq_lt, polyAt_val hr hk] at this
        rw [hb2]
        exact (good_clamp (by rw [← VG.Proof.MlDsa.Round.n_eq] at *; exact hr _ hk)).mpr this
      · intro h k hk
        have hk' : k < 256 := by rw [VG.Proof.MlDsa.Round.n_eq] at hk; exact hk
        have := (hI.acc (k % 8 / 4) (by omega) (k % 4) (by omega)).mp (h _ (by omega) _ (by omega)) (k / 8) (by omega)
        rw [show 8 * (k / 8) + 4 * (k % 8 / 4) + k % 4 = k by omega, hb2] at this
        rw [normZq_lt, polyAt_val hr hk]
        exact (good_clamp (by rw [← VG.Proof.MlDsa.Round.n_eq] at *; exact hr _ hk)).mp this
    rw [hv]
    by_cases h : allMsb s₄ = true
    · rw [ite_eq_left h, ite_eq_left (hnorm.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hnorm.mp h'))]
  · rw [hm', hI.mem]; exact Frame.refl _ _

theorem normLtY_correct : ∃ t s', Exec isa normLtAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ normLtK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rsi, .rdi] (normLtY_wp hp) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf (by simp)), hv⟩

end

theorem normLtY_ct : ConstantTime isa normLtK.pre normLtK.pub normLtAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.1, hp.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2)
    (by taint_decide)

theorem normLtY_verified : Verified X86_64.target normLtAvx2 (normLtContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => normLtY_correct hp) normLtY_ct (by
    round_implies [normLtContract, normLtSig, normLtK, X86_64.abi, X86_64.argRegs] [normSat] using normSat)

end VG.Proof.MlDsa.X86_64.Round
