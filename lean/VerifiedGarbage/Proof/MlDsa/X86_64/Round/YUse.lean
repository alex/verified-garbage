import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint

/-!
# ML-DSA on x86-64: `vg_mldsa_use_hint_avx2`

Untrusted: everything here is checked by Lean. In each doubleword, `uhX`
computes `uhL` of the hint and the coefficient of `r` (`uhX_ok`), which is
the value `vg_mldsa_use_hint` stores (`uhL_toNat`, as `uhS_toNat`); the loop
stores eight of them in each iteration (`YUseL.step`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (XOnly ifp ifn)
open VG.Impl.MlKem.X86_64 (xb xmov toY)
open VG.Proof.MlDsa.X86_64.Arith (dword_psubd dword_pand dword_psrad sshiftRight31)

/-! ## A doubleword -/

/-- `x - m`, plus `m` if negative, as `msub` computes it. -/
def msubL (g : Nat) (x : BitVec 32) : BitVec 32 :=
  (x - BitVec.ofNat 32 (dMod g)) +
    ((x - BitVec.ofNat 32 (dMod g)).sshiftRight (min (31 : BitVec 8).toNat 32) &&& BitVec.ofNat 32 (dMod g))

/-- What `uhX` computes from the hint `h` and the coefficient `a`. -/
def uhL (g : Nat) (h a : BitVec 32) : BitVec 32 :=
  msubL g (msubL g (hbFL g a + (~~~((mul2L g (hbFL g a) - a).sshiftRight (min (31 : BitVec 8).toNat 32) +
      (mul2L g (hbFL g a) - a).sshiftRight (min (31 : BitVec 8).toNat 32)) &&&
    ((0 - h) ||| h).sshiftRight (min (31 : BitVec 8).toNat 32)) + BitVec.ofNat 32 (dMod g)))

theorem msubL_toNat (g : Nat) (hm : dMod g ≤ 44) {y : BitVec 32} (hy : y.toNat < 2 ^ 31) :
    (msubL g y).toNat = if y.toNat < dMod g then y.toNat else y.toNat - dMod g := by
  have hsub : (y - BitVec.ofNat 32 (dMod g)).toNat = (y.toNat + 2 ^ 32 - dMod g) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dMod g < 2 ^ 32 by omega)]; omega
  unfold msubL
  rw [sshiftRight31]
  split
  · rename_i h
    rw [hsub] at h
    rw [show (0 : BitVec 32) &&& BitVec.ofNat 32 (dMod g) = 0 from BitVec.zero_and,
      show ∀ x : BitVec 32, x + 0 = x from fun x => BitVec.add_zero x, hsub,
      ifn (by omega)]
    omega
  · rename_i h
    rw [hsub] at h
    rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.allOnes_and, BitVec.sub_add_cancel,
      ifp (by omega)]

/-- The sign of `h | -h` is set exactly when `h` is not 0. -/
theorem nz_mask (h : BitVec 32) :
    ((0 - h) ||| h).sshiftRight (min (31 : BitVec 8).toNat 32) = if h ≠ 0 then -1 else 0 := by
  rw [sshiftRight31]
  by_cases e : h = 0
  · subst e; rfl
  · have h0 : h.toNat ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    have en : (0 - h).toNat = 2 ^ 32 - h.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]; have := h.isLt; omega
    have hm : (0 - h ||| h).msb = true := by
      rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, en]
      have := h.isLt
      by_cases hb : 2 ^ 31 ≤ h.toNat
      · simp [hb]
      · simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    have h2 := BitVec.msb_eq_decide (0 - h ||| h)
    rw [hm] at h2
    have h3 : 2 ^ 31 ≤ (0 - h ||| h).toNat := of_decide_eq_true h2.symm
    rw [ite_eq_right (fun h' => absurd h' (by omega)), ifp e]

theorem uhL_toNat {g : Nat} (h : g ∈ gamma2s) (hv : BitVec 32) {a : BitVec 32} (ha : a.toNat < q) :
    (uhL g hv a).toNat = (if hv ≠ 0 then (if hbF g a.toNat * (2 * g) < a.toNat then
      hbF g a.toNat + Proof.MlDsa.Round.hbM g + 1 else hbF g a.toNat + Proof.MlDsa.Round.hbM g - 1)
      else hbF g a.toNat + Proof.MlDsa.Round.hbM g) % Proof.MlDsa.Round.hbM g := by
  have hf := hbF32 h ha
  have hle := hbF_le h ha
  have hm : dMod g ≤ 44 ∧ 16 ≤ dMod g := by unfold dMod; split <;> decide
  have hM := dMod_eq' h
  have hfg : hbF g a.toNat * (2 * g) ≤ q - 1 := by rw [← hbM_mul h]; exact Nat.mul_le_mul_right _ hle
  rw [← hM] at hle ⊢
  have hmul : (mul2L g (hbFL g a)).toNat = hbF g a.toNat * (2 * g) := by
    rw [mul2L_toNat h (by omega), hf]
  have hP : (mul2L g (hbFL g a) - a).sshiftRight (min (31 : BitVec 8).toNat 32) =
      if hbF g a.toNat * (2 * g) < a.toNat then -1 else 0 := by
    rw [sshiftRight31]
    have e : (mul2L g (hbFL g a) - a).toNat = (hbF g a.toNat * (2 * g) + 2 ^ 32 - a.toNat) % 2 ^ 32 := by
      rw [BitVec.toNat_sub, hmul]; omega
    rw [q_eq] at ha hfg
    by_cases c : hbF g a.toNat * (2 * g) < a.toNat
    · rw [ifn (by rw [e]; omega), ifp c]
    · rw [ifp (by rw [e]; omega), ifn c]
  unfold uhL
  rw [hP, nz_mask]
  generalize hx : hbFL g a = F at hf
  have hF := hf
  by_cases hb : hv ≠ 0 <;> by_cases hp : hbF g a.toNat * (2 * g) < a.toNat
  · rw [ifp hb, ifp hp, ifp hb, ifp hp, show ~~~((-1 : BitVec 32) + -1) &&& -1 = 1 by decide]
    have e1 : (F + 1 + BitVec.ofNat 32 (dMod g)).toNat = hbF g a.toNat + dMod g + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hF, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega
    rw [msubL_toNat g hm.1 (by rw [msubL_toNat g hm.1 (by omega), e1]; split <;> omega), msubL_toNat g hm.1 (by omega),
      e1]
    rcases (by unfold dMod; split <;> simp : dMod g = 16 ∨ dMod g = 44) with e | e <;> rw [e] at hle ⊢ <;>
      (repeat' split) <;> omega
  · rw [ifp hb, ifn hp, ifp hb, ifn hp, show ~~~((0 : BitVec 32) + 0) &&& -1 = -1 by decide]
    have e1 : (F + -1 + BitVec.ofNat 32 (dMod g)).toNat = hbF g a.toNat + dMod g - 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hF, BitVec.toNat_ofNat, show (-1 : BitVec 32).toNat = 2 ^ 32 - 1 from rfl]
      omega
    rw [msubL_toNat g hm.1 (by rw [msubL_toNat g hm.1 (by omega), e1]; split <;> omega), msubL_toNat g hm.1 (by omega),
      e1]
    rcases (by unfold dMod; split <;> simp : dMod g = 16 ∨ dMod g = 44) with e | e <;> rw [e] at hle ⊢ <;>
      (repeat' split) <;> omega
  all_goals
    rw [ifn hb, ifn hb, show ∀ x : BitVec 32, x &&& 0 = 0 from fun _ => BitVec.and_zero,
      show ∀ x : BitVec 32, x + 0 = x from fun x => BitVec.add_zero x]
    have e1 : (F + BitVec.ofNat 32 (dMod g)).toNat = hbF g a.toNat + dMod g := by
      rw [BitVec.toNat_add, hF, BitVec.toNat_ofNat]; omega
    rw [msubL_toNat g hm.1 (by rw [msubL_toNat g hm.1 (by omega), e1]; split <;> omega), msubL_toNat g hm.1 (by omega),
      e1]
    rcases (by unfold dMod; split <;> simp : dMod g = 16 ∨ dMod g = 44) with e | e <;> rw [e] at hle ⊢ <;>
      (repeat' split) <;> omega

/-! ## The code on a register -/

theorem dword_pandn (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pandn a b) i = ~~~dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj, show 32 * i + j < 128 by omega]

theorem uhX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) :
    WP isa (.block (uhX g)) s fun s' =>
      (∀ e < 4, dword (s'.xmm .xmm4) e = uhL g (dword (s.xmm .xmm5) e) (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [uhX, hfX, msub, mulX, mul2X_32, mul2X_88, dSh_32, dSh_88, dShift_32, dShift_88, xmov, xb,
      List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | assumption) only [dword_pand, dword_pandn, dword_por, dword_pxor, dword_psrad,
      dword_psubd, dword_psrld, dword_pslld, dword_paddd, hc.c8 e he, hc.c9 e he, hc.c10 e he, BitVec.toNat_ofNat,
      BitVec.xor_self]
    rfl

end VG.Proof.MlDsa.X86_64.Round

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Round (HbC uhL uhX_ok)
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok wp_rcxLoopY ifp ifn ptr_step add_ofNat_zero
  lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Spec.MlDsa (q n coeffAt Reduced gamma2s)

/-- `YC` holds while the lanes of its registers are kept. -/
theorem YC.keep' {g : Nat} {s s' : State} (h : YC g s)
    (hl : ∀ r ∈ [XReg.xmm8, .xmm9, .xmm10, .xmm15], ∀ l < 2, s'.lane r l = s.lane r l) : YC g s' := fun l hl' => by
  rw [hl _ (by simp) l hl', hl _ (by simp) l hl', hl _ (by simp) l hl', hl _ (by simp) l hl']
  exact h l hl'

theorem lane_uhX (g : Nat) (hg : g = g32 ∨ g = g88) : laneSseBlock (toY (uhX g)) = some (uhX g) := by
  rcases hg with rfl | rfl <;> decide +kernel

namespace YUseL

/-- After `i` vectors of eight. -/
structure Inv (s₀ : State) (g : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  r10 : s.gpr .r10 = s₀.gpr .rcx + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  yc : YC g s
  frame : Frame [pR (s₀.gpr .rcx)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rcx) k = if k < 8 * i then
    uhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) else coeffAt s₀.mem (s₀.gpr .rcx) k

section
variable {s₀ : State} (hrd : s₀.rd = [pR (s₀.gpr .rdi), pR (s₀.gpr .rsi)]) (hwr : s₀.wr = [pR (s₀.gpr .rcx)])
  (hdz : (pR (s₀.gpr .rdi)).Disjoint (pR (s₀.gpr .rcx))) (hdr : (pR (s₀.gpr .rsi)).Disjoint (pR (s₀.gpr .rcx)))
  {g : Nat} (hg : g = g32 ∨ g = g88)
include hrd hwr hdz hdr hg

theorem step {i : Nat} (hi : i < 32) {s : State} (hI : Inv s₀ g i s) :
    WP isa (.block (uhBodyY g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ g (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rcx) ∈ s.wr := by rw [hI.wr, hwr]; simp
  have hrz : pR (s₀.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have hrr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega
  have e2 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have e3 : s.gpr .r10 = coeffAddr (s₀.gpr .rcx) (8 * i) := by rw [hI.r10]; congr 2; omega
  rw [uhBodyY, List.append_assoc, List.append_assoc,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 hrr j0)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact f_in32 hrz j0)) fun s2 ⟨L2, o2⟩ => ?_
  have k2 : YC g s2 := hI.yc.keep' fun r hr' l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rw [o2.lane r (by rcases hr' with rfl | rfl | rfl | rfl <;> decide) l hl,
      o1.lane r (by rcases hr' with rfl | rfl | rfl | rfl <;> decide) l hl]
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (lane_uhX g hg) (P := fun l t => ∀ e < 4,
      dword (t.xmm .xmm4) e = uhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e))
    fun l hl => uhX_ok hg _ (k2.hbc hl)) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := (o1.trans o2).trans o3
  have k3 : YC g s3 := k2.keep' fun r hr' l hl => o3.lane r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl <;> decide) l hl
  have g3 : s3.gpr .r10 = coeffAddr (s₀.gpr .rcx) (8 * i) := by rw [o13.gpr, e3]
  have w0 : InRegions s3.wr (s3.gpr .r10) 32 := by rw [o13.wr, g3]; exact f_in32 hw j0
  have hv : ∀ l < 2, ∀ e < 4, uhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) =
      uhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
    fun l hl e he => by
      rw [State.proj_xmm, State.proj_xmm, L2 l hl, o2.lane _ (by decide) l hl, L1 l hl, o1.mem, o1.gpr, e1, e2,
        dword_readW _ _ he, dword_readW _ _ he, lane_load, lane_load, coeffAddr_add, coeffAddr_add, ← coeffAt_eq,
        ← coeffAt_eq, coeffAt_frame hI.frame (by simpa using hdz) (by rw [n_eq]; omega),
        coeffAt_frame hI.frame (by simpa using hdr) (by rw [n_eq]; omega)]
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.r10]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · exact k3.keep (rs := []) (by simp) fun r _ l _ => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm4 l) e =
          uhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by rw [← State.proj_xmm, B3 l hl e he, hv l hl e he]
      split
      · rename_i h4
        have := hc 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this
        exact this
      · rename_i h4
        have := hc 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this
        exact this
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

/-- The constants and the loop: `UseHint` of each coefficient at `out`. -/
theorem loop_ok {s : State} (hs0 : s.gpr .rdi = s₀.gpr .rdi) (hs1 : s.gpr .rsi = s₀.gpr .rsi)
    (hs10 : s.gpr .r10 = s₀.gpr .rcx) (hsrd : s.rd = s₀.rd) (hswr : s.wr = s₀.wr) (hsm : s.mem = s₀.mem) :
    WP isa (uhY g) s fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
      ∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
        uhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
  refine WP.seq (WP.mono (yC_ok g s) fun w ⟨yc, k1, m1, _, _⟩ => ?_)
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
    ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs0],
      by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs1],
      by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs10],
      by rw [o.keep.2.1, k1.2.1, hsrd], by rw [o.keep.2.2, k1.2.2, hswr],
      fun l hl => by simp only [State.lane]; rw [o.xmm, hy]; exact yc l hl,
      by rw [o.mem, m1, hsm]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, hsm, ifn (by omega)]⟩)
    fun i hi u hI => step hrd hwr hdz hdr hg hi hI) fun u hI => ⟨hI.frame, fun k hk => by
      rw [hI.coeff k hk, ifp (by omega)]⟩

end

end YUseL

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)

theorem useHintY_correct (s₀ : State) (hp : useHintK.pre s₀) :
    ∃ t s', Exec isa useHintAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ useHintK.post s₀ s' := by
  have hg : arg32 s₀ .rdx ∈ gamma2s := hp.2.2.2.2.2.2.2.1
  have hr : Reduced s₀.mem (s₀.gpr .rsi) := hp.2.2.2.2.2.2.2.2
  have wp : WP isa useHintAvx2 s₀ fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
      ∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
        uhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
    unfold useHintAvx2
    refine WP.seq (WP.mono (prologue_rdx_rcx s₀) fun s₁ ⟨⟨h10, hzf, hm⟩, hk⟩ => ?_)
    have go : ∀ g, arg32 s₀ .rdx = g → (g = g32 ∨ g = g88) → WP isa (uhY g) s₁ fun s' =>
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
          uhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) :=
      fun g hge hg' => by
        subst hge
        exact Arith.YUseL.loop_ok hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hg' (hk.gpr (by decide)) (hk.gpr (by decide)) h10
          hk.2.1 hk.2.2 hm
    have hite : WP isa (.ite .e (uhY g32) (uhY g88)) s₁ fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
        ∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
          uhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
      refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hzf) (fun h => ?_) (fun h => ?_)
      · rw [sub_beq_zero32, decide_eq_true_eq] at h
        exact go _ ((gamma_cases hg).1 h) (.inl rfl)
      · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
        exact go _ ((gamma_cases hg).2 h) (.inr rfl)
    refine WP.seq (WP.mono hite fun u ⟨hf, hc⟩ => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrund; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hf, hc⟩
  obtain ⟨t, s', he, ⟨hf, hv⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r10] wp (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.2.2.1
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hv k hk, zipWith_get _ _ _ hk, hintAt_get _ _ hk, useHint_eq hg, polyAt_val hr hk, Int.toNat_natCast]
    rw [uhL_toNat hg _ (hr k hk)]
    simp only [decide_eq_true_eq]

theorem useHintY_ct : ConstantTime isa useHintK.pre useHintK.pub useHintAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

theorem useHintY_verified : Verified X86_64.target useHintAvx2 (useHintContract X86_64.abi) :=
  Verified.of_correct useHintY_correct useHintY_ct (by
    round_implies [useHintContract, useHintSig, useHintK, hintK, X86_64.abi, X86_64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.X86_64.Round
