import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBlock
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits

/-!
# ML-DSA on x86-64: `vg_mldsa_high_bits_avx2` and `vg_mldsa_low_bits_avx2`

After the constants (`yC_ok`), each iteration of the loop loads eight
coefficients of `r`, does in each lane what `hbX` or `lbX` does to a register
(`YBlock.lean`), whose proof holds of each lane (`ylanes`), and stores the
eight results to `out` (`YMap.step`); the loop leaves `out` with all 256
(`YMap.loop_ok`), for the `γ₂` the function compared (`ybits_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Round (HbC bc_ofDwords)
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep ifp ifn ptr_step GOnly wp_rcxLoopY
  add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst)
open VG.Spec.MlDsa (q n coeffAt)

/-- Each doubleword of `v`. -/
def bc (v : BitVec 32) : BitVec 128 := ofDwords v v v v

/-- The constants of `hbX` and `lbX` in both lanes. -/
def YC (g : Nat) (s : State) : Prop :=
  ∀ l < 2, s.lane .xmm8 l = bc 127 ∧ s.lane .xmm9 l = bc (BitVec.ofNat 32 (dAdd g)) ∧
    s.lane .xmm10 l = bc (BitVec.ofNat 32 (dMod g)) ∧ s.lane .xmm15 l = qV

theorem YC.hbc {g : Nat} {s : State} (h : YC g s) {l : Nat} (hl : l < 2) : HbC g (s.proj l) :=
  ⟨by rw [State.proj_xmm, (h l hl).1]; exact bc_ofDwords _, by rw [State.proj_xmm, (h l hl).2.1]; exact bc_ofDwords _,
    by rw [State.proj_xmm, (h l hl).2.2.1]; exact bc_ofDwords _⟩

theorem YC.q {g : Nat} {s : State} (h : YC g s) {l : Nat} (hl : l < 2) : (s.proj l).xmm .xmm15 = qV := by
  rw [State.proj_xmm, (h l hl).2.2.2]

/-- The constants are kept by code that writes only `xmm0` to `xmm3`. -/
theorem YC.keep {g : Nat} {s s' : State} (h : YC g s) {rs : List XReg} (hr : ∀ r ∈ rs, r ∈ [.xmm0, .xmm1, .xmm2, .xmm3])
    (hl : ∀ r ∉ rs, ∀ l < 2, s'.lane r l = s.lane r l) : YC g s' := fun l hl' => by
  have n : ∀ r ∈ [XReg.xmm8, .xmm9, .xmm10, .xmm15], r ∉ rs := fun r hr' hr'' => by
    have := hr r hr''; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' this
    rcases hr' with rfl | rfl | rfl | rfl <;> rcases this with h | h | h | h <;> cases h
  rw [hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl']
  exact h l hl'

theorem yC_ok (g : Nat) (s : State) :
    WP isa (.block (yC g)) s fun s' => YC g s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      ∀ r ∉ [XReg.xmm8, .xmm9, .xmm10, .xmm15], ∀ l < 2, s'.lane r l = s.lane r l := by
  simp only [yC, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm8 _ s) fun s1 ⟨l1, k1, m1, x1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm9 _ s1) fun s2 ⟨l2, k2, m2, x2, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm10 _ s2) fun s3 ⟨l3, k3, m3, x3, o3⟩ => ?_
  refine WP.mono (yconst_ok .xmm15 _ s3) fun s4 ⟨l4, k4, m4, x4, o4⟩ =>
    ⟨fun l hl => ⟨?_, ?_, ?_, ?_⟩, (((k1.trans k2).trans k3).trans k4).mono (by simp), m4.trans (m3.trans (m2.trans m1)),
      x4.trans (x3.trans (x2.trans x1)), fun r hr l hl => ?_⟩
  · rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, o2 _ (by decide) l hl, l1 l hl]; rfl
  · rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, l2 l hl]; rfl
  · rw [o4 _ (by decide) l hl, l3 l hl]; rfl
  · rw [l4 l hl]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o4 r hr.2.2.2 l hl, o3 r hr.2.2.1 l hl, o2 r hr.2.1 l hl, o1 r hr.1 l hl]

namespace YMap

/-- After `i` vectors of eight, each coefficient of `out` before `8i` is `v k`. -/
structure Inv (s₀ : State) (g : Nat) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  r10 : s.gpr .r10 = s₀.gpr .rdx + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  yc : YC g s
  frame : Frame [pR (s₀.gpr .rdx)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdx) k = if k < 8 * i then v k else coeffAt s₀.mem (s₀.gpr .rdx) k

section
variable {s₀ : State} (hrd : s₀.rd = [pR (s₀.gpr .rdi)]) (hwr : s₀.wr = [pR (s₀.gpr .rdx)])
  (hdis : (pR (s₀.gpr .rdi)).Disjoint (pR (s₀.gpr .rdx)))
  {g : Nat} {x : List Instr} {d : XReg} {L : BitVec 32 → BitVec 32}
  (hX : ∀ t : State, HbC g t → t.xmm .xmm15 = qV →
    WP isa (.block x) t fun t' => (∀ e < 4, dword (t'.xmm d) e = L (dword (t.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3] t t')
  (hY : laneSseBlock (toY x) = some x)
include hrd hwr hdis hX hY

/-- An iteration, which stores `L` of the eight coefficients of `r` to `out`. -/
theorem step {i : Nat} (hi : i < 32) {s : State}
    (hI : Inv s₀ g (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k)) i s) :
    WP isa (.block (bitsBodyY x d ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ g (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rdx) ∈ s.wr := by rw [hI.wr, hwr]; simp
  have hr : pR (s₀.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have e2 : s.gpr .r10 = coeffAddr (s₀.gpr .rdx) (8 * i) := by
    rw [hI.r10]; congr 2; omega
  rw [bitsBodyY, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 hr j0)) fun s1 ⟨L1, o1⟩ => ?_
  have yc1 : YC g s1 := hI.yc.keep (by simp) o1.lane
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => ∀ e < 4, dword (t.xmm d) e = L (dword ((s1.proj l).xmm .xmm0) e))
    fun l hl => hX _ (yc1.hbc hl) (yc1.q hl)) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o1.trans o3
  have yc3 : YC g s3 := yc1.keep (by simp) o3.lane
  have g3 : s3.gpr .r10 = coeffAddr (s₀.gpr .rdx) (8 * i) := by rw [o13.gpr, e2]
  have g3' : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i) := by rw [o13.gpr, ← e1, add_ofNat_zero]
  have w0 : InRegions s3.wr (s3.gpr .r10) 32 := by
    rw [o13.wr, g3]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.r10]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · exact yc3.keep (rs := []) (by simp) fun r _ l _ => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane d l) e = L (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by
          rw [← State.proj_xmm, B3 l hl e he, State.proj_xmm, L1 l hl, e1, dword_readW _ _ he, lane_load,
            coeffAddr_add, ← coeffAt_eq, coeffAt_frame hI.frame (by simpa using hdis) (by rw [n_eq]; omega)]
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

/-- The constants and the loop. -/
theorem loop_ok {s : State} (hs0 : s.gpr .rdi = s₀.gpr .rdi) (hs10 : s.gpr .r10 = s₀.gpr .rdx)
    (hsrd : s.rd = s₀.rd) (hswr : s.wr = s₀.wr) (hsm : s.mem = s₀.mem) :
    WP isa (.seq (.block (yC g)) (VG.Impl.MlKem.X86_64.rcxLoop 32 (bitsBodyY x d))) s fun s' =>
      Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem ∧
        ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdx) k = L (coeffAt s₀.mem (s₀.gpr .rdi) k) := by
  refine WP.seq (WP.mono (yC_ok g s) fun w ⟨yc, k1, m1, _, _⟩ => ?_)
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
    ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs0],
      by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs10],
      by rw [o.keep.2.1, k1.2.1, hsrd], by rw [o.keep.2.2, k1.2.2, hswr],
      fun l hl => by
        simp only [State.lane]; rw [o.xmm, hy]; exact yc l hl,
      by rw [o.mem, m1, hsm]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, hsm, ifn (by omega)]⟩)
    fun i hi u hI => step hrd hwr hdis hX hY hi hI) fun u hI => ⟨hI.frame, fun k hk => by
      rw [hI.coeff k hk, ifp (by omega)]⟩

end

end YMap

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of XOnly)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Proof.MlDsa.X86_64.Arith (qV)

section
variable {post : State → State → Prop} {s₀ : State} (hp : (bitsK post).pre s₀)
include hp

/-- The prologue, the loop of the `γ₂` it compared, and the epilogue: `out` holds `L γ₂` of each
coefficient of `r`. -/
theorem ybits_ok {x : Nat → List Instr} {d : XReg} {L : Nat → BitVec 32 → BitVec 32}
    (hX : ∀ g, (g = g32 ∨ g = g88) → ∀ t : State, HbC g t → t.xmm .xmm15 = qV →
      WP isa (.block (x g)) t fun t' => (∀ e < 4, dword (t'.xmm d) e = L g (dword (t.xmm .xmm0) e)) ∧
        XOnly [.xmm0, .xmm1, .xmm2, .xmm3] t t')
    (hY : ∀ g, (g = g32 ∨ g = g88) → laneSseBlock (toY (x g)) = some (x g)) :
    WP isa (bitsY x d) s₀ fun s' =>
      (∀ k < 256, coeffAt s'.mem (s₀.gpr .rdx) k = L (arg32 s₀ .rsi) (coeffAt s₀.mem (s₀.gpr .rdi) k)) ∧
        Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem := by
  unfold bitsY
  refine WP.seq (WP.mono (prologue_rsi_rdx s₀) fun s₁ ⟨⟨h10, hz, hm⟩, hk⟩ => ?_)
  have h0 : s₁.gpr .rdi = s₀.gpr .rdi := hk.gpr (by decide)
  have go : ∀ g, arg32 s₀ .rsi = g → (g = g32 ∨ g = g88) →
      WP isa (.seq (.block (yC g)) (VG.Impl.MlKem.X86_64.rcxLoop 32 (bitsBodyY (x g) d))) s₁ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rdx) k = L (arg32 s₀ .rsi) (coeffAt s₀.mem (s₀.gpr .rdi) k)) ∧
          Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem := fun g hge hg =>
    WP.mono (Arith.YMap.loop_ok hp.1 hp.2.1 hp.2.2.1 (hX g hg) (hY g hg) h0 h10 hk.2.1 hk.2.2 hm)
      fun _ ⟨hf, hc⟩ => ⟨fun k hk => by rw [hc k hk, hge], hf⟩
  have hite : WP isa (.ite .e (.seq (.block (yC g32)) (VG.Impl.MlKem.X86_64.rcxLoop 32 (bitsBodyY (x g32) d)))
      (.seq (.block (yC g88)) (VG.Impl.MlKem.X86_64.rcxLoop 32 (bitsBodyY (x g88) d)))) s₁ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rdx) k = L (arg32 s₀ .rsi) (coeffAt s₀.mem (s₀.gpr .rdi) k)) ∧
          Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem := by
    refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hz) (fun h => ?_) (fun h => ?_)
    · rw [sub_beq_zero32, decide_eq_true_eq] at h
      exact go _ ((gamma_cases hp.2.2.2.2.2.1).1 h) (.inl rfl)
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
      exact go _ ((gamma_cases hp.2.2.2.2.2.1).2 h) (.inr rfl)
  refine WP.seq (WP.mono hite fun u ⟨hc, hf⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrund; rfl)
    fun u' hm' => ?_
  rw [hm']
  exact ⟨hc, hf⟩

end

theorem hbX_okG (g : Nat) (hg : g = g32 ∨ g = g88) (t : State) (hc : HbC g t) (_ : t.xmm .xmm15 = qV) :
    WP isa (.block (hbX g)) t fun t' => (∀ e < 4, dword (t'.xmm .xmm0) e = hbL g (dword (t.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3] t t' :=
  WP.mono (hbX_ok hg t hc) fun _ ⟨h1, h2⟩ => ⟨h1, h2.mono (by simp)⟩

theorem lane_hbX : ∀ g, (g = g32 ∨ g = g88) → laneSseBlock (toY (hbX g)) = some (hbX g) := by
  intro g hg; rcases hg with rfl | rfl <;> decide +kernel

theorem lane_lbX : ∀ g, (g = g32 ∨ g = g88) → laneSseBlock (toY (lbX g)) = some (lbX g) := by
  intro g hg; rcases hg with rfl | rfl <;> decide +kernel

theorem highBitsY_correct (s₀ : State) (hp : highBitsK.pre s₀) :
    ∃ t s', Exec isa highBitsAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ highBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rsi, .rdi, .r10]
    (ybits_ok hp (L := hbL) hbX_okG lane_hbX) (by decide +kernel)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, hbL_toNat hp.2.2.2.2.2.1 (hr k hk), highBits_eq hp.2.2.2.2.2.1, polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm

theorem lowBitsY_correct (s₀ : State) (hp : lowBitsK.pre s₀) :
    ∃ t s', Exec isa lowBitsAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ lowBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rsi, .rdi, .r10]
    (ybits_ok hp (L := lbL) (fun g hg t hc hq => lbX_ok hg t hc hq) lane_lbX) (by decide +kernel)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, lbL_toNat hp.2.2.2.2.2.1 (hr k hk), polyAt_get _ _ hk]

theorem highBitsY_ct : ConstantTime isa highBitsK.pre highBitsK.pub highBitsAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) bitsτ bits_agree (by taint_decide)

theorem lowBitsY_ct : ConstantTime isa lowBitsK.pre lowBitsK.pub lowBitsAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) bitsτ bits_agree (by taint_decide)

theorem highBitsY_verified : Verified X86_64.target highBitsAvx2 (highBitsContract X86_64.abi) :=
  Verified.of_correct highBitsY_correct highBitsY_ct (by
    round_implies [highBitsContract, bitsSig, highBitsK, bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using bitsSat)

theorem lowBitsY_verified : Verified X86_64.target lowBitsAvx2 (lowBitsContract X86_64.abi) :=
  Verified.of_correct lowBitsY_correct lowBitsY_ct (by
    round_implies [lowBitsContract, bitsSig, lowBitsK, bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using bitsSat)

end VG.Proof.MlDsa.X86_64.Round
