import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt_avx2` and `vg_mldsa_multiply_add_ntt_avx2`

As `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt` (`Mul.lean`) on
eight coefficients at a time: each iteration of the loop loads eight
coefficients of `f`, `g` and `h` and, in each lane, does what the SSE2 code's
`mulCore` (`mulAddCore`) does (`ylanes`), on the coefficients `8i + 4l` to `8i +
4l + 3` of lane `l`, and stores the eight results (`YMul.step`); the loop
stores the first 248 (`YMul.loop_ok`), and the last eight, from the
coefficients of `h` in `ymm6` (`YMul.last`), are stored after MXCSR is loaded
back (`YMul.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm xmm_setXmm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced)

theorem lane_mulCore : laneSseBlock (toY mulCore) = some mulCore := by decide +kernel
theorem lane_mulAddCore : laneSseBlock (toY mulAddCore) = some mulAddCore := by decide +kernel

/-- The constants, and `2⁶⁴ mod q` in both lanes of `ymm11`. -/
theorem ymulPro_ok (s : State) :
    WP isa (.block ymulPro) s fun s' => YConsts s' ∧ (∀ l < 2, s'.lane .xmm11 l = r2V) ∧
      (∀ l < 2, s'.lane .xmm6 l = s.lane .xmm6 l) ∧ Keep [.rax] s s' ∧ s'.mem = s.mem := by
  rw [ymulPro, WP.block_append_iff]
  refine WP.mono (yconsts_ok s) fun s1 ⟨c1, k1, m1, _, o1⟩ =>
    WP.mono (yconst_ok .xmm11 _ s1) fun s2 ⟨l2, k2, m2, _, o2⟩ =>
      ⟨fun l hl => ⟨?_, ?_⟩, fun l hl => by rw [l2 l hl]; decide,
        fun l hl => by rw [o2 _ (by decide) l hl, o1 _ (by decide) (by decide) l hl],
        (k1.trans k2).mono (by simp), m2.trans m1⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl]; exact (c1 l hl).q
  · rw [State.proj_xmm, o2 _ (by decide) l hl]; exact (c1 l hl).qinv

namespace YMul

/-- After `i` iterations: the first `8i` coefficients of `h` are `R`'s, the
others as they were in `s₀`. -/
structure Inv (h f g : Addr) (s₀ : State) (R : Poly) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = h + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = f + BitVec.ofNat 64 (32 * i)
  rdx : s.gpr .rdx = g + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : YConsts s
  r2 : ∀ l < 2, s.lane .xmm11 l = r2V
  x6 : ∀ l < 2, s.lane .xmm6 l = s₀.lane .xmm6 l
  frame : Frame [pR h] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem h k).toNat = (R[k]!).val
  rest : ∀ k < 256, 8 * i ≤ k → coeffAt s.mem h k = coeffAt s₀.mem h k

section
variable {h f g : Addr} {s₀ : State} (hwh : pR h ∈ s₀.wr) (hrf : pR f ∈ s₀.rd ++ s₀.wr)
  (hrg : pR g ∈ s₀.rd ++ s₀.wr) (hdf : (pR h).Disjoint (pR f)) (hdg : (pR h).Disjoint (pR g))
  {F G : Poly} (hF : ∀ k < 256, (coeffAt s₀.mem f k).toNat = (F[k]!).val)
  (hG : ∀ k < 256, (coeffAt s₀.mem g k).toNat = (G[k]!).val)
  {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
  (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = r2V → WP isa (.block core) s fun s' =>
    s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
  (hY : laneSseBlock (toY core) = some core)
  {R : Poly} {H : Nat → BitVec 32} (hH : ∀ k < 248, coeffAt s₀.mem h k = H k)
  (hlane : ∀ i < 64, ∀ x y z : BitVec 128, (∀ e < 4, (dword x e).toNat = (F[4 * i + e]!).val) →
    (∀ e < 4, (dword y e).toNat = (G[4 * i + e]!).val) → (∀ e < 4, dword z e = H (4 * i + e)) →
    ∀ e < 4, (dword (Fv x y z) e).toNat = (R[4 * i + e]!).val)
include hwh hrf hrg hdf hdg hF hG hcore hY hH hlane

theorem step {i : Nat} (hi : i < 31) {s : State} (hI : Inv h f g s₀ R i s) :
    WP isa (.block (ymulLoads ++ toY core ++ ymulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv h f g s₀ R (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr f (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega
  have e2 : s.gpr .rdx + BitVec.ofNat 64 0 = coeffAddr g (8 * i) := by
    rw [add_ofNat_zero, hI.rdx]; congr 2; omega
  have e3 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr h (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  have mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  rw [show ymulLoads ++ toY core ++ ymulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
    [.vmovdquLoad .l256 .xmm3 (at_ .rsi 0)] ++ [.vmovdquLoad .l256 .xmm13 (at_ .rdx 0)] ++
      [.vmovdquLoad .l256 .xmm5 (at_ .rdi 0)] ++ (toY core ++ (ymulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr)))
    by simp [ymulLoads, List.append_assoc],
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1, hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains32 f j0⟩)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2, hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains32 g j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  refine WP.mono (yld_ok (by
    rw [o12.rd, o12.wr, o12.gpr, e3, hI.rd, hI.wr]; exact f_in32 (List.mem_append_right _ hwh) j0))
    fun s3 ⟨L3, o3⟩ => ?_
  have o13 := o12.trans o3
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t =>
      t.xmm .xmm3 = Fv ((s3.proj l).xmm .xmm3) ((s3.proj l).xmm .xmm13) ((s3.proj l).xmm .xmm5))
    fun l hl => hcore _ (yonly_yconsts o13 hI.c (by decide) (by decide) l hl)
      (by rw [State.proj_xmm, o13.lane _ (by decide) l hl]; exact hI.r2 l hl))
    fun s4 ⟨B4, o4⟩ => ?_
  have o14 := o13.trans o4
  have g4 : s4.gpr .rdi = coeffAddr h (8 * i) := by rw [o14.gpr, ← e3, add_ofNat_zero]
  have w0 : InRegions s4.wr (s4.gpr .rdi) 32 := by rw [o14.wr, g4, hI.wr]; exact f_in32 hwh j0
  -- the lanes of the result
  have hl : ∀ l < 2, ∀ e < 4, (dword (s4.lane .xmm3 l) e).toNat = (R[8 * i + 4 * l + e]!).val := by
    intro l hl e he
    rw [← State.proj_xmm, B4 l hl, State.proj_xmm, State.proj_xmm, State.proj_xmm,
      o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, L1 l hl,
      L2 l hl, L3 l hl, o1.gpr, o1.mem, o2.gpr, o2.mem, o1.gpr, o1.mem, e1, e2, e3,
      show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega]
    refine hlane (2 * i + l) (by omega) _ _ _ (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) e he
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mf _ (by omega), hF _ (by omega),
        show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega]
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mg _ (by omega), hG _ (by omega),
        show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega]
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hI.rest _ (by omega) (by omega),
        hH _ (by omega), show 8 * i + 4 * l + e = 4 * (2 * i + l) + e by omega]
  simp only [ymulTail]
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun l hl => ⟨?_, ?_⟩, fun l hl => ?_, fun l hl => ?_, ?_, fun k hk => ?_,
    fun k hk hk' => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o14.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o14.gpr, hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o14.gpr, hI.rdx]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o14.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o14.wr, hI.wr]
  · rw [State.proj_xmm]; simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    exact (yonly_yconsts o14 hI.c (by decide) (by decide) l hl).q
  · rw [State.proj_xmm]; simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    exact (yonly_yconsts o14 hI.c (by decide) (by decide) l hl).qinv
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o14.lane _ (by decide) l hl]; exact hI.r2 l hl
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o14.lane _ (by decide) l hl]; exact hI.x6 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g4, o14.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g4, o14.mem, coeffAt_write256 _ _ j0 _ (by omega)]
    split
    · rename_i hk'
      rw [State.ymm, extract_ymm _ _ (by omega)]
      split
      · rename_i h4
        have := hl 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this
        exact this
      · rename_i h4
        have := hl 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this
        exact this
    · exact hI.done k (by omega)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g4, o14.mem, coeffAt_write256 _ _ j0 _ hk, ifn (by omega)]
    exact hI.rest k hk (by omega)
  · exact ⟨by rw [o14.gpr], by rw [o14.gpr]⟩

theorem loop_ok (hdi : s₀.gpr .rdi = h) (hsi : s₀.gpr .rsi = f) (hdx : s₀.gpr .rdx = g) (hc : YConsts s₀)
    (h11 : ∀ l < 2, s₀.lane .xmm11 l = r2V) :
    WP isa (rcxLoop 31 (ymulLoads ++ toY core ++ ymulTail)) s₀ (Inv h f g s₀ R 31) :=
  wp_rcxLoopY (N := 31) (by decide) (by decide) _ (fun u o hy _ =>
    have lu : ∀ r l, u.lane r l = s₀.lane r l := fun r l => by simp only [State.lane]; rw [o.xmm, hy]
    ⟨by rw [o.keep.gpr (by decide), hdi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hsi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, add_ofNat_zero], o.keep.2.1, o.keep.2.2,
      fun l hl => ⟨by rw [State.proj_xmm, lu]; exact (hc l hl).q, by rw [State.proj_xmm, lu]; exact (hc l hl).qinv⟩,
      fun l hl => by rw [lu]; exact h11 l hl, fun l _ => lu _ l,
      by rw [o.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega), fun k _ _ => by rw [o.mem]⟩)
    fun i hi u hI => step hwh hrf hrg hdf hdg hF hG hcore hY hH hlane hi hI

omit hwh hH in
/-- The last eight coefficients, with those of `h` in `ymm6`. -/
theorem last {s : State} (hI : Inv h f g s₀ R 31 s)
    (hz : ∀ l < 2, ∀ e < 4, dword (s₀.lane .xmm6 l) e = H (248 + 4 * l + e)) :
    WP isa (.block (ymulLast core)) s fun s' =>
      (∀ l < 2, ∀ e < 4, (dword (s'.lane .xmm3 l) e).toNat = (R[248 + 4 * l + e]!).val) ∧ s'.gpr = s.gpr ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have j0 : 8 * 31 + 8 ≤ 256 := by decide
  have e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr f 248 := by rw [add_ofNat_zero, hI.rsi]
  have e2 : s.gpr .rdx + BitVec.ofNat 64 0 = coeffAddr g 248 := by rw [add_ofNat_zero, hI.rdx]
  have mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  have mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  have hY' : laneSseBlock ([.vop (.vmovdqa .l256 .xmm5 .xmm6)] ++ toY core) = some (xmov .xmm5 .xmm6 :: core) := by
    show (match laneSse _, laneSseBlock (toY core) with | some a, some b => some (a ++ b) | _, _ => none) = _
    rw [hY]; rfl
  rw [ymulLast, show ∀ a b c : Instr, ∀ l : List Instr, [a, b, c] ++ l = [a] ++ [b] ++ ([c] ++ l) from
    fun _ _ _ _ => rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1, hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains32 f j0⟩)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2, hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains32 g j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  refine WP.mono (ylanes hY' (rs := [.xmm5, .xmm12, .xmm3, .xmm2, .xmm4]) (P := fun l t =>
      t.xmm .xmm3 = Fv ((s2.proj l).xmm .xmm3) ((s2.proj l).xmm .xmm13) ((s2.proj l).xmm .xmm6))
    fun l hl => ?_) fun s3 ⟨B3, o3⟩ => ⟨fun l hl e he => ?_, (o12.trans o3).gpr, (o12.trans o3).mem,
      (o12.trans o3).rd, (o12.trans o3).wr⟩
  · have c2 := yonly_yconsts o12 hI.c (by decide) (by decide) l hl
    rw [show xmov .xmm5 .xmm6 :: core = [xmov .xmm5 .xmm6] ++ core from rfl, WP.block_append_iff]
    vrund [eval_movdqa]
    refine WP.mono (hcore _ (c2.setXmm (by decide) (by decide) _)
      (by rw [xmm_setXmm, ifn (by decide), State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.r2 l hl))
      fun t ⟨ht, ot⟩ => ⟨?_, ?_⟩
    · rw [ht, xmm_setXmm, xmm_setXmm, xmm_setXmm, ifn (by decide), ifn (by decide), ifp rfl]
    · refine (XOnly.trans (⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr => ?_⟩ :
        XOnly [.xmm5] (s2.proj l) ((s2.proj l).setXmm .xmm5 ((s2.proj l).xmm .xmm6))) ot).mono
        (rs' := [.xmm5, .xmm12, .xmm3, .xmm2, .xmm4]) (by simp)
      rw [xmm_setXmm, ifn (by simpa using hr)]
  · rw [← State.proj_xmm, B3 l hl, State.proj_xmm, State.proj_xmm, State.proj_xmm,
      o2.lane _ (by decide) l hl, L1 l hl, L2 l hl, o1.gpr, o1.mem, e1, e2,
      o12.lane _ (by decide) l hl, hI.x6 l hl, show 248 + 4 * l + e = 4 * (62 + l) + e by omega]
    refine hlane (62 + l) (by omega) _ _ _ (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) e he
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mf _ (by omega), hF _ (by omega),
        show 248 + 4 * l + e = 4 * (62 + l) + e by omega]
    · rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, mg _ (by omega), hG _ (by omega),
        show 248 + 4 * l + e = 4 * (62 + l) + e by omega]
    · rw [hz l hl e he, show 248 + 4 * l + e = 4 * (62 + l) + e by omega]

end


/-- The whole function, from its precondition, with a `core` whose lanes are
those of `t`. -/
theorem fn_ok {t : Poly → Poly → Poly → Poly} {hPre : Mem → Addr → Prop} {σ : State} (hp : (mulK t hPre).pre σ)
    {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = r2V → WP isa (.block core) s fun s' =>
      s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
    (hY : laneSseBlock (toY core) = some core)
    (hlane : ∀ i < 64, ∀ x y z : BitVec 128,
      (∀ e < 4, (dword x e).toNat = ((polyAt σ.mem (σ.gpr .rsi))[4 * i + e]!).val) →
      (∀ e < 4, (dword y e).toNat = ((polyAt σ.mem (σ.gpr .rdx))[4 * i + e]!).val) →
      (∀ e < 4, dword z e = coeffAt σ.mem (σ.gpr .rdi) (4 * i + e)) →
      ∀ e < 4, (dword (Fv x y z) e).toNat = ((t (polyAt σ.mem (σ.gpr .rdi)) (polyAt σ.mem (σ.gpr .rsi))
        (polyAt σ.mem (σ.gpr .rdx)))[4 * i + e]!).val)
    (hk : writesOnly [.rax, .rdi, .rsi, .rdx, .rcx]
      (.seq (.block ymulPro) (.seq (rcxLoop 31 (ymulLoads ++ toY core ++ ymulTail)) (.block (ymulLast core)))) =
        true) :
    WP isa (ymulFn core) σ fun s' => Keep [.r8, .rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] σ s' ∧
      Frame [pR (σ.gpr .rdi)] σ.mem s'.mem ∧ (mulK t hPre).post σ s' := by
  obtain ⟨hrd, hwr, hdf, hdg, -, -, -, -, redf, redg⟩ := hp
  generalize eh : σ.gpr .rdi = h at *
  generalize ef : σ.gpr .rsi = f at *
  generalize eg : σ.gpr .rdx = g at *
  let R := t (polyAt σ.mem h) (polyAt σ.mem f) (polyAt σ.mem g)
  have hwh : pR h ∈ σ.wr := by rw [hwr]; exact List.mem_singleton_self _
  simp only [ymulFn]
  rw [show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r8 = h ∧
      (∀ l < 2, s1.lane .xmm6 l = σ.mem.readW (coeffAddr h 248 + BitVec.ofNat 64 (16 * l)) 128) ∧
      Keep [.r8] σ s1 ∧ s1.mem = σ.mem) ?_ fun s1 ⟨h8, h6, k1, m1⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (Q := fun (s0 : State) => s0.gpr .r8 = h ∧ s0.gpr .rdi = h ∧ GOnly [.r8] σ s0 ∧
        s0.ymmHi = σ.ymmHi) (by vrund [eh, RegUpd.ymmHi_setReg]; gonlyd)
      fun s0 ⟨h80, hd0, o0, y0⟩ => ?_
    refine WP.mono (yld_ok (by
      rw [hd0, o0.keep.2.1, o0.keep.2.2]
      exact ⟨_, List.mem_append_right _ hwh, Offset.contains_base h (by omega) (by omega)⟩))
      fun s1 ⟨L1, o1⟩ => ⟨by rw [o1.gpr, h80], fun l hl => by rw [L1 l hl, hd0, o0.mem],
        ⟨fun r hr => by rw [o1.gpr, o0.keep.gpr hr], by rw [o1.rd, o0.keep.2.1], by rw [o1.wr, o0.keep.2.2]⟩,
        by rw [o1.mem, o0.mem]⟩
  have hw1 : pR h ∈ s1.wr := by rw [k1.2.2]; exact hwh
  refine WP.seq (WP.mono (withMxcsrH_ok (r := .r8) ⟨by decide, by decide⟩ [.rax, .rdi, .rsi, .rdx, .rcx]
    ⟨by decide, by decide⟩ h8 hw1 hk (Q := fun (s3 : State) => Keep [.rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] s1 s3 ∧
      s3.gpr .rdi = coeffAddr h 248 ∧ Frame [pR h] σ.mem s3.mem ∧
      (∀ k < 248, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
      ∀ l < 2, ∀ e < 4, (dword (s3.lane .xmm3 l) e).toNat = (R[248 + 4 * l + e]!).val)
    fun s2 k2 f2 x2 y2 => ?_) fun s4 ⟨s3, ⟨kk, hdi, fr, dn, ln⟩, f4, k4, x4, y4⟩ => ?_)
  · have fσ2 : Frame [mxH h] σ.mem s2.mem := by rw [← m1]; exact f2
    have l2 : ∀ r l, s2.lane r l = s1.lane r l := fun r l => by simp only [State.lane]; rw [x2, y2]
    refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx] (WP.seq (WP.mono (ymulPro_ok s2)
      fun w ⟨cw, xw, x6, kw, mw⟩ => ?_) (Q := fun (s3 : State) => s3.gpr .rdi = coeffAddr h 248 ∧
        Frame [pR h] σ.mem s3.mem ∧ (∀ k < 248, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
        ∀ l < 2, ∀ e < 4, (dword (s3.lane .xmm3 l) e).toNat = (R[248 + 4 * l + e]!).val)) hk)
      fun s3 ⟨q3, kk⟩ => ⟨k2.trans kk, q3⟩
    have gw : ∀ r, r ≠ .rax → r ≠ .r11 → r ≠ .r8 → w.gpr r = σ.gpr r := fun r h1 h2 h3 => by
      rw [kw.gpr (by simpa using h1), k2.gpr (by simp [h1, h2]), k1.gpr (by simpa using h3)]
    have rw' : w.rd = σ.rd ∧ w.wr = σ.wr :=
      ⟨kw.2.1.trans (k2.2.1.trans k1.2.1), kw.2.2.trans (k2.2.2.trans k1.2.2)⟩
    have fσw : Frame [mxH h] σ.mem w.mem := by rw [mw]; exact fσ2
    have fσw' : Frame [pR h] σ.mem w.mem :=
      Frame.sub fσw fun r hr => ⟨pR h, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact mxH_sub h⟩
    refine WP.seq (WP.mono (loop_ok (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.2]; exact hwh) (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore hY (fun k hk => Mul.coeffAt_mxH fσw (by omega)) hlane
      (by rw [gw _ (by decide) (by decide) (by decide), eh]) (by rw [gw _ (by decide) (by decide) (by decide), ef])
      (by rw [gw _ (by decide) (by decide) (by decide), eg]) cw xw) fun s hI => ?_)
    refine WP.mono (last (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore hY hlane hI (fun l hl e he => by
        rw [x6 l hl, l2, h6 l hl, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq]))
      fun s3 ⟨ln, g3, m3, _, _⟩ => ?_
    refine ⟨by rw [g3, hI.rdi], ?_, fun k hk => by rw [m3]; exact hI.done k (by omega), ln⟩
    rw [m3]
    exact Frame.trans fσw' hI.frame
  · have k14 := (k1.trans kk).trans k4
    have hdi4 : s4.gpr .rdi = coeffAddr h 248 := by rw [k4.gpr (by simp), hdi]
    have wh4 : InRegions s4.wr (s4.gpr .rdi) 32 := by
      rw [hdi4, k14.2.2]; exact f_in32 hwh (by omega)
    have l4 : ∀ r l, s4.lane r l = s3.lane r l := fun r l => by simp only [State.lane]; rw [x4, y4]
    simp only [yepi, List.singleton_append]
    vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
      State.setMem_ymm, wh4]
    have f4' : Frame [pR h] s3.mem s4.mem := Frame.sub f4 fun r hr => ⟨pR h, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact mxH_sub h⟩
    refine ⟨k14.mono (by simp), (fr.trans f4').writeW (List.mem_singleton_self _) _
      (by rw [hdi4]; exact pR_contains32 h (by omega)), ?_⟩
    dsimp only [mulK]
    rw [eh, ef, eg, show ∀ s : State, (VOp.vzeroupper.exec s).mem = s.mem from fun _ => rfl, State.setMem_mem]
    refine polyIs_of_toNat fun k hk => ?_
    rw [n_eq] at hk
    rw [hdi4, coeffAt_write256 _ _ (j := 248) (by decide) _ hk]
    split
    · rw [State.ymm, extract_ymm _ _ (by omega)]
      split
      · rename_i h1 h4
        have := ln 0 (by decide) (k - 248) h4
        rw [show 248 + 4 * 0 + (k - 248) = k by omega, ← l4] at this
        exact this
      · rename_i h1 h4
        have := ln 1 (by decide) (k - 248 - 4) (by omega)
        rw [show 248 + 4 * 1 + (k - 248 - 4) = k by omega, ← l4] at this
        exact this
    · rw [Mul.coeffAt_mxH f4 (by omega)]
      exact dn k (by omega)

end YMul

/-! ## The functions -/

theorem mulY_correct (s : State) (hs : mulK'.pre s) :
    ∃ t s', Exec isa mulAvx2 s t s' ∧ abiPreserved s s' ∧ mulK'.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := YMul.fn_ok hs (core := mulCore) (Fv := fun x y _ => mulV x y)
    (fun s hc h11 => mulCore_ok hc h11) lane_mulCore
    (fun i hi x y z hx hy _ e he => by
      rw [mul_get _ _ (by rw [n_eq]; omega)]
      exact mul_lane hx hy he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem mulAddY_correct (s : State) (hs : mulAddK.pre s) :
    ∃ t s', Exec isa mulAddAvx2 s t s' ∧ abiPreserved s s' ∧ mulAddK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := YMul.fn_ok hs (core := mulAddCore) (Fv := mulAddV)
    (fun s hc h11 => mulAddCore_ok hc h11) lane_mulAddCore
    (fun i hi x y z hx hy hz e he => by
      rw [add_get _ _ (by rw [n_eq]; omega), mul_get _ _ (by rw [n_eq]; omega)]
      exact mulAdd_lane hx hy (c := fun e => (polyAt s.mem (s.gpr .rdi))[4 * i + e]!)
        (fun e he => by rw [hz e he, polyAt_val hs.2.2.2.2.2.2.2.1 (by rw [n_eq]; omega)]) he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem mulY_ct : ConstantTime isa mulK'.pre mulK'.pub mulAvx2 :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem mulAddY_ct : ConstantTime isa mulAddK.pre mulAddK.pub mulAddAvx2 :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem mulY_verified : Verified X86_64.target mulAvx2 (Spec.MlDsa.mulContract X86_64.abi) :=
  Verified.of_correct mulY_correct mulY_ct (by
    mldsa_implies [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

theorem mulAddY_verified : Verified X86_64.target mulAddAvx2 (Spec.MlDsa.mulAddContract X86_64.abi) :=
  Verified.of_correct mulAddY_correct mulAddY_ct (by
    mldsa_implies [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlDsa.X86_64.Arith
