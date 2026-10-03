import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub

/-!
# ML-DSA on x86-64: `vg_mldsa_add_avx2` and `vg_mldsa_sub_avx2`

Each iteration of the loop loads eight coefficients of `f` and of `g` and, in
each lane, does what an iteration of `vg_mldsa_add` (`vg_mldsa_sub`) does
(`AddSub.lean`), whose proof holds of each lane (`ylanes`), and stores the
eight results to `f` (`YAddSub.step`); the loop leaves `f` with all 256
(`YAddSub.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

theorem addFixX_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = addV (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s' := by
  simp only [vcsub, vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, by xonly⟩

theorem subFixX_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = subV (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s' := by
  simp only [vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, by xonly⟩

theorem lane_addFix : laneSseBlock (toY (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) =
    some (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) := by decide +kernel

theorem lane_subFix : laneSseBlock (toY (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) =
    some (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2) := by decide +kernel

namespace YAddSub

/-- After `i` vectors of eight, each coefficient before `8i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qV
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 8 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
  {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
  {L : BitVec 32 → BitVec 32 → BitVec 32}
  (hF : ∀ (s : State), s.xmm .xmm15 = qV →
    WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
      s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s')
  (hY : laneSseBlock (toY (xb op .xmm0 .xmm1 :: fix)) = some (xb op .xmm0 .xmm1 :: fix))
  (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
include hp hF hY hL

/-- An iteration, which stores `F` of the vectors of `f` and `g` in each lane. -/
theorem step {i : Nat} (hi : i < 32) {s : State}
    (hI : Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (yaccBody op fix ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have e2 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega
  rw [yaccBody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 (List.mem_append_right _ hw) j0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact ⟨_, hr, pR_contains32 _ j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  refine WP.mono (ylanes hY (P := fun l t => t.xmm .xmm0 = F ((s2.proj l).xmm .xmm0) ((s2.proj l).xmm .xmm1))
    fun l hl => hF _ (by rw [State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have g3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i) := by rw [o13.gpr, ← e1, add_ofNat_zero]
  have g3' : s3.gpr .rsi = coeffAddr (s₀.gpr .rsi) (8 * i) := by rw [o13.gpr, ← e2, add_ofNat_zero]
  have w0 : InRegions s3.wr (s3.gpr .rdi) 32 := by rw [o13.wr, g3]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e =
          L (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by
          rw [← State.proj_xmm, B3 l hl, hL _ _ _ he, State.proj_xmm, State.proj_xmm,
            o2.lane _ (by decide) l hl, L1 l hl, L2 l hl, o1.gpr, o1.mem, e1, e2, dword_readW _ _ he,
            dword_readW _ _ he, lane_load, lane_load, coeffAddr_add, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq,
            hI.coeff _ (by omega), ifn (by omega),
            coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) (by rw [n_eq]; omega)]
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

/-- The whole function, from its precondition. -/
theorem fn_ok (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx] (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi)) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block (yconst .xmm15 8380417))
        (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hW : WP isa (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) s₀ fun s' =>
      Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdi) k =
        L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
    refine WP.seq (WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, _⟩ => ?_)
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy], lq l hl]; decide,
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega)]⟩)
      fun i hi u hI => step hp hF hY hL hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by simp only [yepi]; vrund; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, fun k hk => by rw [hI.coeff k hk, ifp (by omega)]⟩
  obtain ⟨tr, s', he, ⟨hf, hco⟩, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hf ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    rw [hco k hk]
    exact hv k hk

end

end YAddSub

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (n)

theorem addY_correct (s : State) (hs : (accK Spec.MlDsa.add).pre s) :
    ∃ t s', Exec isa addAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.add).post s s' :=
  YAddSub.fn_ok hs (op := .paddd) (fix := vcsub .xmm0 .xmm2) (L := fun a b => csubL (a + b)) addFixX_ok
    lane_addFix (fun x y e he => dword_addV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [add_get _ _ hk', addD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_add])
    (by decide +kernel) (by decide +kernel)

theorem subY_correct (s : State) (hs : (accK Spec.MlDsa.sub).pre s) :
    ∃ t s', Exec isa subAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.sub).post s s' :=
  YAddSub.fn_ok hs (op := .psubd) (fix := vcadd .xmm0 .xmm2) (L := fun a b => caddL (a - b)) subFixX_ok
    lane_subFix (fun x y e he => dword_subV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [sub_get _ _ hk', subD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_sub])
    (by decide +kernel) (by decide +kernel)

theorem addY_ct : ConstantTime isa (accK Spec.MlDsa.add).pre (accK Spec.MlDsa.add).pub addAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem subY_ct : ConstantTime isa (accK Spec.MlDsa.sub).pre (accK Spec.MlDsa.sub).pub subAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem addY_verified : Verified X86_64.target addAvx2 (Spec.MlDsa.addContract X86_64.abi) :=
  Verified.of_correct addY_correct addY_ct (by
    mldsa_implies [Spec.MlDsa.addContract, Spec.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

theorem subY_verified : Verified X86_64.target subAvx2 (Spec.MlDsa.subContract X86_64.abi) :=
  Verified.of_correct subY_correct subY_ct (by
    mldsa_implies [Spec.MlDsa.subContract, Spec.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlDsa.X86_64.Arith
