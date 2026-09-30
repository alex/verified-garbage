import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call

/-!
# ML-DSA key generation on x86-64: masking a sampled polynomial

Untrusted: everything here is checked by Lean. After each sampler, `mask a`
ANDs its result (0 or 1, in `eax`) into `r15`, and each coefficient of the
polynomial at `a` with `-eax`: the polynomial is kept if the sampler
succeeded, and zeroed if it failed (`mask_ok`), without a branch
(`mask_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc lea at_)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params coeffAt)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-! ## One coefficient -/

abbrev maskBody : List Instr := [.mov32 .rax (.mem (at_ .rdi 0)), .alu32 .and .rax (.reg .r8),
  .store32 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (h1 : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block maskBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rdi) 32 &&& (s.gpr .r8).setWidth 32) ∧
        s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1]

/-! ## The polynomial -/

/-- The coefficients after masking with the 32 bits `r`, 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) :
    x &&& (BitVec.setWidth 64 (0 - r)).setWidth 32 = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [ifp rfl, show (BitVec.setWidth 64 (0 - (1 : BitVec 32))).setWidth 32 = BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

abbrev maskPre (a : Ptr) : List Instr :=
  [.alu32 .and .r15 (.reg .rax), .mov32 .r8 (.imm 0), .alu32 .sub .r8 (.reg .rax)] ++ lea .rdi a ++ imm .rcx 256

theorem maskPre_ok {a : Ptr} (ha : PtrOk a) (h15 : a.1 ≠ .r15) (s : State) :
    WP isa (.block (maskPre a)) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
        s'.gpr .r8 = BitVec.setWidth 64 (0 - (s.gpr .rax).setWidth 32) ∧ s'.gpr .rdi = pa s a ∧
        s'.gpr .rcx = BitVec.ofNat 64 256) ∧ Keep [.r15, .r8, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold maskPre lea imm
  xrun [sx_ofNat ha.off, imm_eq (show 256 < 2 ^ 32 by decide), h15, ha.ne (r := .r8) (by decide),
    ha.ne (r := .rdi) (by decide), List.cons_append, List.nil_append]

theorem mask_ok {p : Params} {s : State} (L : Lay kgR (kgW p) s) {a : Ptr} (ha : PtrOk a) (ha15 : a.1 ≠ .r15)
    (w : inB (kgW p) a 1024 = true) (hr : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1) :
    WP isa (mask a) s fun s' => PostB s s' [⟨pa s a, 1024⟩] ∧ MX s' = MX s ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i =
        if (s.gpr .rax).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  have hW : InRegions s.wr (pa s a) 1024 := L.cW w _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hn : (pa s a).toNat + 1024 ≤ 2 ^ 64 := L.nwp (inB_mono w)
  refine WP.mono (WP.mx (c := mask a) (noLd_spec (by rfl)) (Q := fun s' => PostB s s' [⟨pa s a, 1024⟩] ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i =
        if (s.gpr .rax).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0) ?_)
    fun s' ⟨⟨hP, h15, hc⟩, hx⟩ => ⟨hP, hx, h15, hc⟩
  unfold mask
  refine WP.seq (WP.mono (maskPre_ok ha ha15 s) fun s1 ⟨⟨hm1, h15, h8, hdi, hcx⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := 256) (by decide) (by decide) (fun i s' =>
      s'.gpr .rdi = pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .r8 = s1.gpr .r8 ∧ s'.gpr .r15 = s1.gpr .r15 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨pa s a, 1024⟩] s.mem s'.mem ∧
      (∀ j < 256, coeffAt s'.mem (pa s a) j =
        if j < i then coeffAt s.mem (pa s a) j &&& (s1.gpr .r8).setWidth 32 else coeffAt s.mem (pa s a) j) ∧
      Keep [.r15, .r8, .rdi, .rcx, .rax] s s')
    (fun i hi s' ⟨hdi', h8', h15', hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hdi, add_ofNat_zero], rfl, rfl, k1.2.1, k1.2.2, by rw [hm1]; exact Frame.refl _ _,
      fun j _ => by rw [ifn (Nat.not_lt_zero j), hm1], k1.mono (by decide)⟩ hcx)
    fun s' ⟨_, h8', h15', hrd', hwr', hf, hc, kk⟩ => ⟨⟨hrd', hwr', fun r hr => kk.gpr ?_, kk.gpr (by decide),
      hf.mono fun _ hr => List.mem_append_left _ hr⟩, ?_, ?_⟩
  · have hc4 : (⟨pa s a, 1024⟩ : Region).Contains (pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      contains_offset' (by omega) (by omega)
    have hin : InRegions s'.wr (s'.gpr .rdi) 4 := by
      rw [hwr', hdi']; exact inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .rdi) 4 :=
      let ⟨r, hr, hc⟩ := hin; ⟨r, List.mem_append_right _ hr, hc⟩
    refine WP.mono (maskBody_ok s' hin0 hin)
      fun s'' ⟨⟨hm, hdi'', hcx'', hz⟩, k'⟩ => ⟨⟨?_, by rw [k'.gpr (by decide), h8'],
        by rw [k'.gpr (by decide), h15'], k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_,
        (kk.trans k').mono (by decide)⟩, hcx'', hz⟩
    · rw [hdi'', hdi', show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, off_add]; rfl
    · rw [hm, hdi']; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, hdi', coeffAt_writeW32 _ _ hj (by omega), h8']
      by_cases e : i = j
      · subst e
        rw [ifp rfl, ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [ifn e, hc j hj]
        by_cases hji : j < i
        · rw [ifp hji, ifp (by omega)]
        · rw [ifn hji, ifn (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, bases] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [h15', h15]
  · intro j hj
    rw [hc j hj, ifp hj, h8, and_mask hr]
/-! ## Constant time -/

/-- The check is the same for every offset: its hint is computed once, for offset 0. -/
theorem mask_taint : ∀ j < 128, (taint.check (X86_64.Taint.ofRegs [.rbx]) (mask (sc (oP j)))
    (VG.Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (mask (sc 0)))).isSome = true := by decide +kernel

theorem mask_tr {j : Nat} (hj : j < 128) {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (mask (sc (oP j))) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (mask_taint j hj)

end VG.Proof.MlDsa.X86_64.KeyGen
