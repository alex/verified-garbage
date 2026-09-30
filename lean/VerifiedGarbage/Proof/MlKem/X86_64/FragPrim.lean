import VerifiedGarbage.Proof.MlKem.X86_64.FragCall

/-!
# ML-KEM-768 on x86-64: the calls of the polynomial primitives

Untrusted: everything here is checked by Lean. For each call of a
polynomial primitive from a top-level function: what it needs of the state
(`…H`), what it does (`…_ok`), and that two runs that agree on its public
data leak the same (`…_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(execBlock_nomem h e₁).trans (execBlock_nomem h e₂).symm, trivial⟩

theorem lea_nomem (d : Reg) (p : Ptr) : ∀ i ∈ lea d p, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem nomem_append {a b : List Instr} (ha : ∀ i ∈ a, ∀ s, isa.addrs i s = [])
    (hb : ∀ i ∈ b, ∀ s, isa.addrs i s = []) : ∀ i ∈ a ++ b, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h s, hb i h s]

theorem mov32i_nomem (d : Reg) (v : BitVec 32) : ∀ i ∈ ([.mov32 d (.imm v)] : List Instr), ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [List.mem_singleton] at hi
  subst hi; rfl

theorem covers_nil_wr {rs : List Region} {s : State} (h : Covers rs s.wr) : Covers ([] ++ rs) (s.rd ++ s.wr) :=
  fun a n hi => by
    rw [List.nil_append] at hi
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## The callees' stack -/

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem ntt_nosp : NoSp Impl.MlKem.X86_64.ntt := nosp_of (by decide +kernel)
theorem nttInv_nosp : NoSp Impl.MlKem.X86_64.nttInv := nosp_of (by decide +kernel)
theorem mul_nosp : NoSp multiplyNTTs := nosp_of (by decide +kernel)
theorem add_nosp : NoSp Impl.MlKem.X86_64.add := nosp_of (by decide +kernel)
theorem sub_nosp : NoSp Impl.MlKem.X86_64.sub := nosp_of (by decide +kernel)
theorem cbd2_nosp : NoSp cbd2 := nosp_of (by decide +kernel)
theorem encode12_nosp : NoSp encode12 := nosp_of (by decide +kernel)
theorem decode12_nosp : NoSp decode12 := nosp_of (by decide +kernel)
theorem ce_nosp : NoSp compressEncode := nosp_of (by decide +kernel)
theorem dd_nosp : NoSp decodeDecompress := nosp_of (by decide +kernel)
theorem sample_nosp : NoSp sampleNTT := nosp_of (by decide +kernel)

theorem ntt_depth : Impl.MlKem.X86_64.ntt.depth = 0 := by decide +kernel
theorem nttInv_depth : Impl.MlKem.X86_64.nttInv.depth = 0 := by decide +kernel
theorem mul_depth : multiplyNTTs.depth = 0 := by decide +kernel
theorem add_depth : Impl.MlKem.X86_64.add.depth = 0 := by decide +kernel
theorem sub_depth : Impl.MlKem.X86_64.sub.depth = 0 := by decide +kernel
theorem cbd2_depth : cbd2.depth = 0 := by decide +kernel
theorem encode12_depth : encode12.depth = 0 := by decide +kernel
theorem decode12_depth : decode12.depth = 0 := by decide +kernel
theorem ce_depth : compressEncode.depth = 0 := by decide +kernel
theorem dd_depth : decodeDecompress.depth = 0 := by decide +kernel
theorem sample_depth : sampleNTT.depth = 2 := by decide +kernel

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of `vg_mlkem_ntt` or `vg_mlkem_inv_ntt` on `f` needs. -/
structure IpH (f : Ptr) (s : State) : Prop where
  off : f.2 < 2 ^ 31
  red : Reduced s.mem (pa s f)
  d : (pR (pa s f)).Disjoint (pR (pa s (sc oSS)))
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  kZ : (below (s.gpr .rsp) 32).Disjoint (pR (pa s (sc oSS)))
  w : Covers [pR (pa s f), pR (pa s (sc oSS))] s.wr

theorem ipGlue_ok (f : Ptr) (hf : f.2 < 2 ^ 31) (s : State) :
    WP isa (.block (lea .rdi f ++ lea .rsi (sc oSS))) s fun s1 =>
      ((s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = pa s (sc oSS)) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat hf, sx_ofNat (show oSS < 2 ^ 31 by decide), List.cons_append, List.nil_append]

theorem ipPre {t : Poly → Poly} {f : Ptr} {s s1 : State} (h : IpH f s) (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = pa s (sc oSS))
    (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    (inPlaceK t).pre (s1.callEntry.withRegions [] [pR (pa s f), pR (pa s (sc oSS))]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [inPlaceK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  refine ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kZ), ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.red

/-- A call of an in-place transformation `t` (`NTT` or `NTT⁻¹`). -/
theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (inPlaceK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (inPlaceK t).post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) {f : Ptr} {s : State} (h : IpH f s) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call n c)) s fun s' =>
      Post s s' [pR (pa s f), pR (pa s (sc oSS))] ∧ PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  refine WP.mono (glueCall_ok hv hsp (Nat.le_succ_of_le hd) (ipGlue_ok f h.off s) (fun s1 hv hm k => ipPre h hv hm k)
    (covers_nil_wr h.w) h.w) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [inPlaceK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    hV.1, hm₂, ce_polyAt s1 (by rw [hsp]; exact h.kF), hm] at hq
  exact hq


theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (inPlaceK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (inPlaceK t).post s s')
    (hct : ConstantTime isa (inPlaceK t).pre (inPlaceK t).pub c) {f : Ptr} :
    RelCT isa (fun x y => IpH f x ∧ IpH f y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp) (.seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call n c)) fun _ _ => True :=
  glueCall_tr hv hct (V := fun x x1 => ((x1.gpr .rdi = pa x f ∧ x1.gpr .rsi = pa x (sc oSS)) ∧ x1.mem = x.mem) ∧
      Keep argRegs x x1)
    (block_nomem_tr (nomem_append (lea_nomem _ _) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨ipGlue_ok f hx.off x, ipGlue_ok f hy.off y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨[], _, [], _, ipPre hx hv1 hm1 k1, ipPre hy hv2 hm2 k2, ?_, covers_nil_wr (by rw [k1.2.2]; exact hx.w),
        by rw [k1.2.2]; exact hx.w, covers_nil_wr (by rw [k2.2.2]; exact hy.w), by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [inPlaceK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

/-! ## Addition and subtraction -/

/-- What a call of `vg_mlkem_add` or `vg_mlkem_sub` on `f`, `g` needs. -/
structure AccH (f g : Ptr) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31
  redF : Reduced s.mem (pa s f)
  redG : Reduced s.mem (pa s g)
  d : (pR (pa s f)).Disjoint (pR (pa s g))
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  kG : (below (s.gpr .rsp) 32).Disjoint (pR (pa s g))
  c : Covers ([pR (pa s g)] ++ [pR (pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (pa s f)] s.wr

theorem accGlue_ok (f g : Ptr) (hf : f.2 < 2 ^ 31) (hg : g.2 < 2 ^ 31) (hgr : g.1 ≠ .rdi) (s : State) :
    WP isa (.block (lea .rdi f ++ lea .rsi g)) s fun s1 =>
      ((s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = pa s g) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat hf, sx_ofNat hg, hgr, List.cons_append, List.nil_append]

theorem accPre {t : Poly → Poly → Poly} {f g : Ptr} {s s1 : State} (h : AccH f g s)
    (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = pa s g) (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    (accK t).pre (s1.callEntry.withRegions [pR (pa s g)] [pR (pa s f)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [accK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  refine ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kG),
    ?_, ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.redF
  · rw [ce_reduced s1 (by rw [hsp]; exact h.kG), hm]; exact h.redG

theorem accAt_ok {t : Poly → Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (accK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accK t).post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) {f g : Ptr} (hgr : g.1 ≠ .rdi) {s : State} (h : AccH f g s) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi g)) (.call n c)) s fun s' =>
      Post s s' [pR (pa s f)] ∧ PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (glueCall_ok hv hsp (Nat.le_succ_of_le hd) (accGlue_ok f g h.off.1 h.off.2 hgr s) (fun s1 hv hm k => accPre h hv hm k)
    h.c h.w) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [accK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂, ce_polyAt s1 (by rw [hsp]; exact h.kF),
    ce_polyAt s1 (by rw [hsp]; exact h.kG), hm] at hq
  exact hq

theorem accAt_tr {t : Poly → Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (accK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accK t).post s s')
    (hct : ConstantTime isa (accK t).pre (accK t).pub c) {f g : Ptr} (hgr : g.1 ≠ .rdi) :
    RelCT isa (fun x y => AccH f g x ∧ AccH f g y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr g.1 = y.gpr g.1 ∧
      x.gpr .rsp = y.gpr .rsp) (.seq (.block (lea .rdi f ++ lea .rsi g)) (.call n c)) fun _ _ => True :=
  glueCall_tr hv hct (V := fun x x1 => ((x1.gpr .rdi = pa x f ∧ x1.gpr .rsi = pa x g) ∧ x1.mem = x.mem) ∧
      Keep argRegs x x1)
    (block_nomem_tr (nomem_append (lea_nomem _ _) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨accGlue_ok f g hx.off.1 hx.off.2 hgr x, accGlue_ok f g hy.off.1 hy.off.2 hgr y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, accPre hx hv1 hm1 k1, accPre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [accK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]


/-! ## `MultiplyNTTs` -/

/-- What a call of `vg_mlkem_multiply_ntts` writing `h` from `f`, `g` needs. -/
structure MulH (h f g : Ptr) (s : State) : Prop where
  off : h.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31
  redF : Reduced s.mem (pa s f)
  redG : Reduced s.mem (pa s g)
  hf : (pR (pa s h)).Disjoint (pR (pa s f))
  hg : (pR (pa s h)).Disjoint (pR (pa s g))
  hz : (pR (pa s h)).Disjoint (pR (pa s (sc oSS)))
  fz : (pR (pa s f)).Disjoint (pR (pa s (sc oSS)))
  gz : (pR (pa s g)).Disjoint (pR (pa s (sc oSS)))
  kH : (below (s.gpr .rsp) 32).Disjoint (pR (pa s h))
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  kG : (below (s.gpr .rsp) 32).Disjoint (pR (pa s g))
  kZ : (below (s.gpr .rsp) 32).Disjoint (pR (pa s (sc oSS)))
  c : Covers ([pR (pa s f), pR (pa s g)] ++ [pR (pa s h), pR (pa s (sc oSS))]) (s.rd ++ s.wr)
  w : Covers [pR (pa s h), pR (pa s (sc oSS))] s.wr

/-- The bases of the arguments are not argument registers. -/
abbrev NA (p : Ptr) : Prop := p.1 ∉ argRegs

theorem mulGlue_ok (h f g : Ptr) (ho : h.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31) (hf : NA f) (hg : NA g)
    (s : State) :
    WP isa (.block (lea .rdi h ++ lea .rsi f ++ lea .rdx g ++ lea .rcx (sc oSS))) s fun s1 =>
      ((s1.gpr .rdi = pa s h ∧ s1.gpr .rsi = pa s f ∧ s1.gpr .rdx = pa s g ∧ s1.gpr .rcx = pa s (sc oSS)) ∧
        s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  have f1 : f.1 ≠ .rdi := fun e => hf (by rw [e]; decide)
  have g1 : g.1 ≠ .rdi := fun e => hg (by rw [e]; decide)
  have g2 : g.1 ≠ .rsi := fun e => hg (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2, sx_ofNat (show oSS < 2 ^ 31 by decide), f1, g1, g2,
    List.cons_append, List.nil_append]

theorem mulPre {h f g : Ptr} {s s1 : State} (H : MulH h f g s)
    (hv : s1.gpr .rdi = pa s h ∧ s1.gpr .rsi = pa s f ∧ s1.gpr .rdx = pa s g ∧ s1.gpr .rcx = pa s (sc oSS))
    (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    mulK.pre (s1.callEntry.withRegions [pR (pa s f), pR (pa s g)] [pR (pa s h), pR (pa s (sc oSS))]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  refine ⟨trivial, trivial, H.hf, H.hg, H.hz, H.fz, H.gz, ret_disj s1 (by rw [hsp]; exact H.kH),
    ret_disj s1 (by rw [hsp]; exact H.kF), ret_disj s1 (by rw [hsp]; exact H.kG),
    ret_disj s1 (by rw [hsp]; exact H.kZ), ?_, ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kF), hm]; exact H.redF
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kG), hm]; exact H.redG

theorem mulAt_ok {h f g : Ptr} (hf : NA f) (hg : NA g) {s : State} (H : MulH h f g s) :
    WP isa (mulAt h f g) s fun s' => Post s s' [pR (pa s h), pR (pa s (sc oSS))] ∧
      PolyIs s'.mem (pa s h) (multiplyNTTs (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (glueCall_ok mul_correct mul_nosp (by rw [mul_depth]; decide) (mulGlue_ok h f g H.off hf hg s)
    (fun s1 hv hm k => mulPre H hv hm k) H.c H.w) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [mulK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hm₂,
    ce_polyAt s1 (by rw [hsp]; exact H.kF), ce_polyAt s1 (by rw [hsp]; exact H.kG), hm] at hq
  exact hq

theorem mulAt_tr {h f g : Ptr} (hf : NA f) (hg : NA g) :
    RelCT isa (fun x y => MulH h f g x ∧ MulH h f g y ∧ x.gpr h.1 = y.gpr h.1 ∧ x.gpr f.1 = y.gpr f.1 ∧
      x.gpr g.1 = y.gpr g.1 ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp) (mulAt h f g) fun _ _ => True :=
  glueCall_tr mul_correct mul_ct (V := fun x x1 => ((x1.gpr .rdi = pa x h ∧ x1.gpr .rsi = pa x f ∧
      x1.gpr .rdx = pa x g ∧ x1.gpr .rcx = pa x (sc oSS)) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
      (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨mulGlue_ok h f g hx.off hf hg x, mulGlue_ok h f g hy.off hf hg y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3, e4, e5⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, mulPre hx hv1 hm1 k1, mulPre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e5]⟩
      simp only [mulK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1,
        hv2.2.2.2, pa, e1, e2, e3, e4, k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e5, and_self]


/-! ## Two-pointer calls: `SamplePolyCBD₂`, `ByteEncode₁₂`, `ByteDecode₁₂` -/

/-- What a call reading `n` bytes (or a polynomial) at `p` and writing `m` bytes (or a polynomial) at `q` needs. -/
structure TwoH (p q : Ptr) (n m : Nat) (s : State) : Prop where
  off : p.2 < 2 ^ 31 ∧ q.2 < 2 ^ 31
  d : Region.Disjoint ⟨pa s p, n⟩ ⟨pa s q, m⟩
  kP : (below (s.gpr .rsp) 32).Disjoint ⟨pa s p, n⟩
  kQ : (below (s.gpr .rsp) 32).Disjoint ⟨pa s q, m⟩
  c : Covers ([⟨pa s p, n⟩] ++ [⟨pa s q, m⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s q, m⟩] s.wr

theorem cbdPre {p q : Ptr} {s s1 : State} (h : TwoH p q 128 1024 s) (hv : s1.gpr .rdi = pa s p ∧ s1.gpr .rsi = pa s q)
    (k : Keep argRegs s s1) : cbd2K.pre (s1.callEntry.withRegions [⟨pa s p, 128⟩] [pR (pa s q)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [cbd2K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  exact ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ)⟩

theorem cbd2At_ok {p q : Ptr} (hq : NA q) {s : State} (h : TwoH p q 128 1024 s) :
    WP isa (cbd2At p q) s fun s' => Post s s' [pR (pa s q)] ∧
      PolyIs s'.mem (pa s q) (samplePolyCBD 2 (bytesAt s.mem (pa s p) 128)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok cbd2_correct cbd2_nosp (by rw [cbd2_depth]; decide)
    (accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv _ k => cbdPre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [cbd2K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂,
    ce_bytesAt s1 (n := 128) (by decide) (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem cbd2At_tr {p q : Ptr} (hq : NA q) :
    RelCT isa (fun x y => TwoH p q 128 1024 x ∧ TwoH p q 128 1024 y ∧ x.gpr p.1 = y.gpr p.1 ∧
      x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp) (cbd2At p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr cbd2_correct cbd2_ct (V := fun x x1 => ((x1.gpr .rdi = pa x p ∧ x1.gpr .rsi = pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (lea_nomem _ _) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨accGlue_ok p q hx.off.1 hx.off.2 hq1 x, accGlue_ok p q hy.off.1 hy.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, cbdPre hx hv1 k1, cbdPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [cbd2K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]

theorem encPre {p q : Ptr} {s s1 : State} (h : TwoH p q 1024 384 s) (hr : Reduced s.mem (pa s p))
    (hv : s1.gpr .rdi = pa s p ∧ s1.gpr .rsi = pa s q) (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    encode12K.pre (s1.callEntry.withRegions [pR (pa s p)] [⟨pa s q, 384⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [encode12K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  refine ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ), ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kP), hm]; exact hr

theorem enc12At_ok {p q : Ptr} (hq : NA q) {s : State} (h : TwoH p q 1024 384 s) (hr : Reduced s.mem (pa s p)) :
    WP isa (enc12At p q) s fun s' => Post s s' [⟨pa s q, 384⟩] ∧
      bytesAt s'.mem (pa s q) 384 = encode12 (polyAt s.mem (pa s p)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok encode12_correct encode12_nosp (by rw [encode12_depth]; decide)
    (accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv hm k => encPre h hr hv hm k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [encode12K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂, ce_polyAt s1 (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem enc12At_tr {p q : Ptr} (hq : NA q) :
    RelCT isa (fun x y => (TwoH p q 1024 384 x ∧ Reduced x.mem (pa x p)) ∧ (TwoH p q 1024 384 y ∧
      Reduced y.mem (pa y p)) ∧ x.gpr p.1 = y.gpr p.1 ∧ x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp)
      (enc12At p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr encode12_correct encode12_ct (V := fun x x1 => ((x1.gpr .rdi = pa x p ∧ x1.gpr .rsi = pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (lea_nomem _ _) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨accGlue_ok p q hx.1.off.1 hx.1.off.2 hq1 x, accGlue_ok p q hy.1.off.1 hy.1.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, encPre hx.1 hx.2 hv1 hm1 k1, encPre hy.1 hy.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact hx.1.c, by rw [k1.2.2]; exact hx.1.w, by rw [k2.2.1, k2.2.2]; exact hy.1.c,
        by rw [k2.2.2]; exact hy.1.w, by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [encode12K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]

theorem decPre {p q : Ptr} {s s1 : State} (h : TwoH p q 384 1024 s) (hv : s1.gpr .rdi = pa s p ∧ s1.gpr .rsi = pa s q)
    (k : Keep argRegs s s1) : decode12K.pre (s1.callEntry.withRegions [⟨pa s p, 384⟩] [pR (pa s q)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decode12K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  exact ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ)⟩

theorem dec12At_ok {p q : Ptr} (hq : NA q) {s : State} (h : TwoH p q 384 1024 s) :
    WP isa (dec12At p q) s fun s' => Post s s' [pR (pa s q)] ∧
      PolyIs s'.mem (pa s q) (decode12 (bytesAt s.mem (pa s p) 384)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok decode12_correct decode12_nosp (by rw [decode12_depth]; decide)
    (accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv _ k => decPre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decode12K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂,
    ce_bytesAt s1 (n := 384) (by decide) (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem dec12At_tr {p q : Ptr} (hq : NA q) :
    RelCT isa (fun x y => TwoH p q 384 1024 x ∧ TwoH p q 384 1024 y ∧ x.gpr p.1 = y.gpr p.1 ∧
      x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp) (dec12At p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr decode12_correct decode12_ct (V := fun x x1 => ((x1.gpr .rdi = pa x p ∧ x1.gpr .rsi = pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (lea_nomem _ _) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨accGlue_ok p q hx.off.1 hx.off.2 hq1 x, accGlue_ok p q hy.off.1 hy.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, decPre hx hv1 k1, decPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [decode12K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]


/-! ## `ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` -/

theorem sw32_64' (d : Nat) (hd : d < 2 ^ 32) : ((BitVec.ofNat 64 d).setWidth 32).toNat = d := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem widths_lt {d : Nat} (h : d ∈ compressWidths) : d ≤ 10 := by
  simp only [compressWidths, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- What a call of `vg_mlkem_compress_encode` of `f` to `out` with width `d` needs. -/
structure CEH (f out : Ptr) (d : Nat) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31
  dw : d ∈ compressWidths
  red : Reduced s.mem (pa s f)
  dj : Region.Disjoint (pR (pa s f)) ⟨pa s out, 32 * d⟩
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  kO : (below (s.gpr .rsp) 32).Disjoint ⟨pa s out, 32 * d⟩
  c : Covers ([pR (pa s f)] ++ [⟨pa s out, 32 * d⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s out, 32 * d⟩] s.wr

theorem ceGlue_ok (f out : Ptr) (d : Nat) (ho : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31) (hd : d ≤ 10) (hout : NA out) (s : State) :
    WP isa (.block (lea .rdi f ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rdx out ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) s fun s1 =>
      ((s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 d ∧ s1.gpr .rdx = pa s out ∧
        s1.gpr .rcx = BitVec.ofNat 64 (32 * d)) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  have o1 : out.1 ≠ .rsi := fun e => hout (by rw [e]; decide)
  have o2 : out.1 ≠ .rdi := fun e => hout (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2, o1, o2, sw_ofNat (show d < 2 ^ 32 by omega),
    sw_ofNat (show 32 * d < 2 ^ 32 by omega), List.cons_append, List.nil_append]

theorem cePre {f out : Ptr} {d : Nat} {s s1 : State} (h : CEH f out d s)
    (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 d ∧ s1.gpr .rdx = pa s out ∧
      s1.gpr .rcx = BitVec.ofNat 64 (32 * d)) (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    compressEncodeK.pre (s1.callEntry.withRegions [pR (pa s f)] [⟨pa s out, 32 * d⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hd := widths_lt h.dw
  simp only [compressEncodeK, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega)]
  refine ⟨trivial, trivial, h.dj, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kO),
    h.dw, trivial, ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.red

theorem ceAt_ok {f out : Ptr} {d : Nat} (hout : NA out) {s : State} (h : CEH f out d s) :
    WP isa (ceAt f d out) s fun s' => Post s s' [⟨pa s out, 32 * d⟩] ∧
      bytesAt s'.mem (pa s out) (32 * d) = compressEncode d (polyAt s.mem (pa s f)) := by
  have hd := widths_lt h.dw
  refine WP.mono (glueCall_ok compressEncode_correct ce_nosp (by rw [ce_depth]; decide)
    (ceGlue_ok f out d h.off hd hout s) (fun s1 hv hm k => cePre h hv hm k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [compressEncodeK, dArg, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, hm₂, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega),
    ce_polyAt s1 (by rw [hsp]; exact h.kF), hm] at hq
  exact hq

theorem ceAt_tr {f out : Ptr} {d : Nat} (hout : NA out) :
    RelCT isa (fun x y => CEH f out d x ∧ CEH f out d y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr out.1 = y.gpr out.1 ∧
      x.gpr .rsp = y.gpr .rsp) (ceAt f d out) fun _ _ => True :=
  glueCall_tr compressEncode_correct compressEncode_ct (V := fun x x1 => ((x1.gpr .rdi = pa x f ∧
      x1.gpr .rsi = BitVec.ofNat 64 d ∧ x1.gpr .rdx = pa x out ∧ x1.gpr .rcx = BitVec.ofNat 64 (32 * d)) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (mov32i_nomem _ _)) (lea_nomem _ _))
      (mov32i_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨ceGlue_ok f out d hx.off (widths_lt hx.dw) hout x,
      ceGlue_ok f out d hy.off (widths_lt hy.dw) hout y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, cePre hx hv1 hm1 k1, cePre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [compressEncodeK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

/-- What a call of `vg_mlkem_decode_decompress` of the `32d` bytes at `b` to `f` needs. -/
structure DDH (b f : Ptr) (d : Nat) (s : State) : Prop where
  off : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31
  dw : d ∈ compressWidths
  dj : Region.Disjoint ⟨pa s b, 32 * d⟩ (pR (pa s f))
  kB : (below (s.gpr .rsp) 32).Disjoint ⟨pa s b, 32 * d⟩
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  c : Covers ([⟨pa s b, 32 * d⟩] ++ [pR (pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (pa s f)] s.wr

theorem ddGlue_ok (b f : Ptr) (d : Nat) (ho : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31) (hd : d ≤ 10) (hf : NA f) (s : State) :
    WP isa (.block (lea .rdi b ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))),
      .mov32 .rdx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rcx f)) s fun s1 =>
      ((s1.gpr .rdi = pa s b ∧ s1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ s1.gpr .rdx = BitVec.ofNat 64 d ∧
        s1.gpr .rcx = pa s f) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  have o1 : f.1 ≠ .rsi := fun e => hf (by rw [e]; decide)
  have o2 : f.1 ≠ .rdi := fun e => hf (by rw [e]; decide)
  have o3 : f.1 ≠ .rdx := fun e => hf (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2, o1, o2, o3, sw_ofNat (show d < 2 ^ 32 by omega),
    sw_ofNat (show 32 * d < 2 ^ 32 by omega), List.cons_append, List.nil_append]

theorem ddPre {b f : Ptr} {d : Nat} {s s1 : State} (h : DDH b f d s)
    (hv : s1.gpr .rdi = pa s b ∧ s1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ s1.gpr .rdx = BitVec.ofNat 64 d ∧
      s1.gpr .rcx = pa s f) (k : Keep argRegs s s1) :
    decodeDecompressK.pre (s1.callEntry.withRegions [⟨pa s b, 32 * d⟩] [pR (pa s f)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hd := widths_lt h.dw
  simp only [decodeDecompressK, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega)]
  exact ⟨trivial, trivial, h.dj, ret_disj s1 (by rw [hsp]; exact h.kB), ret_disj s1 (by rw [hsp]; exact h.kF),
    h.dw, trivial⟩

theorem ddAt_ok {b f : Ptr} {d : Nat} (hf : NA f) {s : State} (h : DDH b f d s) :
    WP isa (ddAt b d f) s fun s' => Post s s' [pR (pa s f)] ∧
      PolyIs s'.mem (pa s f) (decodeDecompress d (bytesAt s.mem (pa s b) (32 * d))) := by
  have hd := widths_lt h.dw
  refine WP.mono (glueCall_ok decodeDecompress_correct dd_nosp (by rw [dd_depth]; decide)
    (ddGlue_ok b f d h.off hd hf s) (fun s1 hv _ k => ddPre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decodeDecompressK, dArg, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, hm₂, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega),
    ce_bytesAt s1 (n := 32 * d) (by omega) (by rw [hsp]; exact h.kB), hm] at hq
  exact hq

theorem ddAt_tr {b f : Ptr} {d : Nat} (hf : NA f) :
    RelCT isa (fun x y => DDH b f d x ∧ DDH b f d y ∧ x.gpr b.1 = y.gpr b.1 ∧ x.gpr f.1 = y.gpr f.1 ∧
      x.gpr .rsp = y.gpr .rsp) (ddAt b d f) fun _ _ => True :=
  glueCall_tr decodeDecompress_correct decodeDecompress_ct (V := fun x x1 => ((x1.gpr .rdi = pa x b ∧
      x1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ x1.gpr .rdx = BitVec.ofNat 64 d ∧ x1.gpr .rcx = pa x f) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨ddGlue_ok b f d hx.off (widths_lt hx.dw) hf x,
      ddGlue_ok b f d hy.off (widths_lt hy.dw) hf y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, ddPre hx hv1 k1, ddPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [decodeDecompressK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]


/-! ## `SampleNTT` -/

/-- What a call of `vg_mlkem_sample_ntt` of the seed at `SB` to `a` needs. -/
structure SampH (a : Ptr) (s : State) : Prop where
  off : a.2 < 2 ^ 31
  dSA : Region.Disjoint ⟨pa s (sc oSB), 34⟩ (pR (pa s a))
  dSZ : Region.Disjoint ⟨pa s (sc oSB), 34⟩ ⟨pa s (sc oSS), 2048⟩
  dAZ : (pR (pa s a)).Disjoint ⟨pa s (sc oSS), 2048⟩
  kS : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oSB), 34⟩
  kA : (below (s.gpr .rsp) 32).Disjoint (pR (pa s a))
  kZ : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oSS), 2048⟩
  nw : (pa s (sc oSS)).toNat + 2048 ≤ 2 ^ 64
  c : Covers ([⟨pa s (sc oSB), 34⟩] ++ [pR (pa s a), ⟨pa s (sc oSS), 2048⟩]) (s.rd ++ s.wr)
  w : Covers [pR (pa s a), ⟨pa s (sc oSS), 2048⟩] s.wr

theorem sampGlue_ok (a : Ptr) (ha : a.2 < 2 ^ 31) (hna : NA a) (s : State) :
    WP isa (.block (lea .rdi (sc oSB) ++ lea .rsi a ++ lea .rdx (sc oSS))) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc oSB) ∧ s1.gpr .rsi = pa s a ∧ s1.gpr .rdx = pa s (sc oSS)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : a.1 ≠ .rdi := fun e => hna (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ha, sx_ofNat (show oSB < 2 ^ 31 by decide), sx_ofNat (show oSS < 2 ^ 31 by decide), o1,
    List.cons_append, List.nil_append]

theorem sampPre {a : Ptr} {s s1 : State} (h : SampH a s)
    (hv : s1.gpr .rdi = pa s (sc oSB) ∧ s1.gpr .rsi = pa s a ∧ s1.gpr .rdx = pa s (sc oSS))
    (k : Keep argRegs s s1) :
    sampleK.pre (s1.callEntry.withRegions [⟨pa s (sc oSB), 34⟩] [pR (pa s a), ⟨pa s (sc oSS), 2048⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [sampleK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hv.1, hv.2.1, hv.2.2]
  exact ⟨trivial, trivial, h.dSA, h.dSZ, h.dAZ, ret_disj s1 (by rw [hsp]; exact h.kS),
    ret_disj s1 (by rw [hsp]; exact h.kA), ret_disj s1 (by rw [hsp]; exact h.kZ),
    stk_disj s1 (by rw [hsp]; exact h.kS), stk_disj s1 (by rw [hsp]; exact h.kA),
    stk_disj s1 (by rw [hsp]; exact h.kZ), h.nw⟩

theorem and15_ok (s : State) :
    WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- What a call of `SampleNTT` leaves. -/
structure SampPost (a : Ptr) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([pR (pa s a), ⟨pa s (sc oSS), 2048⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
    (if (sampleNTT minIterations (bytesAt s.mem (pa s (sc oSB)) 34)).isSome then 1 else 0))
  res : ∀ f, sampleNTT minIterations (bytesAt s.mem (pa s (sc oSB)) 34) = some f → PolyIs s'.mem (pa s a) f

theorem sampleAt_ok {a : Ptr} (hna : NA a) {s : State} (h : SampH a s) : WP isa (sampleAt a) s (SampPost a s) := by
  refine WP.seq (WP.mono (sampGlue_ok a h.off hna s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.call sample_correct sample_nosp (by rw [sample_depth]; decide) (sampPre h hv k)
    (by rw [k.2.1, k.2.2]; exact h.c) (by rw [k.2.2]; exact h.w) fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂, ce_bytesAt s1 (n := 34) (by decide)
    (by rw [hsp]; exact h.kS), hm] at hpost
  rw [hg₂ .rax (by decide)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    rw [sample_depth] at hf
    exact Frame.below_mono hf (by omega) (by omega)
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hpost.1]
  · rw [hm3]; exact hpost.2

theorem sampleAt_tr {a : Ptr} (hna : NA a) :
    RelCT isa (fun x y => SampH a x ∧ SampH a y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr a.1 = y.gpr a.1 ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34)
      (sampleAt a) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (SampH a x ∧ SampH a y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr a.1 = y.gpr a.1 ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34) ∧
      (((x1.gpr .rdi = pa x (sc oSB) ∧ x1.gpr .rsi = pa x a ∧ x1.gpr .rdx = pa x (sc oSS)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc oSB) ∧ y1.gpr .rsi = pa y a ∧ y1.gpr .rdx = pa y (sc oSS)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨sampGlue_ok a hx.off hna x, sampGlue_ok a hy.off hna y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (RelCT.callEx sample_correct sample_ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, sampPre hx hv1 k1, sampPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
    by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
    by rw [hs1, hs2, e3]⟩
  simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
    ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2]
  rw [ce_bytesAt x1 (n := 34) (by decide) (by rw [hs1]; exact hx.kS),
    ce_bytesAt y1 (n := 34) (by decide) (by rw [hs2]; exact hy.kS), hm1, hm2, e4]
  simp only [pa, e1, e2, hs1, hs2, e3, and_self]

end VG.Proof.MlKem.X86_64
