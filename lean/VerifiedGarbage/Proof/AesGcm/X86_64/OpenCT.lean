import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_open` is constant time

Untrusted: everything here is checked by Lean. The first branch is on the
tag length (public); then both runs go through `oneAad`, `oneBlocks` and
`oneTag` with the same public data, as in `seal`, and copy and compare the
tags without a branch (the taint analysis). The second branch is on the
comparison, which `open` may leak: correctness says it is whether
`openResult` succeeds (`openPre_ok`), the same in both runs by `pub`; then
both runs decrypt the rest (`oneCrypt`) or encrypt the whole blocks again
(`oneUndo_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- `a; (b; (c; (d; (e; (f; (g; h))))))`, related as `(a; (b; (c; (d; (e; (f; g)))))); h`. -/
theorem rel_reassoc7 {P Q : State → State → Prop} {a b c d e f g h : Prog isa}
    (hr : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) h) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f (.seq g h))))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with | seq d₁ e₁ =>
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq f₁ e₁ => cases e₁ with | seq g₁ h₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with | seq d₂ e₂ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq f₂ e₂ => cases e₂ with | seq g₂ h₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq x₁ (.seq f₁ g₁)))))) h₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq x₂ (.seq f₂ g₂)))))) h₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- What `open`'s entry leaves, for a tag length `t`. -/
abbrev OpenIn (s₀ : State) (Ctx W SP A D : Addr) (n t : Nat) (s : State) : Prop :=
  OneEntry s₀ Ctx W SP A D n s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t

/-- `oneAad`'s precondition, after the entry. -/
theorem OneEntry.aadPre {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s) (hNp : s₀.gpr .rdx = Np)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) (hR : (s₀.gpr .rsi).toNat = R) :
    OneS Ctx W SP R A al D n none s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl :=
  ⟨⟨E.env, hR ▸ E.rounds, E.aad, by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    C.aad.of_eq E.rd E.wr, C.data.of_eq E.rd E.wr, fun _ h => nomatch h⟩, by rw [E.r12, hNp],
    by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq], C.nonce.of_eq E.rd E.wr⟩

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneAad` keeps the tag length. -/
theorem aadTl_ok {s₀ s : State} {Np A D : Addr} {nl al n t : Nat} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (h : OpenIn s₀ Ctx W SP A D n t s) :
    WP isa (oneAad v.callees) s fun s' => s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t :=
  WP.mono (oneMid_ok v C h.1 hNp hnl hal) fun _ M => by
    rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm) (by decide), h.2.2]

/-- `oneBlocks` keeps the tag length, and what stays in `W`. -/
theorem blocksTl_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {s : State}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat)
    (h : OneS Ctx W SP R A al D n none s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) :
    WP isa (oneBlocks v.callees.dec) s fun s' =>
      OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t :=
  WP.mono (oneBlocksD_ok L v ⟨h.1.env, h.1.rounds, h.1.dat, h.1.len, h.1.dD, t_c, t_w, t_d, sp24⟩) fun _ ⟨P, _⟩ =>
    ⟨ObPost.oneS L t_w h.1 P, by
      rw [(obFrame_B P.frame).readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrameB L h.1.dD.ok.w t_w (.inr ⟨by decide, by decide⟩)) (by decide), h.2]⟩

/-- `oneTag` keeps `OneS` and the tag length. -/
theorem tagTl_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n N t : Nat} {s : State} (hN : N < 2 ^ 64)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h : OneS Ctx W SP R A al D n (some N) s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) :
    WP isa (oneTag v.callees uO) s fun s' => OneS Ctx W SP R A al D n (some N) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t :=
  WP.mono (oneTag_ok v L (.inr rfl) (x := []) (by decide) h.1.env rfl h.1.rounds h.1.dat h.1.len (h.1.tlen N rfl) hN
    h.1.alen h.1.dD.ok hDW h.1.dD.ctx) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := D) (n := n) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hDW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hDW (.inr ⟨by decide, by decide⟩)) (by decide), h.2]⟩

omit L in
/-- The tag length loaded into `rbx`. -/
theorem loadTl_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {T : Option Nat} {s : State}
    (h : OneS Ctx W SP R A al D n T s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO))]) s fun s' => OneS Ctx W SP R A al D n T s' ∧
      s'.gpr .rbx = BitVec.ofNat 64 t := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hbx, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s = some s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, r₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm hrd hwr, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

omit L in
/-- The result loaded from `W + 216`. -/
theorem loadAux_ok {s : State} (h : Env Ctx (W + BitVec.ofNat 64 16) W SP s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 auxO))]) s (Env Ctx (W + BitVec.ofNat 64 16) W SP) := by
  have r₁ := h.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 auxO))] s = some s₁ ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.r15, r₁], ?_, ?_, ?_⟩
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hrd hwr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

end

/-- From the entry, for an allowed tag length: ZF says whether
`openResult` fails. -/
theorem openPre_ok (v : GcmImpl) {s s₁ : State} {Ctx W SP Np A D : Addr} {nl al n R t : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (h : OpenIn s Ctx W SP A D n t s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hal : (s.gpr .r9).toNat = al)
    (hR : (s.gpr .rsi).toNat = R) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (.seq (oneAad v.callees) (.seq (oneBlocks v.callees.dec) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
      (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))) s₁
      fun s' => (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s' ∧
        DataW Ctx (W + BitVec.ofNat 64 16) W SP s' D n) ∧
        s'.zf = some (!(Spec.Gcm.openResult (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) t
          (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem W t)).isSome) := by
  have L := C.lay
  have E := h.1
  have hS := (E.aadPre C hNp hnl hal hR).1
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  have hlt := C.data.ok.lt
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₃ M => ?_)
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm) (by decide), h.2.2]
  have hd₃ := C.data.of_eq M.rd M.wr
  have hS₃ : OneS Ctx W SP R A al D n none s₃ := hS.frame L M.env (M.rd.trans E.rd.symm) (M.wr.trans E.wr.symm) C.dE
    (wFrame_one (.inl rfl) (wFrame_cons M.fr))
  refine WP.mono (openFront_ok v L (al := al) ⟨M.env, hR ▸ M.rounds, M.dat, M.len, hd₃, C.t_c, C.t_w, C.t_d, C.sp24⟩
    M.hH hal₃ htl₃ hb.1 hb.2 M.abs M.j0 M.cb) fun s' F => ?_
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => F.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L C.dE C.t_w hd) (by decide)
  refine ⟨⟨⟨F.env, F.rounds, by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact hS₃.aad,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact hS₃.alen, F.dat, F.len, hS₃.dA.of_eq F.rd F.wr,
    (hS₃.dD.of_eq F.rd F.wr).drop (by omega), fun N hN => by cases hN; exact F.tlen⟩, hd₃.of_eq F.rd F.wr⟩, ?_⟩
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have dWR : ∀ r ∈ [oneR W], (⟨W, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hc₃ : ciphOf s₃.mem Ctx R = ctxCiph s.mem Ctx R := ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
  have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by omega)
  have hw₃ : bytesAt s₃.mem W t = bytesAt s.mem W t := by
    rw [bytesAt_take _ _ hb.2, bytesAt_take s.mem _ hb.2, bytesAt_frame M.fr (fun r hr => ?_) (by decide),
      bytesAt_frame E.frame dWR (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (a := 0) (n := 16) (by decide)).symm.sub_left
        (by simpa using Region.sub_prefix (base := W) (show 16 ≤ 16 by decide))
  have hz := F.zf
  rw [hc₃, hp₃, hw₃] at hz
  rw [hz]
  simp only [Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- From the entry to the comparison, for an allowed tag length. -/
theorem openPre_rel {s₀ s₀' : State} {Np A D : Addr} {nl al n R t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq (oneAad v.callees) (.seq (oneBlocks v.callees.dec) (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
        (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))))
      fun _ _ => True := by
  have hDW := C.dE
  have hlt := C.data.ok.lt
  have hDW' := C.dE.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega))
  have a := rel_wp ((oneAad_rel v L (R := R) (Np := Np) (nl := nl) (A := A) (al := al) (T := none) hDW).mono
      (P' := fun (s₁ s₂ : State) => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (fun _ _ h => ⟨h.1.1.aadPre C hNp hnl hal hR, h.2.1.aadPre C' hNp' hnl' hal' hR'⟩) fun _ _ h => h)
    (fun _ _ h => h) (fun _ h => aadTl_ok v L C hNp hnl hal h) (fun _ h => aadTl_ok v L C' hNp' hnl' hal' h)
  have bl := rel_wp ((oneBlocksD_rel v L (R := R) (A := A) (al := al) (T := none) C.t_c C.t_w C.t_d C.sp24).mono
      (P' := fun (s₁ s₂ : State) =>
        (OneS Ctx W SP R A al D n none s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧
        (OneS Ctx W SP R A al D n none s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t))
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => blocksTl_ok v L C.t_c C.t_w C.t_d C.sp24 h) (fun _ h => blocksTl_ok v L C.t_c C.t_w C.t_d C.sp24 h)
  have b := rel_wp ((oneTag_rel v L (.inr rfl) hDW' (N := n)).mono (P' := fun (s₁ s₂ : State) =>
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t))
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => tagTl_ok v L hlt hDW' h) (fun _ h => tagTl_ok v L hlt hDW' h)
  have c := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
        s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env ⟨h.2.1.1, h.2.2.1⟩) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => loadTl_ok h) (fun _ h => loadTl_ok h)
  have d := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
        s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
      (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
        s₂.gpr .rbx = BitVec.ofNat 64 t))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩)
    (RelCT.seq (bl.mono (fun _ _ h => h) fun _ _ h => h.2) (RelCT.seq b (RelCT.seq c d)))

/-- `oneUndo` in two runs: the same branch on the public length, and the same
arguments to `vg_aes_ctr32`. -/
theorem oneUndo_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ =>
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧
        (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n))
      (oneUndo v.callees) fun s₁ s₂ =>
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  let G₁ : State → Prop := fun s => s.zf = some (decide (n / 16 = 0)) ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧
    (n / 16 ≠ 0 → WP isa (.block undoB2) s fun s₂ =>
      CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
  have hw₁ : ∀ s, (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s ∧
      DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) → WP isa (.block undoB1) s G₁ := fun s h =>
    WP.mono (undo1_ok h.2.ok.lt h.1.env (h.1.tlen n rfl) h.1.dat) fun s₁ ⟨hcx, h8, z, g, m, rd, wr⟩ => by
      have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := h.1.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr
      exact ⟨z, he₁, fun _ => WP.mono (undo2_ok L he₁ ⟨by rw [m]; exact h.1.rounds.1, h.1.rounds.2⟩
        (h.2.of_eq rd wr) hcx h8) fun _ ⟨c, e, _⟩ => ⟨c, e⟩⟩
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.1.env h.2.1.env)
    ⟨_, by taint_decide⟩) (fun _ _ h => h) (G₁ := G₁) (G₂ := G₁) hw₁ hw₁
  have t := (rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some true) (c := .block [])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) (fun _ h => WP.block_nil h.2.1) (fun _ h => WP.block_nil h.2.1)).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block undoB2) s fun s₂ =>
      CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some false) (c := .block undoB2)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨⟨h.1.2.1, h.2⟩, ⟨h.1.2.2, by rw [h.1.2.2.1, ← h.1.2.1.1, h.2]⟩⟩) hw₂ hw₂
  have hw₃ : ∀ s, CtrCall s Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s →
      WP isa (.call v.ctr.callee.name v.ctr.callee.code) s (Env Ctx (W + BitVec.ofNat 64 16) W SP) := fun s h =>
    WP.mono (ctr_call v.ctr h.1) fun _ g => h.2.of_saved g.saved g.rd g.wr
  have c := (rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧
      (CtrCall s₁ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₁) ∧
      (CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
        Env Ctx (W + BitVec.ofNat 64 16) W SP s₂))
      fun _ _ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.rsp, h.2.2.2.rsp]⟩)
    (fun _ _ h => h.2) hw₃ hw₃).mono (fun _ _ h => h) fun _ _ h => h.2
  rw [oneUndo_eq]
  exact RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.1, h.2.2.1]) t (RelCT.seq b c))

/-- After the comparison: the rest decrypted if the tags match, the whole
blocks encrypted again if not, and the result loaded. -/
theorem openPost_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {b₁ b₂ : Bool} (hb : b₁ = b₂)
    (hDW' : (⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => True ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧ s₁.zf = some b₁) ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n) ∧ s₂.zf = some b₂))
      (.seq (.ite .e (oneUndo v.callees) (oneCrypt v.callees)) (.block [.mov .rax (.mem (at_ .r15 auxO))]))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have t := (oneUndo_rel v L (R := R) (A := A) (al := al) (D := D) (n := n)).mono
    (P' := fun (s₁ s₂ : State) => (True ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧ s₁.zf = some b₁) ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n) ∧ s₂.zf = some b₂)) ∧ s₁.zf = some true)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
  have e := (oneCrypt_rel v L (R := R) (A := A) (al := al) (T := some n) hDW').mono
    (P' := fun (s₁ s₂ : State) => (True ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₁ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n) ∧ s₁.zf = some b₁) ∧
        ((OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s₂ ∧
          DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n) ∧ s₂.zf = some b₂)) ∧ s₁.zf = some false)
    (Q' := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    (fun _ _ h => ⟨h.1.2.1.1.1, h.1.2.2.1.1⟩) fun _ _ h => ⟨h.1.env, h.2.env⟩
  have f := rel_wp (rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun _ h => loadAux_ok h) (fun _ h => loadAux_ok h)
  exact RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, hb]) t e)
    (f.mono (fun _ _ h => h) fun _ _ h => h.2)

end

/-- After the entry: the tag length checked, then the tag. -/
theorem openBody_rel (v : GcmImpl) {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (ht : t < 2 ^ 64)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem W t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem W t)).isSome) :
    RelCT isa (fun s₁ s₂ => True ∧ OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq tagLenOk (.ite .e (.block [.mov32 .rax (imm 0)])
        (.seq (oneAad v.callees)
        (.seq (oneBlocks v.callees.dec)
        (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
        (.seq recv
        (.seq (cmp uO)
        (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
        (.seq (.ite .e (oneUndo v.callees) (oneCrypt v.callees))
          (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))))))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  have hK : ∀ {s₀ s : State}, OpenIn s₀ Ctx W SP A D n t s → WP isa tagLenOk s fun s' =>
      OpenIn s₀ Ctx W SP A D n t s' ∧ s'.zf = some (!Spec.Gcm.tagLenOk t) := fun h =>
    WP.mono (tagLenOk_ok _ h.2.1 ht) fun _ ⟨hz, k⟩ =>
      ⟨⟨h.1.keep L (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k.rd k.wr
          (by rw [k.mem]; exact Frame.refl _ _), by rw [k.gpr _ (by decide), h.2.1], by rw [k.mem]; exact h.2.2⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun (s₁ s₂ : State) => True ∧ OpenIn s₀ Ctx W SP A D n t s₁ ∧
      OpenIn s₀' Ctx W SP A D n t s₂) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun _ h => hK h) (fun _ h => hK h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length §5.2.1.2 does not allow.
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.env, h.1.2.2.1.1.env⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.env h.1.2.2.1.1.env)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hlt := C.data.ok.lt
    refine rel_reassoc7 (RelCT.seq ?_ (openPost_rel v L (R := R) (A := A) (al := al) (congrArg (!·) hres)
      (C.dE.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega)))))
    exact rel_wp ((openPre_rel v L C C' hNp hnl hal hR hNp' hnl' hal' hR').mono
        (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h) (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
      (fun _ h => openPre_ok v C h hNp hnl hal hR hok) (fun _ h => openPre_ok v C' h hNp' hnl' hal' hR' hok)

theorem open_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.openX86_64.pre s₀)
    (hp' : Proof.AesGcm.openX86_64.pre s₀') (hq : Proof.AesGcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  have C := OneCtx.of hp
  have C' := OneCtx.of hp'
  have L := C.lay
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩, hres⟩ := hq
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃ hres
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₂] at C'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← a₀, ← a₁, ← a₂, ← a₃] at hres
  generalize ht : (stackArg s₀ 3).toNat = t at hres
  have hE : ∀ {s : State} (C : OneCtx s 4 (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8)
      (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .r8 = s₀.gpr .r8 →
      stackArg s 0 = stackArg s₀ 0 → (stackArg s 1).toNat = (stackArg s₀ 1).toNat → stackArg s 2 = stackArg s₀ 2 →
      stackArg s 3 = stackArg s₀ 3 →
      WP isa (.block (oneEntry ++ [.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx])) s
        (OpenIn s (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat t) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => WP.mono (openEntry_ok C h₁ h₂ h₃ h₄ h₅ h₆) fun _ ⟨E, hbx, htl, _⟩ =>
      ⟨E, by rw [hbx, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [htl, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl rfl
  have hE₂ := hE C' q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) a₂.symm a₃.symm
  rw [oneEntry] at hE₁ hE₂
  simp only [List.append_assoc] at hE₁ hE₂
  rw [«open», oneEntry]
  simp only [List.append_assoc]
  have ha₂ := C.args 2 (by decide); have ha₂' := C'.args 2 (by decide)
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 2 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 2) (SP := s₀.gpr .rsp) (k := 24) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩) a₂ (by simpa [hp.2.2.1] using ha₂)
    (by simpa [q₇] using ha₂') ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  exact openBody_rel v C C' rfl rfl rfl rfl q₃.symm (by rw [← q₄]) (by rw [← q₆]) (by rw [← q₂])
    (by rw [← ht]; exact (stackArg s₀ 3).isLt) hres

theorem open_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.openX86_64.pre Proof.AesGcm.openX86_64.pub («open» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => open_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
