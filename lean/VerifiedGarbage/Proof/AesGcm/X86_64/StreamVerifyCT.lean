import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinishCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. The only branch is on the
tag length (`tagLenOk`, checked by the taint analysis); the tag is computed
from the same lengths and number of rounds (`finTag_rel`), and the
comparison and the mask have no branch.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- The lengths and rounds kept, and the tag length at `W + 224`. -/
def VerS (Ctx St W SP : Addr) (R : Nat) (aL tL tl : BitVec 64) (s : State) : Prop :=
  FinS Ctx St W SP R aL tL s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl

theorem verifyEntry_ok {s : State} (hp : Proof.AesGcm.verifyPre s) :
    WP isa (.block (finEntry ++ ([.mov .rbx (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rbx] : List Instr))) s fun s₂ =>
      VerS (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r9) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8)
        (stackArg s 0) s₂ ∧ s₂.gpr .rbx = stackArg s 0 := by
  have hp' := hp
  simp only [Proof.AesGcm.verifyPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds,
    Proof.AesGcm.args] at hp'
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, d_sa, d_wa, r_s, r_w, k_c, k_s, k_w, wc, ws, ww, wsp, hR⟩ := hp'
  have htlR : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  generalize stackArg s 0 = tl at *
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : s.gpr .r9 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have L : Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have hperm : Perm Ctx St W s := ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  have hA : stackArgAddr s 0 = SP + BitVec.ofNat 64 8 := by simp [stackArgAddr, hSP]
  rw [hA] at d_sa d_wa hrd
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hSP hperm ww hR) fun s₁ he => ?_)
  have dA : ∀ r ∈ [savedR W, slotsR W], (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact d_wa.symm.sub_right (Lay.wSub (by decide))
  have htl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = tl := by
    rw [he.frame.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) dA (by decide), htlR]
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 8) 8 := by
    rw [he.rd, he.wr, hrd]
    exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩
  have w₁ := he.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 8)),
      .store (at_ .r15 tlO) .rbx] s₁ = some s₂ ∧ s₂.gpr .rbx = tl ∧ (∀ r, r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) tl ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.rsp, he.env.r15, r₁, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₁]
    · intro r a; simp [gpr_setReg, a]
    · simp [htl₁]
    all_goals rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 224 ∨ 232 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h' (by decide)) (by decide)
  refine WP.of_runBlock ⟨s₂, run₂, ⟨⟨he.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂,
    ⟨by rw [rd₂ 176 (.inl (by decide)) (by decide)]; exact he.rounds.1, he.rounds.2⟩,
    by rw [rd₂ 184 (.inl (by decide)) (by decide)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (by decide)]; exact he.tlen⟩, by rw [hm₂, Mem.readW_writeW_self64]⟩, hbx₂⟩

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- The tag computed and compared, for an allowed length `t`. -/
theorem verifyCheck_rel {R t : Nat} (h1 : 1 ≤ t) (h16 : t ≤ 16) {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => (VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
        VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t)
      (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
        (.seq (cmp 0) (.block [.mov32 .rcx (imm 0), .alu .sub .rcx (.reg .rax), .mov .rdx (.mem (at_ .r15 0)),
          .alu .and .rdx (.reg .rcx), .store (at_ .r15 0) .rdx, .mov .rdx (.mem (at_ .r15 8)),
          .alu .and .rdx (.reg .rcx), .store (at_ .r15 8) .rdx]))))) fun _ _ => True := by
  -- `recv` keeps the lengths.
  have hR : ∀ s, VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s ∧ s.gpr .rbx = BitVec.ofNat 64 t →
      WP isa recv s (VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t)) := fun s ⟨⟨h, ht⟩, hbx⟩ =>
    WP.mono (recv_ok L h.1 hbx h1 h16) fun s' ⟨he', _, f, _⟩ => by
      have d : ∀ d, 176 ≤ d → d + 8 ≤ 256 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide)
      exact ⟨⟨he', rounds_frame f (d 176 (by decide) (by decide)) h.2.1,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 184 (by decide) (by decide)) (by decide), h.2.2.1],
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 192 (by decide) (by decide)) (by decide), h.2.2.2]⟩,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 224 (by decide) (by decide)) (by decide), ht]⟩
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => (VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 t) ∧ VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₂ ∧
      s₂.gpr .rbx = BitVec.ofNat 64 t) ([.rbx] ++ [.r13, .r14, .r15, .rsp])
      (fun _ _ h => EnvAgree.regs ⟨h.1.1.1.1, h.2.1.1.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hR hR
  -- `finTag` keeps the tag length.
  have hT : ∀ s, VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s → WP isa (finTag v.callees 0) s fun s' =>
      Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := fun s ⟨h, ht⟩ =>
    WP.mono (finTag_ok v L (.inl rfl) h.1 h.2.1 h.2.2.1 h.2.2.2
      (x := List.replicate ((if tL = 0 then aL.toNat else tL.toNat) % 16) 0) (by simp)) fun _ ⟨he', _, f, _⟩ =>
      ⟨he', by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.st_w (a := 0) (n := 32) (d := 224) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · simpa using L.w_w (a := 224) (n := 8) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w (by decide)).symm) (by decide), ht]⟩
  have b := rel_wp ((finTag_rel v L (R := R) (aL := aL) (tL := tL) (.inl rfl)).mono
      (P' := fun s₁ s₂ => True ∧ VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₁ ∧
        VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₂) (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hT hT
  -- The tag length, and the comparison and mask.
  have hL : ∀ s, (Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) →
      WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO))]) s fun s' => Env Ctx St W SP s' ∧
        s'.gpr .rbx = BitVec.ofNat 64 t := fun s ⟨he, ht⟩ => by
    have r₁ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
    obtain ⟨s₁, run₁, hbx, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s = some s₁ ∧
        s₁.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [he.r15, r₁], ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, ht]
      · intro r a; simp [gpr_setReg, a]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => ?_) hrd hwr, hbx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ (Env Ctx St W SP s₁ ∧
      s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧ (Env Ctx St W SP s₂ ∧
      s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.2.1.1 h.2.2.1) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hL hL
  have d := rel_taint (P := fun s₁ s₂ => True ∧ (Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
      (Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t)) (c := .seq (cmp 0)
      (.block [.mov32 .rcx (imm 0), .alu .sub .rcx (.reg .rax), .mov .rdx (.mem (at_ .r15 0)),
        .alu .and .rdx (.reg .rcx), .store (at_ .r15 0) .rdx, .mov .rdx (.mem (at_ .r15 8)),
        .alu .and .rdx (.reg .rcx), .store (at_ .r15 8) .rdx])) ([.rbx] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c d))

end

theorem streamVerify_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamVerifyX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamVerifyX86_64.pre s₀') (hq : Proof.AesGcm.streamVerifyX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamVerify v.callees) fun _ _ => True := by
  have L : Lay (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .r9) (s₀.gpr .rsp) := by
    have hp₀ := hp
    simp only [Proof.AesGcm.streamVerifyX86_64, Proof.AesGcm.verifyPre, Proof.AesGcm.stk, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, Proof.AesGcm.args] at hp₀
    obtain ⟨-, -, d_cs, d_cw, d_sw, -, -, -, -, k_c, k_s, k_w, wc, ws, ww, -, -⟩ := hp₀
    exact Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq
  have hE₂ := verifyEntry_ok hp'
  simp only [Proof.AesGcm.arg] at q₈
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  generalize hctx : s₀.gpr .rdi = Ctx at *
  generalize hst : s₀.gpr .rdx = St at *
  generalize hw : s₀.gpr .r9 = W at *
  generalize hsp : s₀.gpr .rsp = SP at *
  refine rel_reassoc_inner (fn_rel (Ctx := Ctx) (St := St) (W := W) (SP := SP) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hctx, ← q₁]
      · exact q₂
      · rw [hst, ← q₃]
      · exact q₄
      · exact q₅
      · rw [hw, ← q₆]
      · rw [hsp, ← q₇])
    ⟨_, by taint_decide⟩ (by have := verifyEntry_ok hp; rwa [hctx, hst, hw, hsp] at this) hE₂ ?_)
  generalize hR : (s₀.gpr .rsi).toNat = R
  generalize htl : stackArg s₀ 0 = tl
  generalize ht : tl.toNat = t
  have htl' : tl = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  subst htl'
  -- The tag length.
  let A : State → Prop := fun s => (VerS Ctx St W SP R (s₀.gpr .rcx) (s₀.gpr .r8) (BitVec.ofNat 64 t) s ∧
    s.gpr .rbx = BitVec.ofNat 64 t) ∧ s.zf = some (!Spec.Gcm.tagLenOk t)
  have hK : ∀ s, VerS Ctx St W SP R (s₀.gpr .rcx) (s₀.gpr .r8) (BitVec.ofNat 64 t) s ∧
      s.gpr .rbx = BitVec.ofNat 64 t → WP isa tagLenOk s A := fun s ⟨⟨h, hm⟩, hbx⟩ =>
    WP.mono (tagLenOk_ok s hbx (by rw [← ht]; exact (BitVec.ofNat 64 t).isLt)) fun s' ⟨hz, k⟩ =>
      ⟨⟨⟨h.keep (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> decide)) k.mem k.rd k.wr, by rw [k.mem]; exact hm⟩,
        by rw [k.gpr _ (by decide), hbx]⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => True ∧
      (VerS Ctx St W SP R (s₀.gpr .rcx) (s₀.gpr .r8) (BitVec.ofNat 64 t) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
      (VerS Ctx St W SP R (s₀.gpr .rcx) (s₀.gpr .r8) (BitVec.ofNat 64 t) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t))
      ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.1.1, h.2.2.1.1.1,
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hK hK
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length §5.2.1.2 does not allow (`rax` is 0 and the tag zeroed).
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.1.1, h.1.2.2.1.1.1.1⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.1.1 h.1.2.2.1.1.1.1)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
      omega
    have hc : ∀ s, (VerS Ctx St W SP R (s₀.gpr .rcx) (s₀.gpr .r8) (BitVec.ofNat 64 t) s ∧
        s.gpr .rbx = BitVec.ofNat 64 t) → WP isa (.seq recv (.seq (finTag v.callees 0)
          (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (.seq (cmp 0) (.block [.mov32 .rcx (imm 0),
            .alu .sub .rcx (.reg .rax), .mov .rdx (.mem (at_ .r15 0)), .alu .and .rdx (.reg .rcx),
            .store (at_ .r15 0) .rdx, .mov .rdx (.mem (at_ .r15 8)), .alu .and .rdx (.reg .rcx),
            .store (at_ .r15 8) .rdx]))))) s (Env Ctx St W SP) := fun s ⟨⟨h, hm⟩, hbx⟩ =>
      WP.mono (verifyCheck_ok v L h.1 h.2.1 h.2.2.1 h.2.2.2 hm hbx hb.1 hb.2
        (x := List.replicate ((if s₀.gpr .r8 = 0 then (s₀.gpr .rcx).toNat else (s₀.gpr .r8).toNat) % 16) 0)
        (by simp)) fun _ h => h.1
    exact (rel_wp ((verifyCheck_rel v L hb.1 hb.2).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) hc hc).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamVerifyX86_64.pre Proof.AesGcm.streamVerifyX86_64.pub
      (streamVerify v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamVerify_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
