import VerifiedGarbage.Proof.AesGcm.X86_64.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT

/-!
# AES-GCM on x86-64: `textAbsorb` in two runs

Untrusted: everything here is checked by Lean. Two runs of `textAbsorb`
with the same lengths and data address kept in `W` leak the same: its
branches are on the lengths, the padding of the additional data is
`flush_rel`, and the text is absorbed by `absorb_rel`.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem TaIn.keep {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s s' : State}
    (h : TaIn Ctx St W SP H aL tL D n s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TaIn Ctx St W SP H aL tL D n s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.hH, by rw [hm]; exact h.alen, by rw [hm]; exact h.tlen,
    by rw [hm]; exact h.dat, by rw [hm]; exact h.len, h.data.of_eq hrd hwr⟩

omit L in
theorem ta1_ok {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State} (h : TaIn Ctx St W SP H aL tL D n s) :
    WP isa (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .test .rbp (.reg .rbp)]) s fun s₁ =>
      TaIn Ctx St W SP H aL tL D n s₁ ∧ s₁.zf = some (decide (n = 0)) := by
  have r₁ := h.env.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbp (.mem (at_ .r15 lenO)),
      .alu .test .rbp (.reg .rbp)] s = some s₁ ∧ s₁.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.env.r15, r₁], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, h.len]; rw [and_self_beq h.data.lt]
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hz₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)

omit L in
theorem ta2_ok {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State} (h : TaIn Ctx St W SP H aL tL D n s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s fun s₁ =>
      TaIn Ctx St W SP H aL tL D n s₁ ∧ s₁.zf = some (decide (tL.toNat = 0)) := by
  have r₂ := h.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (tL.toNat = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [h.env.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, h.tlen]
      have := and_self_beq tL.isLt
      rw [BitVec.ofNat_toNat] at this
      exact congrArg some this
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₂, run₂, h.keep (fun r hr => ?_) hm₂ hrd₂ hwr₂, hz₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)

omit L in
theorem taA_ok {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State} (h : TaIn Ctx St W SP H aL tL D n s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      TaIn Ctx St W SP H aL tL D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (aL.toNat % 16) := by
  have r₃ := h.env.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hand := and15 aL
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL.toNat % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    refine ⟨_, by xrun [h.env.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, h.alen, hand]
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₃, run₃, h.keep (fun r hr => ?_) hm₃ hrd₃ hwr₃, hbx₃⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)

/-- `flush 16` keeps what `textAbsorb` needs. -/
theorem taFlush_ok {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State}
    (h : TaIn Ctx St W SP H aL tL D n s) (hbx : s.gpr .rbx = BitVec.ofNat 64 (aL.toNat % 16)) :
    WP isa (flush v.callees 16) s (TaIn Ctx St W SP H aL tL D n) := by
  refine WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (H := H) (x := List.replicate aL.toNat 0)
    ⟨h.env, h.hH⟩ (by simpa using hbx))) fun s' ⟨o, hrd, hwr⟩ => ?_
  have g := tFrame_taFrame o.frame
  have rd : ∀ d, 176 ≤ d → d + 8 ≤ 512 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => g.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_taFrame L h₁ h₂) (by decide)
  exact ⟨o.env, o.hH, by rw [rd 184 (by decide) (by decide)]; exact h.alen, by rw [rd 192 (by decide) (by decide)]; exact h.tlen,
    by rw [rd 200 (by decide) (by decide)]; exact h.dat, by rw [rd 208 (by decide) (by decide)]; exact h.len,
    h.data.of_eq hrd hwr⟩

omit L in
theorem ta3_ok {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State} (h : TaIn Ctx St W SP H aL tL D n s) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)),
      .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      ∃ H', AbsIn Ctx St W SP 16 H' (List.replicate (tL.toNat % 16) 0) D n s₁ := by
  have he := h.env
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have hand := and15 tL
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₄, run₄, h12, hbp, hbx, hg₄, -, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)] s = some s₄ ∧
      s₄.gpr .r12 = D ∧ s₄.gpr .rbp = BitVec.ofNat 64 n ∧ s₄.gpr .rbx = BitVec.ofNat 64 (tL.toNat % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₄.gpr r = s.gpr r) ∧ s₄.mem = s.mem ∧ s₄.rd = s.rd ∧
      s₄.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂, q₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.dat]
    · simp [gpr_setReg, h.len]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, h.tlen, hand]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₄, run₄, _, he.keep (fun r hr => ?_) hrd₄ hwr₄, h12, hbp, by simpa using hbx,
    h.data.of_eq hrd₄ hwr₄, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)

/-- `textAbsorb`, with the same lengths and data address kept in `W`. -/
theorem textAbsorb_rel {H₁ H₂ : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ => TaIn Ctx St W SP H₁ aL tL D n s₁ ∧ TaIn Ctx St W SP H₂ aL tL D n s₂)
      (textAbsorb v.callees) fun _ _ => True := by
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => TaIn Ctx St W SP H₁ aL tL D n s₁ ∧ TaIn Ctx St W SP H₂ aL tL D n s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.env h.2.env) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => ta1_ok h) (fun s h => ta1_ok h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ (TaIn Ctx St W SP H₁ aL tL D n s₁ ∧
      s₁.zf = some (decide (n = 0))) ∧ (TaIn Ctx St W SP H₂ aL tL D n s₂ ∧ s₂.zf = some (decide (n = 0)))) ∧
      s₁.zf = some false) [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.env h.1.2.2.1.env)
      ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => ta2_ok h) (fun s h => ta2_ok h)
  refine RelCT.seq b (RelCT.seq (R := fun (s₁ s₂ : State) => TaIn Ctx St W SP H₁ aL tL D n s₁ ∧
    TaIn Ctx St W SP H₂ aL tL D n s₂) ?_ ?_)
  · refine rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2]) ?_
      (RelCT.block_nil fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
    have c := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ (TaIn Ctx St W SP H₁ aL tL D n s₁ ∧
        s₁.zf = some (decide (tL.toNat = 0))) ∧ (TaIn Ctx St W SP H₂ aL tL D n s₂ ∧
        s₂.zf = some (decide (tL.toNat = 0)))) ∧ s₁.zf = some true) [.r13, .r14, .r15, .rsp]
        (fun _ _ h => env_agree h.1.2.1.1.env h.1.2.2.1.env) ⟨_, by taint_decide⟩)
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => taA_ok h) (fun s h => taA_ok h)
    have hF : ∀ {H : Block} (s : State), (TaIn Ctx St W SP H aL tL D n s ∧ s.gpr .rbx = BitVec.ofNat 64 (aL.toNat % 16)) →
        WP isa (flush v.callees 16) s (TaIn Ctx St W SP H aL tL D n) := fun s h => taFlush_ok v L h.1 h.2
    have f := rel_wp ((flush_rel v L (.inr rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
        (TaIn Ctx St W SP H₁ aL tL D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (aL.toNat % 16)) ∧
        (TaIn Ctx St W SP H₂ aL tL D n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (aL.toNat % 16)))
        (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
      (fun _ _ h => h.2) (fun s h => hF s h) (fun s h => hF s h)
    exact (RelCT.seq c f).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The text.
  have d := rel_wp (rel_taint (P := fun s₁ s₂ => TaIn Ctx St W SP H₁ aL tL D n s₁ ∧ TaIn Ctx St W SP H₂ aL tL D n s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.env h.2.env) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => ta3_ok h) (fun s h => ta3_ok h)
  have e := RelCT.exists_ fun H₁' => RelCT.exists_ fun H₂' =>
    absorb_rel v L (.inr rfl) (H₁ := H₁') (H₂ := H₂') (x₁ := List.replicate (tL.toNat % 16) 0)
      (x₂ := List.replicate (tL.toNat % 16) 0) (D := D) (n := n) rfl
  exact RelCT.seq d (e.mono (fun _ _ ⟨_, ⟨H₁', h₁⟩, ⟨H₂', h₂⟩⟩ => ⟨H₁', H₂', h₁, h₂⟩) fun _ _ h => h)

end

end VG.Proof.AesGcm.X86_64
