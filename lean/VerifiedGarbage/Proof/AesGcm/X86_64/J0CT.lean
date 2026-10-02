import VerifiedGarbage.Proof.AesGcm.X86_64.J0
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT

/-!
# AES-GCM on x86-64: `j0` in two runs

Untrusted: everything here is checked by Lean. Two runs of `j0` for nonces
at the same address, of the same length, leak the same: the branch is on the
length, and the GHASH of a nonce of any other length is `absorb`, `flush`
and `lens` (`absorb_rel`, `flush_rel`, `lens_rel`), with the length kept at
`W + 216` between them.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- The nonce's length is kept at `W + 216`. -/
def AuxN (Ctx St W SP : Addr) (n : Nat) (s : State) : Prop :=
  Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

omit L in
theorem j0hashA_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In Ctx St W SP H Np n s) :
    WP isa (.block [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax, .store (at_ .r14 8) .rax,
      .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)]) s fun s₁ =>
      (∃ H', AbsIn Ctx St W SP 0 H' [] Np n s₁) ∧ AuxN Ctx St W SP n s₁ := by
  have he := h.env
  have h14 := he.r14; have h15 := he.r15
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have wa := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax,
      .store (at_ .r14 8) .rax, .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, h15, z₀, z₁, wa], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, h.rbp, Mem.readW_writeW_self64]
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨s₁, run₁, ⟨_, he₁, by rw [hg₁ _ (by decide) (by decide), h.r12],
    by rw [hg₁ _ (by decide) (by decide), h.rbp], by rw [hbx₁]; rfl, h.data.of_eq hrd₁ hwr₁, rfl⟩, he₁, hm₁⟩

omit L in
theorem auxLoad_ok {n : Nat} {s : State} (h : AuxN Ctx St W SP n s) (hn : n < 2 ^ 64) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 auxO)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      AuxN Ctx St W SP n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16) := by
  have ra := h.1.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have hand := and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at hand
  obtain ⟨s₁, run₁, hbx, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 auxO)),
      .alu .and .rbx (imm 15)] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16) ∧
      (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, h.2, hand]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, ⟨h.1.keep (fun r hr => ?_) hrd hwr, by rw [hm]; exact h.2⟩, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

omit L in
theorem auxLens_ok {n : Nat} {s : State} (h : AuxN Ctx St W SP n s) :
    WP isa (.block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))]) s fun s₁ =>
      Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n := by
  have ra := h.1.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hbx, hbp, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov32 .rbx (imm 0),
      .mov .rbp (.mem (at_ .r15 auxO))] s = some s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, h.2]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hrd hwr, hbx, hbp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- `J₀` of a nonce of any length but 12, for nonces at the same address, of
the same length. -/
theorem j0hash_rel {H₁ H₂ : Block} {Np : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ => J0In Ctx St W SP H₁ Np n s₁ ∧ J0In Ctx St W SP H₂ Np n s₂) (j0hash v.callees)
      fun _ _ => True := by
  by_cases hlt : n < 2 ^ 64
  swap
  · exact RelCT.of_false fun _ _ h => hlt h.1.data.lt
  -- After `absorb` and `flush`, the length is still kept.
  have hA : ∀ s, (∃ H', AbsIn Ctx St W SP 0 H' [] Np n s) ∧ AuxN Ctx St W SP n s →
      WP isa (absorb v.callees 0) s (AuxN Ctx St W SP n) := fun s ⟨⟨_, h⟩, ha⟩ =>
    WP.mono (absorb_ok v L (.inl rfl) h) fun _ o =>
      ⟨o.env, by rw [o.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (aux_absFrame L)
        (by decide), ha.2]⟩
  have hF : ∀ s, AuxN Ctx St W SP n s ∧ s.gpr .rbx = BitVec.ofNat 64 (n % 16) →
      WP isa (flush v.callees 0) s (AuxN Ctx St W SP n) := fun s ⟨ha, hbx⟩ =>
    WP.mono (flush_ok v L (yo := 0) (.inl rfl) (x := List.replicate n 0) ⟨ha.1, rfl⟩ (by simpa using hbx))
      fun _ o => ⟨o.env, by
        rw [o.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (aux_tFrame L)
          (by decide), ha.2]⟩
  have r₀ := rel_wp (rel_taint (P := fun s₁ s₂ => J0In Ctx St W SP H₁ Np n s₁ ∧ J0In Ctx St W SP H₂ Np n s₂)
      [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [h.1.r12, h.2.r12]
        · rw [h.1.rbp, h.2.rbp]
        · rw [h.1.env.r13, h.2.env.r13]
        · rw [h.1.env.r14, h.2.env.r14]
        · rw [h.1.env.r15, h.2.env.r15]
        · rw [h.1.env.rsp, h.2.env.rsp]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => j0hashA_ok h) (fun s h => j0hashA_ok h)
  let PA : State → State → Prop := fun s₁ s₂ => True ∧
    ((∃ H', AbsIn Ctx St W SP 0 H' [] Np n s₁) ∧ AuxN Ctx St W SP n s₁) ∧
    ((∃ H', AbsIn Ctx St W SP 0 H' [] Np n s₂) ∧ AuxN Ctx St W SP n s₂)
  have a₁ : RelCT isa PA (absorb v.callees 0) fun _ _ => True :=
    (RelCT.exists_ fun H₁' => RelCT.exists_ fun H₂' =>
      absorb_rel v L (.inl rfl) (H₁ := H₁') (H₂ := H₂') (x₁ := []) (x₂ := []) (D := Np) (n := n) rfl).mono
      (fun s₁ s₂ (h : PA s₁ s₂) => by
        obtain ⟨_, ⟨⟨H₁', h₁⟩, _⟩, ⟨⟨H₂', h₂⟩, _⟩⟩ := h; exact ⟨H₁', H₂', h₁, h₂⟩) fun _ _ h => h
  have r₁ := rel_wp a₁ (fun _ _ h => h.2) hA hA
  have r₂ := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ AuxN Ctx St W SP n s₁ ∧ AuxN Ctx St W SP n s₂)
      (c := .block [.mov .rbx (.mem (at_ .r15 auxO)), .alu .and .rbx (imm 15)])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1.1, h.2.2.1, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => auxLoad_ok h hlt) (fun s h => auxLoad_ok h hlt)
  have r₃ := rel_wp ((flush_rel v L (yo := 0) (.inl rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (AuxN Ctx St W SP n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16)) ∧
      (AuxN Ctx St W SP n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (n % 16)))
      (fun _ _ h => ⟨h.2.1.1.1, h.2.2.1.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hF hF
  have r₄ := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ AuxN Ctx St W SP n s₁ ∧ AuxN Ctx St W SP n s₂)
      (c := .block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1.1, h.2.2.1, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => auxLens_ok h) (fun s h => auxLens_ok h)
  have r₅ := (lens_rel v L (yo := 0) (.inl rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n) ∧
      (Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 0 ∧ s₂.gpr .rbp = BitVec.ofNat 64 n))
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) fun _ _ h => h
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ r₅))))

/-- `j0`, for nonces at the same address, of the same length. -/
theorem j0_rel {H₁ H₂ : Block} {Np : Addr} {n : Nat} :
    RelCT isa (fun s₁ s₂ => J0In Ctx St W SP H₁ Np n s₁ ∧ J0In Ctx St W SP H₂ Np n s₂) (j0 v.callees)
      fun _ _ => True := by
  have hag : ∀ s₁ s₂, J0In Ctx St W SP H₁ Np n s₁ ∧ J0In Ctx St W SP H₂ Np n s₂ →
      ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := fun _ _ h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  have hC : ∀ {H : Block} (s : State), J0In Ctx St W SP H Np n s →
      WP isa (.block [.alu .cmp .rbp (imm 12)]) s (fun s₁ => J0In Ctx St W SP H Np n s₁ ∧
        s₁.zf = some (decide (n = 12))) := fun s h => by
    have hlt := h.data.lt
    obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .rbp (imm 12)] s = some s₁ ∧
        s₁.zf = some (decide (n = 12)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [], ?_, by rfl, by rfl, by rfl, by rfl⟩
      rw [zf_arithFlags, h.rbp]
      exact congrArg some (sub_beq hlt (by decide))
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hm₁]; exact h.hH,
      by rw [hg₁]; exact h.r12, by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁⟩, hzf⟩
  have c := rel_wp (rel_regs [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hC s h) (fun s h => hC s h)
  let P₀ : State → State → Prop := fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (J0In Ctx St W SP H₁ Np n s₁ ∧ s₁.zf = some (decide (n = 12))) ∧
      (J0In Ctx St W SP H₂ Np n s₂ ∧ s₂.zf = some (decide (n = 12)))
  refine RelCT.seq c (RelCT.seq (R := fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂)
    (rel_ite_e (P := P₀) (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_) ?_)
  · let P₁ : State → State → Prop := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (J0In Ctx St W SP H₁ Np n s₁ ∧ s₁.zf = some (decide (n = 12))) ∧
      (J0In Ctx St W SP H₂ Np n s₂ ∧ s₂.zf = some (decide (n = 12)))) ∧ s₁.zf = some true
    have ht : RelCT isa P₁ (.block j012) fun _ _ => True :=
      rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩)
        ⟨_, by taint_decide⟩
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.env, h.1.2.2.1.env⟩) ht).mono (fun _ _ h => h)
      fun _ _ h => h.2
  · by_cases h12 : n = 12
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [h12] at this
    let P₂ : State → State → Prop := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (J0In Ctx St W SP H₁ Np n s₁ ∧ s₁.zf = some (decide (n = 12))) ∧
      (J0In Ctx St W SP H₂ Np n s₂ ∧ s₂.zf = some (decide (n = 12)))) ∧ s₁.zf = some false
    have hj : RelCT isa P₂ (j0hash v.callees) fun _ _ => True :=
      (j0hash_rel v L).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
    exact (rel_wp hj (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (G₁ := Env Ctx St W SP) (G₂ := Env Ctx St W SP)
      (fun s h => WP.mono (j0hash_ok v L h h12) fun _ m => m.env)
      (fun s h => WP.mono (j0hash_ok v L h h12) fun _ m => m.env)).mono (fun _ _ h => h) fun _ _ h => h.2
  · exact rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩

end

end VG.Proof.AesGcm.X86_64
