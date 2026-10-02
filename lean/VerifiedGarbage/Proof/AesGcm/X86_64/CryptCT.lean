import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT

/-!
# AES-GCM on x86-64: `crypt` in two runs

Untrusted: everything here is checked by Lean. Two runs of `crypt` over
data at the same address, of the same length, after the same number of
bytes modulo 16, with the same number of rounds, leak the same: the code
between the calls of `vg_aes_ctr32` is checked by the taint analysis, from
the registers `CrIn` and `CrMid` fix, and each call has the same arguments
in both runs.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem CrMid.agree {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁) (h₂ : CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) :
    ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r12, h₂.r12]
  · rw [h₁.rbp, h₂.rbp]
  · rw [h₁.env.r13, h₂.env.r13]
  · rw [h₁.env.r14, h₂.env.r14]
  · rw [h₁.env.r15, h₂.env.r15]
  · rw [h₁.env.rsp, h₂.env.rsp]

/-- Whole blocks. -/
theorem cryptWhole_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂)
      (cryptWhole v.callees) fun _ _ => True := by
  let Sp : State → Prop := fun s₁ => Env Ctx St W SP s₁ ∧ DataW Ctx St W SP s₁ D n ∧ j ≤ n ∧
    RoundsAt s₁.mem W R ∧ s₁.gpr .rcx = D + BitVec.ofNat 64 j ∧ s₁.gpr .r8 = BitVec.ofNat 64 ((n - j) / 16)
  have hS : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP R icb P D n m j s →
      WP isa (.block (splitWhole .rcx .r8 ++ [.alu .test .r8 (.reg .r8)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hcx, h8, -, -, -, hg₁, hm₁, hrd₁, hwr₁⟩ :=
      wholeSplit_ok .rcx .r8 (.inr ⟨rfl, rfl⟩) h.data.ok.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le,
      by rw [hm₁]; exact h.rounds, hcx, h8⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧
      CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  let Ar : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R ((n - j) / 16)
  have hA : ∀ s, Sp s → WP isa (.block ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++
      ptr .rdx .r14 48 ++ ptr .r9 .r15 scrO)) s Ar := fun s ⟨he, hd, hj, hR, hcx, h8⟩ => by
    obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, -, hrd₂, hwr₂⟩ := ctrArgs_ok he hR
    have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    exact WP.of_runBlock ⟨s₂, run₂, he₂, cwCall_of L he₂ (hd.of_eq hrd₂ hwr₂) hj (by omega) hR.2 hdi hsi hdx
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), hcx])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h8]) h9⟩
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => ((True ∧ Sp s₁ ∧ Sp s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1.2.1.1, h.1.2.2.1, fun _ h => by cases h⟩)
    ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hA hA
  refine (RelCT.seq b (ctr_rel v.ctr fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)).mono
    (fun _ _ h => ⟨⟨trivial, h.1.2.1, h.1.2.2⟩, h.2⟩) fun _ _ h => h
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

/-- The arguments of `cryptTail`'s call of `vg_aes_ctr32`. -/
theorem ctTailArgs_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP R icb P D n m₀ j s) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) s fun s₂ =>
      Env Ctx St W SP s₂ ∧
      CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 ∧
      s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j) := by
  have he := h.env
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  have r₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s = some s₂ ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = St + BitVec.ofNat 64 64 ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hR := h.rounds.1
    have hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (St + BitVec.ofNat 64 64) x).writeW
        (St + BitVec.ofNat 64 72) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
      intro m x y
      rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 72) (n := 8) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
        Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 64) (n := 8) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    refine ⟨_, by xrun [h13, h14, h15, w₁, w₂, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hsep, hR]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  refine ⟨he₂, ?_, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    h.r12], by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]⟩
  refine ⟨hdi, hsi, hdx, hcx, h8, h9, h.rounds.2, by have := L.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    L.st_st (.inl (by decide)) (by decide) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact L.stk_w (by decide)
  · refine covers_cons ?_ (covers_cons (covers_left (he₂.perm.stC (by decide))) (covers_cons
      (covers_left (he₂.perm.stC (by decide))) (covers_left (he₂.perm.wC (by decide)))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
  · exact covers_cons (he₂.perm.stC (by decide)) (covers_cons (he₂.perm.stC (by decide))
      (he₂.perm.wC (by decide)))

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂)
      (cryptTail v.callees) fun _ _ => True := by
  have hT : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP R icb P D n m j s →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) s (CrMid Ctx St W SP R icb P D n m j) := fun s h => by
    obtain ⟨s₁, run₁, -, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (by have := h.data.ok.lt; omega)
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.le, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds, fun hc => by rw [hm₁]; exact h.ctr hc,
      fun hc => by rw [hm₁]; exact h.done hc, by rw [hm₁]; exact h.rest, h.whole, by rw [hm₁]; exact h.frame⟩
  have t := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧
      CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)
  refine RelCT.seq t (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The arguments of the call, and what it keeps.
  let G : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 ∧
    s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j)
  let K : State → Prop := fun s₃ => Env Ctx St W SP s₃ ∧
    s₃.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₃.gpr .rbp = BitVec.ofNat 64 (n - j)
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => ((((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => CrMid.agree h.1.2.1 h.1.2.2 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) (G₁ := G) (G₂ := G) (fun s h => ctTailArgs_ok L h)
    (fun s h => ctTailArgs_ok L h)
  have hK : ∀ s, G s → WP isa (.call v.ctr.callee.name v.ctr.callee.code) s K := fun s ⟨he, hc, h12, hbp⟩ =>
    WP.mono (ctr_call v.ctr hc) fun _ g => ⟨he.of_saved g.saved g.rd g.wr,
      by rw [g.saved _ (by decide), h12], by rw [g.saved _ (by decide), hbp]⟩
  have c := rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧ G s₁ ∧ G s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, _, h.2.1.2.1, h.2.2.2.1, by rw [h.2.1.1.rsp, h.2.2.1.rsp]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hK hK
  have d := rel_taint (P := fun s₁ s₂ => True ∧ K s₁ ∧ K s₂)
    (c := .seq (.block ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r14 64 ++ [.mov .rcx (.reg .rbp)])) xorLoop)
    [.r12, .rbp, .r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]
      · rw [h.2.1.1.r13, h.2.2.1.r13]
      · rw [h.2.1.1.r14, h.2.2.1.r14]
      · rw [h.2.1.1.r15, h.2.2.1.r15]
      · rw [h.2.1.1.rsp, h.2.2.1.rsp]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq c d)

/-- `crypt`, over data at the same address, of the same length, after the
same number of bytes modulo 16, with the same number of rounds. -/
theorem crypt_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} (hP : P₁ % 16 = P₂ % 16) :
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP R icb₂ P₂ D n s₂)
      (crypt v.callees) fun _ _ => True := by
  have hag : ∀ s₁ s₂, CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP R icb₂ P₂ D n s₂ →
      ∀ r ∈ absRegs, s₁.gpr r = s₂.gpr r := fun s₁ s₂ h r hr => by
    simp only [absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hP]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  have hT : ∀ {r : Reg} {icb : Block} {P : Nat} {k : Nat} (s : State), CrIn Ctx St W SP R icb P D n s →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => CrIn Ctx St W SP R icb P D n s' ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds⟩, hz⟩
  have t₁ := rel_wp (rel_regs (P := fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧
      CrIn Ctx St W SP R icb₂ P₂ D n s₂) absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.ok.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.ok.lt)
  refine RelCT.seq t₁ (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  have hr₁ := Nat.mod_lt P₁ (show 16 > 0 by decide)
  have hr₂ := Nat.mod_lt P₂ (show 16 > 0 by decide)
  have t₂ := rel_wp (rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (n = 0))) ∧
      CrIn Ctx St W SP R icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega))
  have i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (P₁ % 16 = 0))) ∧
        CrIn Ctx St W SP R icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (P₂ % 16 = 0)))
      (.ite .e (.block []) cryptHead) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂ := by
    refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : P₁ % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, ?_, ?_⟩
      · have h₂ := h.1.2.1.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
          h₂.rounds, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by simp,
          .inr (by omega), Frame.refl _ _⟩
      · have h₂ := h.1.2.2.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
          h₂.rounds, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by simp,
          .inr (by omega), Frame.refl _ _⟩
    · by_cases ho : P₁ % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (rel_wp ((rel_taint absRegs (P := fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧
          CrIn Ctx St W SP R icb₂ P₂ D n s₂) hag ⟨_, by taint_decide⟩).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, CrMid Ctx St W SP R icb₁ P₁ D n m (min (16 - P₁ % 16) n) s)
        (G₂ := fun s => ∃ m, CrMid Ctx St W SP R icb₂ P₂ D n m (min (16 - P₂ % 16) n) s)
        (fun s h => WP.mono (cryptHead_ok h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (cryptHead_ok h hn0 (by omega)) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
        fun _ _ ⟨_, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ => ⟨_, m₁, m₂, h₁, by rw [hP]; exact h₂⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  refine RelCT.seq t₂ (RelCT.seq i₂ ?_)
  refine RelCT.exists_ fun j => RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := rel_wp (cryptWhole_rel v L (R := R) (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := j)) (fun _ _ h => h)
    (fun s h => cryptWhole_ok v L h (h.ciph L)) (fun s h => cryptWhole_ok v L h (h.ciph L))
  exact RelCT.seq hw ((cryptTail_rel v L).mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.AesGcm.X86_64
