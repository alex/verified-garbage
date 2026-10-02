import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code between the calls
is checked by the taint analysis from the public arguments; the calls of
`vg_aes_expand_key` and `vg_aes_ctr32` have the same arguments in both runs,
which correctness gives (`initA_ok`, `initC_ok`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- After the entry: the call of `vg_aes_expand_key`, and what stays for the rest. -/
structure InitA (K Ctx W SP : Addr) (L R : Nat) (rd wr : List Region) (s : State) : Prop where
  call : KeyCall s K Ctx (W + BitVec.ofNat 64 512) L
  r15 : s.gpr .r15 = W
  r13 : s.gpr .r13 = Ctx
  rbx : s.gpr .rbx = BitVec.ofNat 64 R
  rsp : s.gpr .rsp = SP
  rd : s.rd = rd
  wr : s.wr = wr

theorem initA_ok {s : State} (hp : Proof.AesGcm.initX86_64.pre s) :
    WP isa (.block (save .rcx ++ ([.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi),
      .shift .shr .rbx 2, .alu .add .rbx (imm 6)] : List Instr) ++ ptr .rcx .r15 scrO)) s
      (InitA (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsp) (s.gpr .rsi).toNat
        (Spec.Aes.rounds ((s.gpr .rsi).toNat / 4)) s.rd s.wr) := by
  simp only [Proof.AesGcm.initX86_64, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, -, -, k_k, k_c, k_s, -, -, hL⟩ := hp
  generalize hK : s.gpr .rdi = K at *
  generalize hLn : (s.gpr .rsi).toNat = L at *
  generalize hCtx : s.gpr .rdx = Ctx at *
  generalize hW : s.gpr .rcx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := save_ok s .rcx hW pW
  have hsi : s.gpr .rsi = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hR : BitVec.ofNat 64 L >>> 2 + 6#64 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
    rcases hL with rfl | rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h15, h13, hbx, hcx, hdi, hsi₂, hdx, hsp, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi), .shift .shr .rbx 2,
        .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO) s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rbx = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 512 ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 L ∧
      s₂.gpr .rdx = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, gpr_setFlags, rd_setFlags, wr_setFlags, hg₁, hW, hCtx, hK, hsi, hSP, hR]
  rw [List.append_assoc]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_, h15, h13, hbx, hsp,
    hrd₂.trans hrd₁, hwr₂.trans hwr₁⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := covers_off pW (by decide) (by decide)
  refine ⟨hdi, hsi₂, hdx, hcx, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
    d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
      (Lay.wSub (by decide)), by rw [hsp]; exact k_k, by rw [hsp]; exact k_c.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact k_s.sub_right (Lay.wSub (by decide)), ?_, ?_⟩
  · rw [rd₂, wr₂, hrd]
    exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (covers_left (covers_cons (covers_prefix pC (by decide)) pS))
  · rw [wr₂]; exact covers_cons (covers_prefix pC (by decide)) pS

/-- After the call of `vg_aes_expand_key`: the call of `vg_aes_ctr32`. -/
theorem initC_ok {s : State} (hp : Proof.AesGcm.initX86_64.pre s) {R : Nat} (hR' : R = 10 ∨ R = 12 ∨ R = 14)
    {s₃ : State} (h15 : s₃.gpr .r15 = s.gpr .rcx) (h13 : s₃.gpr .r13 = s.gpr .rdx)
    (hbx : s₃.gpr .rbx = BitVec.ofNat 64 R) (hsp : s₃.gpr .rsp = s.gpr .rsp) (hwr : s₃.wr = s.wr) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .rbx)] : List Instr) ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ ([.mov32 .r8 (imm 1)] : List Instr) ++
        ptr .r9 .r15 scrO)) s₃ fun s₄ =>
      CtrCall s₄ (s.gpr .rdx) (s.gpr .rcx + BitVec.ofNat 64 96) (s.gpr .rdx + BitVec.ofNat 64 240)
        (s.gpr .rcx + BitVec.ofNat 64 512) R 1 ∧ s₄.gpr .r15 = s.gpr .rcx ∧ s₄.gpr .rsp = s.gpr .rsp := by
  simp only [Proof.AesGcm.initX86_64, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨-, hwr', -, -, d_cs, -, -, -, k_c, k_s, wc, -, -⟩ := hp
  generalize hCtx : s.gpr .rdx = Ctx at *
  generalize hW : s.gpr .rcx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr']; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr']; exact covers_of_mem (List.mem_cons_self ..)
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .rbx)] ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) s₃ = some s₄ ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = BitVec.ofNat 64 R ∧ s₄.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .rcx = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₄.gpr .r9 = W + BitVec.ofNat 64 512 ∧ (∀ r ∈ calleeSaved, s₄.gpr r = s₃.gpr r) ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by xrun [h15, h13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hbx]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [hg₄ .r15 (by decide), h15], by rw [hg₄ .rsp (by decide), hsp]⟩
  have g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), hsp]
  have wr₄ : s₄.wr = s.wr := hwr₄.trans hwr
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hR', ?_, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
  · simpa using dCW 0 240 (by decide) 96 16 (by decide)
  · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact dCW 240 16 (by decide) 512 2048 (by decide)
  · rw [g4sp]; exact k_c.sub_right (Region.sub_prefix (by decide))
  · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
  · rw [g4sp]; exact k_c.sub_right (Offset.sub_base _ (by decide))
  · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide))) (covers_cons
      (covers_left (covers_off pC' (by decide) (by decide))) (covers_left (covers_off pW' (by decide) (by decide)))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_cons (covers_off pC' (by decide) (by decide))
      (covers_off pW' (by decide) (by decide)))

theorem init_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.initX86_64.pre s₀)
    (hp' : Proof.AesGcm.initX86_64.pre s₀') (hq : Proof.AesGcm.initX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (init v.callees) fun _ _ => True := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅⟩ := hq
  have hL : (s₀.gpr .rsi).toNat = 16 ∨ (s₀.gpr .rsi).toNat = 24 ∨ (s₀.gpr .rsi).toNat = 32 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  generalize hRd : Spec.Aes.rounds ((s₀.gpr .rsi).toNat / 4) = R
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases hL with h | h | h <;> rw [h] <;> decide
  let A₁ := InitA (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat R s₀.rd s₀.wr
  let A₂ := InitA (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat R s₀'.rd s₀'.wr
  have hA₂ := initA_ok hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, hRd] at hA₂
  have hA₁ := initA_ok hp
  rw [hRd] at hA₁
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (c := .block (save .rcx ++ [.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi),
        .shift .shr .rbx 2, .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO)) [.rdi, .rsi, .rdx, .rcx, .rsp]
      (fun _ _ h r hr => by
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (G₁ := A₁) (G₂ := A₂) (fun s h => by subst h; exact hA₁) (fun s h => by subst h; exact hA₂)
  -- After the call of `vg_aes_expand_key`.
  let K₁ : State → Prop := fun s₃ => s₃.gpr .r15 = s₀.gpr .rcx ∧ s₃.gpr .r13 = s₀.gpr .rdx ∧
    s₃.gpr .rbx = BitVec.ofNat 64 R ∧ s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.rd = s₀.rd ∧ s₃.wr = s₀.wr
  let K₂ : State → Prop := fun s₃ => s₃.gpr .r15 = s₀.gpr .rcx ∧ s₃.gpr .r13 = s₀.gpr .rdx ∧
    s₃.gpr .rbx = BitVec.ofNat 64 R ∧ s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.rd = s₀'.rd ∧ s₃.wr = s₀'.wr
  have hK : ∀ {rd wr : List Region} (s : State),
      InitA (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat R rd wr s →
      WP isa (.call v.key.fn.name v.key.fn.code) s fun s₃ => s₃.gpr .r15 = s₀.gpr .rcx ∧ s₃.gpr .r13 = s₀.gpr .rdx ∧
        s₃.gpr .rbx = BitVec.ofNat 64 R ∧ s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.rd = rd ∧ s₃.wr = wr := fun s h =>
    WP.mono (key_call v.key h.call) fun _ g => ⟨by rw [g.saved .r15 (by decide), h.r15],
      by rw [g.saved .r13 (by decide), h.r13], by rw [g.saved .rbx (by decide), h.rbx],
      by rw [g.saved .rsp (by decide), h.rsp], by rw [g.rd, h.rd], by rw [g.wr, h.wr]⟩
  have k := rel_wp (key_rel v.key (P := fun s₁ s₂ => True ∧ A₁ s₁ ∧ A₂ s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.2.1.call, h.2.2.call, by rw [h.2.1.rsp, h.2.2.rsp]⟩)
    (fun _ _ h => h.2) (G₁ := K₁) (G₂ := K₂) (fun s h => hK s h) (fun s h => hK s h)
  -- The call of `vg_aes_ctr32`.
  let C₁ : State → Prop := fun s₄ => CtrCall s₄ (s₀.gpr .rdx) (s₀.gpr .rcx + BitVec.ofNat 64 96)
    (s₀.gpr .rdx + BitVec.ofNat 64 240) (s₀.gpr .rcx + BitVec.ofNat 64 512) R 1 ∧ s₄.gpr .r15 = s₀.gpr .rcx ∧
    s₄.gpr .rsp = s₀.gpr .rsp
  have hC₁ : ∀ s, K₁ s → WP isa _ s C₁ := fun s h => initC_ok hp hR' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2
  have hC₂ : ∀ s, K₂ s → WP isa _ s C₁ := fun s h => by
    have := initC_ok hp' hR' (s₃ := s) (by rw [h.1, q₄]) (by rw [h.2.1, q₃]) h.2.2.1 (by rw [h.2.2.2.1, q₅])
      h.2.2.2.2.2
    rw [← q₃, ← q₄, ← q₅] at this
    exact this
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ K₁ s₁ ∧ K₂ s₂) [.r13, .r15, .rbx, .rsp]
      (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.1, h.2.2.1]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1]
        · rw [h.2.1.2.2.2.1, h.2.2.2.2.2.1]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hC₁ hC₂
  have hE : ∀ s, C₁ s → WP isa (.call v.ctr.callee.name v.ctr.callee.code) s fun s' =>
      s'.gpr .r15 = s₀.gpr .rcx ∧ s'.gpr .rsp = s₀.gpr .rsp := fun s h =>
    WP.mono (ctr_call v.ctr h.1) fun _ g => ⟨by rw [g.saved .r15 (by decide), h.2.1],
      by rw [g.saved .rsp (by decide), h.2.2]⟩
  have d := rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧ C₁ s₁ ∧ C₁ s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.2, h.2.2.2.2]⟩) (fun _ _ h => h.2) hE hE
  have e := rel_taint (P := fun s₁ s₂ => True ∧ (s₁.gpr .r15 = s₀.gpr .rcx ∧ s₁.gpr .rsp = s₀.gpr .rsp) ∧
      (s₂.gpr .r15 = s₀.gpr .rcx ∧ s₂.gpr .rsp = s₀.gpr .rsp)) (c := .block restore) [.r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.1, h.2.2.1]
      · rw [h.2.1.2, h.2.2.2]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq k (RelCT.seq c (RelCT.seq d e)))

theorem init_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.initX86_64.pre Proof.AesGcm.initX86_64.pub (init v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => init_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
