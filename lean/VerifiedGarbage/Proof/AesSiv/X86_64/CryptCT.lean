import VerifiedGarbage.Proof.AesSiv.X86_64.Open

/-!
# AES-SIV on x86-64: `seal` and `open` are constant time

Both are put together from pieces: the save (and `open`'s counter), proved
by the taint analysis from the public arguments; `finish` and CTR, from the
registers that hold the arguments (`finish_rel`, `ctr_rel'`), with what
correctness says about the slots of the data and the counter; and the rest,
by the taint analysis from those registers. `open` compares the IVs and
masks the data without a branch, so nothing it does depends on the result.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The registers, and the data pointer and length in their slots. -/
structure SPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem cryptPre_spre (h : Env s₀ C D P W R L) (ha : ArgRegs s₀ C D P W R L) :
    WP isa (.block Impl.AesSiv.X86_64.cryptPre) s₀ (SPre s₀ C D P W R L) := by
  obtain ⟨s₁, run₁, hr₁, m₁⟩ := cryptPre_ok h ha
  exact WP.of_runBlock ⟨s₁, run₁, hr₁, by rw [m₁, cryptMem_data], by rw [m₁, cryptMem_len]⟩

theorem finish_spre (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s : State} (hs : SPre s₀ C D P W R L s) :
    WP isa (finish v.callee v.suffix 0) s (SPre s₀ C D P W R L) := by
  refine WP.mono (finish_wp v h hs.regs (Or.inl rfl)) fun t ht => ⟨ht.regs, ?_, ?_⟩
  · rw [ht.frame.readW (Region.contains_self _ _) (fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d208]
  · rw [ht.frame.readW (Region.contains_self _ _) (fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d216]

theorem counter_ctrPre (h : Env s₀ C D P W R L) {s : State} (hs : SPre s₀ C D P W R L s) :
    WP isa (.block (counter 0)) s (CtrPre s₀ C D P W R L) := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := counter_ok h hs.regs.r15 hs.regs.rd hs.regs.wr
  have fc : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, hs.regs.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁, ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃⟩, ?_, ?_⟩
  · rw [fc.readW (Region.contains_self _ _) (cnt_dis (by decide) (by decide)) (by decide), hs.d208]
  · rw [fc.readW (Region.contains_self _ _) (cnt_dis (by decide) (by decide)) (by decide), hs.d216]

/-- The arguments of `seal` and `open` in both runs, by name. -/
structure Both (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) : Prop where
  h : Env s₀ C D P W R L
  h' : Env s₀' C D P W R L
  ha : ArgRegs s₀ C D P W R L
  ha' : ArgRegs s₀' C D P W R L
  cp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩
  pw : (⟨P, L⟩ : Region) ∈ s₀.wr
  pw' : (⟨P, L⟩ : Region) ∈ s₀'.wr

theorem Both.of {s₀ s₀' : State} (h0 : cryptPre s₀) (h0' : cryptPre s₀') (hq : cryptPub s₀ s₀') :
    Both s₀ s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat (s₀.gpr .r8).toNat := by
  obtain ⟨_, q2, q3, q4, q5, q6, q7⟩ := hq
  refine ⟨Env.ofCrypt h0, ?_, ArgRegs.ofCrypt h0, ?_, cryptPre_cp h0, cryptPre_pw h0, ?_⟩
  · rw [q2, q3, q4, q5, q6, q7]; exact Env.ofCrypt h0'
  · rw [q2, q3, q4, q5, q6, q7]; exact ArgRegs.ofCrypt h0'
  · rw [q5, q6]; exact cryptPre_pw h0'

theorem args_agree {s₀ s₀' : State} (hq : cryptPub s₀ s₀') :
    taint.Agree (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) s₀ s₀' := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem seal_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : sealX86_64.pre s₀) (h0' : sealX86_64.pre s₀')
    (hq : sealX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («seal» v.callee v.suffix) fun _ _ => True := by
  have hb := Both.of h0 h0' hq
  have q1 : s₀.gpr .rsp = s₀'.gpr .rsp := hq.1
  generalize s₀.gpr .rdi = C at hb
  generalize s₀.gpr .rdx = D at hb
  generalize s₀.gpr .rcx = P at hb
  generalize s₀.gpr .r9 = W at hb
  generalize (s₀.gpr .rsi).toNat = R at hb
  generalize (s₀.gpr .r8).toNat = L at hb
  obtain ⟨h, h', ha, ha', hcp, hPw, hPw'⟩ := hb
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block Impl.AesSiv.X86_64.cryptPre) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block restore) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact args_agree hq) hA).wp
    (F₁ := SPre s₀ C D P W R L) (F₂ := SPre s₀' C D P W R L) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨cryptPre_spre h ha, cryptPre_spre h' ha'⟩
  have f := ((finish_rel v h h' q1 (Or.inl rfl)).mono (P' := fun a b => SPre s₀ C D P W R L a ∧
      SPre s₀' C D P W R L b) (fun _ _ p => ⟨p.1.regs, p.2.regs⟩) fun _ _ p => p).wp
    (F₁ := SPre s₀ C D P W R L) (F₂ := SPre s₀' C D P W R L) fun a b hab =>
      ⟨finish_spre v h hab.1, finish_spre v h' hab.2⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b) _
    (fun a b hab => regs_agree q1 hab.1.regs hab.2.regs) hB).wp
    (F₁ := CtrPre s₀ C D P W R L) (F₂ := CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨counter_ctrPre h hab.1, counter_ctrPre h' hab.2⟩
  have r := RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hC
  exact (a.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((f.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((c.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((ctr_rel' v h h' q1 hcp hPw hPw').seq r)))

theorem seal_ct (v : Ctr32Impl) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : openX86_64.pre s₀) (h0' : openX86_64.pre s₀')
    (hq : openX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («open» v.callee v.suffix) fun _ _ => True := by
  have hb := Both.of h0 h0' hq
  have q1 : s₀.gpr .rsp = s₀'.gpr .rsp := hq.1
  generalize s₀.gpr .rdi = C at hb
  generalize s₀.gpr .rdx = D at hb
  generalize s₀.gpr .rcx = P at hb
  generalize s₀.gpr .r9 = W at hb
  generalize (s₀.gpr .rsi).toNat = R at hb
  generalize (s₀.gpr .r8).toNat = L at hb
  obtain ⟨h, h', ha, ha', hcp, hPw, hPw'⟩ := hb
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (Impl.AesSiv.X86_64.cryptPre ++ counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq (.block Impl.AesSiv.X86_64.compare)
        (.seq maskData (.block ([.mov .rax (.mem (at_ .r15 dbOff))] ++ restore)))) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact args_agree hq) hA).wp
    (F₁ := CtrPre s₀ C D P W R L) (F₂ := CtrPre s₀' C D P W R L) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨WP.block_append (WP.mono (cryptPre_spre h ha) fun _ hs => counter_ctrPre h hs),
        WP.block_append (WP.mono (cryptPre_spre h' ha') fun _ hs => counter_ctrPre h' hs)⟩
  have t := RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _
    (fun a b hab => regs_agree q1 hab.1 hab.2) hB
  exact (a.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((ctr_rel' v h h' q1 hcp hPw hPw').seq
    ((finish_rel v h h' q1 (Or.inr rfl)).seq t))

theorem open_ct (v : Ctr32Impl) :
    ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.X86_64
