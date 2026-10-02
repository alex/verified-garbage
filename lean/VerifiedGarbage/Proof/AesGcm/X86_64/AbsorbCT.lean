import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb

/-!
# AES-GCM on x86-64: `absorb` in two runs

Untrusted: everything here is checked by Lean. Two runs of `absorb yo` that
absorb data at the same address, of the same length, after the same number
of bytes modulo 16, leak the same: the code between the calls of `vg_ghash`
is checked by the taint analysis, from the registers `AbsIn` and `AbsMid`
fix, and each call has the same arguments in both runs.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)

/-- The registers `absorb` and `crypt` start from. -/
def absRegs : List Reg := [.r12, .rbp, .rbx, .r13, .r14, .r15, .rsp]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The buffer filled. -/
theorem head_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat}
    (hx : x₁.length % 16 = x₂.length % 16) :
    RelCT isa (fun s₁ s₂ => AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ AbsIn Ctx St W SP yo H₂ x₂ D n s₂)
      (absorbHead v.callees yo) fun _ _ => True := by
  refine rel_reassoc4 (RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => ⟨h.1.env, h.2.env⟩) (rel_regs absRegs [] true (fun s₁ s₂ h r hr => ?_) ⟨_, by taint_decide⟩)) ?_)
  · simp only [absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hx]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ (RelCT.block_nil fun _ _ _ => trivial)
  refine (ghash1_rel v L hyo .r14 32 (.inl rfl) (by decide) (P := St + BitVec.ofNat 64 32)
    (L.st_st (.inl (by omega)) (by omega) (by decide)) (L.st_w (by decide) (.inr ⟨by decide, by decide⟩))
    (L.stk_st (by decide)) (gh1Check_r14_32 hyo) (F₁ := Env Ctx St W SP) (F₂ := Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) fun _ _ h => h
  have he : Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r14], covers_left (he.perm.stC (by decide))⟩

omit L hyo in
/-- `AbsMid`'s registers agree in two runs with the same `j`. -/
theorem AbsMid.agree {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁) (h₂ : AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂) :
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

/-- The whole blocks. -/
theorem whole_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧ AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂)
      (absorbWhole v.callees yo) fun _ _ => True := by
  -- What the split leaves in each run.
  let Sp : State → Prop := fun s₁ => Env Ctx St W SP s₁ ∧ DataOk St W SP s₁ D n ∧ j ≤ n ∧
    s₁.gpr .rdx = D + BitVec.ofNat 64 j ∧ s₁.gpr .rcx = BitVec.ofNat 64 ((n - j) / 16)
  have hS : ∀ {H : Block} {x : List Byte} {m : Mem} (s : State), AbsMid Ctx St W SP yo H x D n m j s →
      WP isa (.block (splitWhole .rdx .rcx ++ [.alu .test .rcx (.reg .rcx)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hdx, hcx, -, -, -, hg₁, -, hrd₁, hwr₁⟩ := wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) h.data.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le, hdx, hcx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧
      AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => AbsMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The call's arguments.
  let Ar : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    GhCall s₂ (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (D + BitVec.ofNat 64 j)
      (W + BitVec.ofNat 64 512) ((n - j) / 16)
  have hA : ∀ s, Sp s → WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO)) s Ar :=
    fun s ⟨he, hd, hj, hdx, hcx⟩ => by
      have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
      have hdj := (hd.drop hj).take (k := 16 * ((n - j) / 16)) (by omega)
      obtain ⟨s₂, run₂, hdi, hsi, h8, hg₂, -, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
          (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO) s = some s₂ ∧
          s₂.gpr .rdi = Ctx + BitVec.ofNat 64 240 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 yo ∧
          s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
          (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
          s₂.wr = s.wr := by
        rcases hyo with rfl | rfl
        all_goals
          refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [gpr_setReg, h13]
          · simp [gpr_setReg, h14]
          · simp [gpr_setReg, h15]
          · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
          all_goals rfl
      have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
      refine WP.of_runBlock ⟨s₂, run₂, he₂, ghCall_of L hyo he₂ hdi hsi
        (by rw [hg₂ _ (by decide) (by decide) (by decide), hdx])
        (by rw [hg₂ _ (by decide) (by decide) (by decide), hcx]) h8 (by have := hdj.lt; omega)
        (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
        (by rw [hrd₂, hwr₂]; exact hdj.rd)⟩
  have hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp])
      (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO)) hc).isSome = true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => ((True ∧ Sp s₁ ∧ Sp s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
      have e₁ := h.1.2.1.1; have e₂ := h.1.2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15]
      · rw [e₁.rsp, e₂.rsp]) hc)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hA hA
  refine (RelCT.seq b (gh_rel v.gh fun s₁ s₂ h => ⟨_, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)).mono
    (fun _ _ h => ⟨⟨trivial, h.1.2.1, h.1.2.2⟩, h.2⟩) fun _ _ h => h
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

omit L hyo in
/-- The last bytes, buffered. -/
theorem tail_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧ AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂)
      absorbTail fun _ _ => True :=
  rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h => AbsMid.agree h.1 h.2) ⟨_, by taint_decide⟩

/-- `absorb yo`, for data at the same address, of the same length, after
the same number of bytes modulo 16. -/
theorem absorb_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat}
    (hx : x₁.length % 16 = x₂.length % 16) :
    RelCT isa (fun s₁ s₂ => AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ AbsIn Ctx St W SP yo H₂ x₂ D n s₂)
      (absorb v.callees yo) fun _ _ => True := by
  have hag : ∀ s₁ s₂, AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ AbsIn Ctx St W SP yo H₂ x₂ D n s₂ →
      ∀ r ∈ absRegs, s₁.gpr r = s₂.gpr r := fun s₁ s₂ h r hr => by
    simp only [absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hx]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  -- `test r, r` keeps everything but the flags.
  have hT : ∀ {r : Reg} {H : Block} {x : List Byte} {k : Nat} (s : State), AbsIn Ctx St W SP yo H x D n s →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => AbsIn Ctx St W SP yo H x D n s' ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, h.keep hg₁ hm₁ hrd₁ hwr₁, hz⟩
  have t₁ := rel_wp (rel_regs (P := fun s₁ s₂ => AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧
      AbsIn Ctx St W SP yo H₂ x₂ D n s₂) absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.lt)
  refine RelCT.seq t₁ (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  have hr₁ := Nat.mod_lt x₁.length (show 16 > 0 by decide)
  have hr₂ := Nat.mod_lt x₂.length (show 16 > 0 by decide)
  have t₂ := rel_wp (rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ s₁.zf = some (decide (n = 0))) ∧
      AbsIn Ctx St W SP yo H₂ x₂ D n s₂ ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega))
  -- What each run reaches after filling the buffer: the same `j`.
  have i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ s₁.zf = some (decide (x₁.length % 16 = 0))) ∧
        AbsIn Ctx St W SP yo H₂ x₂ D n s₂ ∧ s₂.zf = some (decide (x₂.length % 16 = 0)))
      (.ite .e (.block []) (absorbHead v.callees yo)) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        AbsMid Ctx St W SP yo H₁ x₁ D n m₁ j s₁ ∧ AbsMid Ctx St W SP yo H₂ x₂ D n m₂ j s₂ := by
    refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : x₁.length % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, ?_, ?_⟩
      · have h₂ := h.1.2.1.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
          fun ha => by simpa [bytesAt] using ha, .inr (by omega), Frame.refl _ _⟩
      · have h₂ := h.1.2.2.1
        exact ⟨h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
          fun ha => by simpa [bytesAt] using ha, .inr (by omega), Frame.refl _ _⟩
    · by_cases ho : x₁.length % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (rel_wp ((head_rel v L hyo (H₁ := H₁) (H₂ := H₂) (D := D) (n := n) hx).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, AbsMid Ctx St W SP yo H₁ x₁ D n m (min (16 - x₁.length % 16) n) s)
        (G₂ := fun s => ∃ m, AbsMid Ctx St W SP yo H₂ x₂ D n m (min (16 - x₂.length % 16) n) s)
        (fun s h => WP.mono (head_ok v L hyo h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (head_ok v L hyo h hn0 (by omega)) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
        fun _ _ ⟨_, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ => ⟨_, m₁, m₂, h₁, by rw [hx]; exact h₂⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  refine RelCT.seq t₂ (RelCT.seq i₂ ?_)
  -- The whole blocks and the rest, from the same `j`.
  refine RelCT.exists_ fun j => RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := rel_wp (whole_rel v L hyo (H₁ := H₁) (H₂ := H₂) (x₁ := x₁) (x₂ := x₂) (D := D) (n := n) (m₁ := m₁)
      (m₂ := m₂) (j := j)) (fun _ _ h => h)
    (fun s h => whole_ok v L hyo h (h.data_eq hyo)) (fun s h => whole_ok v L hyo h (h.data_eq hyo))
  exact RelCT.seq hw (tail_rel.mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.AesGcm.X86_64
