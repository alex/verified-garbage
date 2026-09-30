import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, constant time but for the seeds

Untrusted: everything here is checked by Lean. Two runs whose seeds (the
declared leak) and pointers agree leak the same. The code but for the loops
of `parse` and their fallbacks is proven by the taint analysis, from the
pointers; the loops as `vg_mlkem_sample_ntt`'s (`body_ct`), since both runs
read the same XOF output; the fallbacks take the same branch, and call
`vg_mlkem_sample_ntt` on the same seed.
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Two runs related by `I`, from entry states that agree on what is public. -/
abbrev R4 (I : State → State → Prop) : State → State → Prop := Rel2 sample4K.pre sample4K.pub I

section
variable {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂)
include hq

theorem pub_scr : scr σ₁ = scr σ₂ := hq.2.2.1
theorem pub_aP : aP σ₁ = aP σ₂ := hq.2.1
theorem pub_sd : sd σ₁ = sd σ₂ := hq.1
theorem pub_sp : σ₁.gpr .rsp = σ₂.gpr .rsp := hq.2.2.2.1

theorem pub_B {k : Nat} (hk : k < 4) : B σ₁ k = B σ₂ k := by
  have e := hq.2.2.2.2
  simp only [B, seed4, sd, bytesAt] at e ⊢
  rw [← hq.1] at e ⊢
  apply List.ext_getElem (by simp)
  intro i h₁ _
  have := congrArg (fun L => L[34 * k + i]?) e
  simp only [List.getElem?_map, List.getElem?_range (show 34 * k + i < 136 by simp at h₁; omega),
    Option.map_some, Option.some.injEq] at this
  simp only [List.getElem_map, List.getElem_range, Offset.add_add]
  exact this

end

theorem start_ct : RelCT isa (R4 fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) (R4 fun σ s => SqInv σ 0 s) :=
  relInv (fun σ s hp h => by subst h; exact start_ok (pre_of hp))
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))


theorem env_rbx {σ₁ σ₂ s₁ s₂ : State} (hq : sample4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx := by rw [e₁.rbx, e₂.rbx, pub_scr hq]

/-- `squeeze4 n`, given its taint analysis. -/
theorem sq_ct (n : Nat) (hn : n < 3) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (R4 fun σ s => SqInv σ n s) (squeeze4 n) (R4 fun σ s => SqInv σ (n + 1) s) :=
  relInv (fun σ s hp h => sq_ok (pre_of hp) hn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

theorem sq0_ct : RelCT isa (R4 fun σ s => SqInv σ 0 s) (squeeze4 0) (R4 fun σ s => SqInv σ 1 s) :=
  sq_ct 0 (by decide) (by taint_decide)

/-! ## The loops -/

theorem pub_Lt {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {K : Nat} (hK : K < 4) (t : Nat) :
    Lt σ₁ K t = Lt σ₂ K t := by simp only [Lt, pub_B hq hK]

theorem bpre {σ : State} (hp : sample4K.pre σ) {K t : Nat} (hK : K < 4) (ht : t < 168) {s : State}
    (h : LAt σ K t s) : BPre s (poly4 (aP σ) K) (Lt σ K t) := by
  have hp' := pre_of hp
  refine ⟨h.rbp, h.rdi, sampleAfter_length_le (a := []) (by simp) _ t, fun j hj => ?_, h.stored,
    by simpa using lat_regions hp' hK h (j := 0) (by omega), lat_regions hp' hK h (by omega),
    lat_regions hp' hK h (by omega)⟩
  rw [h.pinv.env.wr, hp'.wr]
  refine ⟨aR σ, by simp, ?_⟩
  rw [coeffAddr, poly4, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Two runs at iteration `t` of `parse K`, `n = 168 - t` iterations from the end. -/
def LI (K n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = 168 - t ∧ t < 168 ∧
    LAt σ₁ K t s₁ ∧ LAt σ₂ K t s₂ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (168 - t) ∧
    s₂.gpr .rcx = BitVec.ofNat 64 (168 - t)

theorem li_brel {K n : Nat} (hK : K < 4) {s₁ s₂ : State} (h : LI K n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂, c₁, c₂⟩ := h
  refine ⟨poly4 (aP σ₁) K, Lt σ₁ K t, bpre p₁ hK ht l₁, by rw [pub_aP hq, pub_Lt hq hK]; exact bpre p₂ hK ht l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [c₁, c₂], fun k hk => ?_⟩
  rw [out_byte hK l₁ (by omega), out_byte hK l₂ (by omega), pub_B hq hK]

theorem loop_ct {K : Nat} (hK : K < 4) (n : Nat) :
    RelCT isa (LI K n) (.loop snBody .ne) (R4 fun σ s => LAt σ K 168 s) := by
  refine RelCT.loop (M := isa) (LI K) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, sample4K.pre p.1 ∧ p.2 < 168 ∧
      LAt p.1 K p.2 x → LAt p.1 K (p.2 + 1) x' ∧ x'.gpr .rcx = x.gpr .rcx - 1 ∧ x'.zf = some (x.gpr .rcx - 1 == 0))
    (RelCT.mono body_ct (fun x y h => li_brel hK h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂, _⟩ := h
    exact ⟨WP.all (fun p hp' => lat_step (pre_of hp'.1) hK hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all (fun p hp' => lat_step (pre_of hp'.1) hK hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂, c₁, c₂⟩ f₁ f₂
    obtain ⟨l₁', r₁, z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', r₂, z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    rw [c₁, SampleNtt.zf_last (by decide) ht] at z₁
    rw [c₂, SampleNtt.zf_last (by decide) ht] at z₂
    rw [c₁, ofNat64_pred (by omega) (by omega)] at r₁
    rw [c₂, ofNat64_pred (by omega) (by omega)] at r₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 168 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 168 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨168 - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega, l₁', l₂',
        by rw [r₁]; congr 1, by rw [r₂]; congr 1⟩

/-- The setup of the loop of `parse K`, given its taint analysis. -/
theorem setup_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13])
      (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
        .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
        .mov32 .rcx (.imm 168)]) hc).isSome = true) :
    RelCT isa (R4 fun σ s => PInv σ K s)
      (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
        .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
        .mov32 .rcx (.imm 168)]) (LI K 168) :=
  RelCT.mono (relInv (I' := fun σ s => LAt σ K 0 s ∧ s.gpr .rcx = BitVec.ofNat 64 168)
      (fun σ s _ h => setup_ok hK h)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq h₁.env h₂.env
        · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]) c))
    (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, c₁⟩, ⟨l₂, c₂⟩⟩ =>
      ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by decide, l₁, l₂, c₁, c₂⟩

/-! ## The fallbacks -/

theorem call_ct {K : Nat} (hK : K < 4) : RelCT isa (R4 fun σ s => ArgI σ K s)
    (.call "vg_mlkem_sample_ntt" sampleNTT) (R4 fun σ s => CallI σ K s) :=
  relInv (fun σ s hp h => callK_ok (pre_of hp) hK h) (RelCT.callEx sample_correct sample_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, pub_sp hq]
      refine ⟨_, _, _, _, argK_pre (pre_of p₁) hK h₁, argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt s₁ (n := 34) (by decide) (argK_kS (pre_of p₁) hK h₁),
        ce_bytesAt s₂ (n := 34) (by decide) (argK_kS (pre_of p₂) hK h₂),
        seed_bytes (pre_of p₁) hK h₁.pinv.env.frame, seed_bytes (pre_of p₂) hK h₂.pinv.env.frame, pub_B hq hK]
      simp only [pub_sd hq, pub_aP hq, at', pub_scr hq, hsp, and_self])

/-- The check of `j` and the call, given the taint analysis of the call's arguments. -/
theorem fallback_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R4 fun σ s => LAt σ K 168 s) (fallback K) (R4 fun σ s => PInv σ (K + 1) s) := by
  unfold fallback
  refine RelCT.seq (relInv (I' := fun σ s => MI σ K s) (fun σ s _ h => cmpK_ok h)
    (taintRel [] SampleNtt.nil_regs (by taint_decide))) (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
      show x.cf = y.cf; rw [h₁.cf, h₂.cf, pub_Lt hq hK]) ?_ ?_)
  · refine RelCT.mono (P := R4 fun σ s => MI σ K s) (RelCT.seq (relInv (I' := fun σ s => ArgI σ K s)
      (fun σ s _ h => argsK_ok hK h.pinv) (taintRel [.r12, .r13, .rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.pinv.env.r12, h₂.pinv.env.r12, pub_sd hq]
        · rw [h₁.pinv.env.r13, h₂.pinv.env.r13, pub_aP hq]
        · exact env_rbx hq h₁.pinv.env h₂.pinv.env) c))
      (RelCT.seq (call_ct hK) (relInv (I' := fun σ s => PInv σ (K + 1) s) (fun σ s _ h => andK_ok h)
        (taintRel [] SampleNtt.nil_regs (by taint_decide))))) (fun _ _ h => h.1) fun _ _ h => h
  · refine RelCT.mono (P := R4 fun σ s => MI σ K s ∧ s.cf = some false)
      (relInv (I' := fun σ s => PInv σ (K + 1) s) (fun σ s _ h => WP.block_nil (skipK_ok hK h.1 h.2))
        (taintRel [] SampleNtt.nil_regs (by taint_decide)))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hc⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hc⟩, ⟨h₂, ?_⟩⟩) fun _ _ h => h
    have hc' : x.cf = some false := hc
    rw [h₂.cf, ← pub_Lt hq hK, ← h₁.cf, hc']

theorem parse_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13])
      (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
        .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
        .mov32 .rcx (.imm 168)]) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) h₂).isSome = true) :
    RelCT isa (R4 fun σ s => PInv σ K s) (parse K) (R4 fun σ s => PInv σ (K + 1) s) := by
  unfold parse
  exact RelCT.seq (setup_ct hK c₁) (RelCT.seq (loop_ct hK 168) (fallback_ct hK c₂))

theorem pinv0 {σ s : State} (h : SqInv σ 3 s) : PInv σ 0 s :=
  ⟨h.env, fun k hk p hp' => h.buf k hk p (by omega), by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega)⟩

theorem ct : ConstantTime isa sample4K.pre sample4K.pub Impl.MlKem.X86_64.Sample4.sampleNTT4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq start_ct (RelCT.seq sq0_ct
    (RelCT.seq (sq_ct 1 (by decide) (by taint_decide)) (RelCT.seq (sq_ct 2 (by decide) (by taint_decide)) ?_))))
  refine RelCT.seq (RelCT.mono (parse_ct (K := 0) (by decide) (by taint_decide) (by taint_decide))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, pinv0 h₁, pinv0 h₂⟩) fun _ _ h => h) ?_
  refine RelCT.seq (parse_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (parse_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (parse_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlKem.X86_64.S4
