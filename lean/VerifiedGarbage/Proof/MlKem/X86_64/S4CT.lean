import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, constant time but for the seeds

Two runs whose seeds (the declared leak) and pointers agree leak the same. The
code but for the loops of `parse` and their fallbacks is proven by the taint
analysis, from the pointers. Both runs read the same XOF output, so in the
loops they are at the same iteration with the same coefficients sampled: each
group of four iterations takes the same branch (on `j < 249`, `vgrp_ct`); the
vector code computes the same mask of the candidates in `eax` (`VI.rax`), so
it loads the same entry of the table, stores to the same address and counts
the same (the taint analysis, from `rax`, `rbx`, `rbp`, `rdi` and `rsi`), and
`vg_mlkem_sample_ntt`'s loop runs as in that function (`body_ct`). The
fallbacks take the same branch, and call `vg_mlkem_sample_ntt` on the same
seed.
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

/-! ## The groups of four iterations -/

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

/-- Two runs at iteration `t + u` of the scalar group from iteration `t`, `n = 4 - u` iterations from its
end. -/
def GI (K t : Nat) (c : BitVec 64) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ u, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = 4 - u ∧ u < 4 ∧
    LAt σ₁ K (t + u) s₁ ∧ LAt σ₂ K (t + u) s₂ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (4 - u) ∧
    s₂.gpr .rcx = BitVec.ofNat 64 (4 - u) ∧ s₁.gpr .r10 = c ∧ s₂.gpr .r10 = c ∧
    ¬ (Lt σ₁ K t).length < 249 ∧ ¬ (Lt σ₂ K t).length < 249

theorem gi_brel {K t : Nat} {c : BitVec 64} {n : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s₁ s₂ : State}
    (h : GI K t c n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, u, p₁, p₂, hq, _, hu, l₁, l₂, c₁, c₂, -⟩ := h
  refine ⟨poly4 (aP σ₁) K, Lt σ₁ K (t + u), bpre p₁ hK (by omega) l₁,
    by rw [pub_aP hq, pub_Lt hq hK]; exact bpre p₂ hK (by omega) l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [c₁, c₂], fun k hk => ?_⟩
  rw [out_byte hK l₁ (by omega), out_byte hK l₂ (by omega), pub_B hq hK]

/-- The four iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem iloop_ct {K t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 4 ≤ 168) (n : Nat) :
    RelCT isa (GI K t c n) (.loop snBody .ne)
      (R4 fun σ s => LAt σ K (t + 4) s ∧ s.gpr .r10 = c ∧ ¬ (Lt σ K t).length < 249) := by
  refine RelCT.loop (M := isa) (GI K t c) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, sample4K.pre p.1 ∧ p.2 < 4 ∧
      LAt p.1 K (t + p.2) x → (LAt p.1 K (t + p.2 + 1) x' ∧ x'.gpr .rcx = x.gpr .rcx - 1 ∧
        x'.zf = some (x.gpr .rcx - 1 == 0)) ∧ x'.gpr .r10 = x.gpr .r10)
    (RelCT.mono body_ct (fun x y h => gi_brel hK ht h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, u, p₁, p₂, _, _, hu, l₁, l₂, _⟩ := h
    exact ⟨WP.all (fun p hp' => WP.gpr (lat_step (pre_of hp'.1) hK (by omega) hp'.2.2) (r := .r10) (by decide))
        ⟨(σ₁, u), p₁, hu, l₁⟩,
      WP.all (fun p hp' => WP.gpr (lat_step (pre_of hp'.1) hK (by omega) hp'.2.2) (r := .r10) (by decide))
        ⟨(σ₂, u), p₂, hu, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, u, p₁, p₂, hq, hn, hu, l₁, l₂, c₁, c₂, d₁, d₂, v₁, v₂⟩ f₁ f₂
    obtain ⟨⟨l₁', r₁, z₁⟩, e₁⟩ := f₁ (σ₁, u) ⟨p₁, hu, l₁⟩
    obtain ⟨⟨l₂', r₂, z₂⟩, e₂⟩ := f₂ (σ₂, u) ⟨p₂, hu, l₂⟩
    rw [c₁, SampleNtt.zf_last (by decide) hu] at z₁
    rw [c₂, SampleNtt.zf_last (by decide) hu] at z₂
    rw [c₁, ofNat64_pred (by omega) (by omega)] at r₁
    rw [c₂, ofNat64_pred (by omega) (by omega)] at r₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : u + 1 = 4 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [Nat.add_assoc, this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁', by rw [e₁, d₁], v₁⟩, ⟨l₂', by rw [e₂, d₂], v₂⟩⟩
    · have : u + 1 ≠ 4 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨4 - (u + 1), by omega, σ₁, σ₂, u + 1, p₁, p₂, hq, rfl, by omega, by rw [← Nat.add_assoc]; exact l₁',
        by rw [← Nat.add_assoc]; exact l₂', by rw [r₁]; congr 1, by rw [r₂]; congr 1, by rw [e₁, d₁], by rw [e₂, d₂],
        v₁, v₂⟩

/-- The relation of two runs at a group: iteration `t`, the constants in place while there are
fewer than 249 coefficients, and `r10 = c`. -/
abbrev RV (K t : Nat) (c : BitVec 64) : State → State → Prop := R4 fun σ s => LV σ K t s ∧ s.gpr .r10 = c

theorem cmpG_ok {σ : State} {K t : Nat} {c : BitVec 64} {s : State} (h : LV σ K t s ∧ s.gpr .r10 = c) :
    WP isa (.block [.alu .cmp .rdi (.imm 249)]) s fun s' => (LV σ K t s' ∧ s'.gpr .r10 = c) ∧
      s'.cf = some (decide ((Lt σ K t).length < 249)) := by
  have hlen : (Lt σ K t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  refine WP.mono (cmp249_ok s) fun s' ⟨hcf, hm, hg, hrd, hwr, hl⟩ => ?_
  exact ⟨⟨⟨h.1.lat.same hg hm hrd hwr, fun h' => (h.1.vc h').same hl⟩, by rw [hg]; exact h.2⟩,
    by rw [hcf, h.1.lat.rdi, ofNat64_toNat (by omega)]⟩

/-- A group of four iterations. -/
theorem vgrp_ct {K t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 4 ≤ 168) :
    RelCT isa (RV K t c) vgrp (RV K (t + 4) c) := by
  unfold vgrp
  refine RelCT.seq (relInv (I' := fun σ s => (LV σ K t s ∧ s.gpr .r10 = c) ∧
      s.cf = some (decide ((Lt σ K t).length < 249))) (fun σ s _ h => cmpG_ok h)
    (taintRel [.rdi] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.lat.rdi, h₂.1.lat.rdi, pub_Lt hq hK])
      (by taint_decide))) (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
        show x.cf = y.cf; rw [h₁.2, h₂.2, pub_Lt hq hK]) ?_ ?_)
  · -- with the vector code
    refine RelCT.mono (P := R4 fun σ s => LAt σ K t s ∧ VC s ∧ (Lt σ K t).length < 249 ∧ s.gpr .r10 = c)
      (RelCT.seq (relInv (I' := fun σ s => VI σ K t s ∧ s.gpr .r10 = c)
          (fun σ s hp h => WP.mono (vec1_ok (pre_of hp) hK ht h.1 h.2.1 h.2.2.1) fun _ ⟨hi, h10⟩ =>
            ⟨hi, by rw [h10]; exact h.2.2.2⟩)
          (taintRel [.rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rsi, h₂.1.rsi, at', at', pub_scr hq])
            (by taint_decide)))
        (relInv (fun σ s hp h => WP.mono (vec2_ok (pre_of hp) hK ht h.1) fun _ ⟨l, v, h10⟩ =>
            ⟨⟨l, fun _ => v⟩, by rw [h10]; exact h.2⟩)
          (taintRel [.rbx, .rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl
            · exact env_rbx hq h₁.1.lat.pinv.env h₂.1.lat.pinv.env
            · rw [h₁.1.rax, h₂.1.rax, pub_B hq hK]
            · rw [h₁.1.lat.rbp, h₂.1.lat.rbp, pub_aP hq]
            · rw [h₁.1.lat.rdi, h₂.1.lat.rdi, pub_Lt hq hK]
            · rw [h₁.1.lat.rsi, h₂.1.lat.rsi, at', at', pub_scr hq]) (by taint_decide))))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨⟨l₁, v₁⟩, d₁⟩, f₁⟩, ⟨⟨⟨l₂, v₂⟩, d₂⟩, f₂⟩⟩, hb⟩ => ?_) fun _ _ h => h
    have hb' : (Lt σ₁ K t).length < 249 := by
      have : x.cf = some true := hb
      rw [f₁] at this; simpa using this
    have hb'' : (Lt σ₂ K t).length < 249 := by rw [← pub_Lt hq hK]; exact hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, v₁ hb', hb', d₁⟩, ⟨l₂, v₂ hb'', hb'', d₂⟩⟩
  · -- with `snBody`
    refine RelCT.mono (P := R4 fun σ s => LAt σ K t s ∧ ¬ (Lt σ K t).length < 249 ∧ s.gpr .r10 = c) ?_ ?_
      fun _ _ h => h
    · refine RelCT.seq (relInv (I' := fun σ s => (LAt σ K t s ∧ ¬ (Lt σ K t).length < 249 ∧ s.gpr .r10 = c) ∧
          s.gpr .rcx = BitVec.ofNat 64 4) ?_ ?_) ?_
      · intro σ s _ h
        refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 4)
          (by xrun) (by decide)) fun s' ⟨⟨hm, hc⟩, k⟩ => ?_
        exact ⟨⟨h.1.same' hm k, h.2.1, by rw [k.gpr (by decide)]; exact h.2.2⟩, hc⟩
      · exact taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
      · refine RelCT.mono (iloop_ct (c := c) hK ht 4) ?_ ?_
        · rintro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨l₁, v₁, d₁⟩, c₁⟩, ⟨⟨l₂, v₂, d₂⟩, c₂⟩⟩
          exact ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by decide, l₁, l₂, c₁, c₂, d₁, d₂, v₁, v₂⟩
        · rintro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, d₁, v₁⟩, ⟨l₂, d₂, v₂⟩⟩
          exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨l₁, fun h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ₁ K t 4) h') v₁⟩, d₁⟩,
            ⟨⟨l₂, fun h' => absurd (Nat.lt_of_le_of_lt (Lt_mono σ₂ K t 4) h') v₂⟩, d₂⟩⟩
    · rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨⟨l₁, -⟩, d₁⟩, f₁⟩, ⟨⟨⟨l₂, -⟩, d₂⟩, f₂⟩⟩, hb⟩
      have hb' : ¬ (Lt σ₁ K t).length < 249 := by
        have : x.cf = some false := hb
        rw [f₁] at this; simpa using this
      have hb'' : ¬ (Lt σ₂ K t).length < 249 := by rw [← pub_Lt hq hK]; exact hb'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, hb', d₁⟩, ⟨l₂, hb'', d₂⟩⟩

/-! ## The fallbacks -/

/-- The call of `vg_mlkem_sample_ntt` on seed `K`, with `X σ` of the memory, which its writes keep. -/
theorem call_ct {X : State → Mem → Prop} {K : Nat} (hK : K < 4)
    (hX : ∀ σ, sample4K.pre σ → ∀ m m', Frame (cWr σ K ++ [stkR σ]) m m' → X σ m → X σ m') :
    RelCT isa (R4 fun σ s => ArgI (X σ) σ K s) (.call "vg_mlkem_sample_ntt" sampleNTT)
      (R4 fun σ s => CallI (X σ) σ K s) :=
  relInv (fun σ s hp h => callK_ok (pre_of hp) hK (hX σ hp) h) (RelCT.callEx sample_correct sample_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, pub_sp hq]
      refine ⟨_, _, _, _, argK_pre (pre_of p₁) hK h₁, argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt24 s₁ (n := 34) (by decide) (argK_kS (pre_of p₁) hK h₁),
        ce_bytesAt24 s₂ (n := 34) (by decide) (argK_kS (pre_of p₂) hK h₂),
        seed_bytes (pre_of p₁) hK h₁.pinv.env.frame, seed_bytes (pre_of p₂) hK h₂.pinv.env.frame, pub_B hq hK]
      simp only [pub_sd hq, pub_aP hq, at', pub_scr hq, hsp, and_self])

/-- The arguments of the call on seed `K`, given their taint analysis. -/
theorem args_ct {X : State → Mem → Prop} {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R4 fun σ s => PC (X σ) σ K s)
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) (R4 fun σ s => ArgI (X σ) σ K s) :=
  relInv (fun σ s _ h => argsK_ok hK h) (taintRel [.r12, .r13, .rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.env.r12, h₂.env.r12, pub_sd hq]
    · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]
    · exact env_rbx hq h₁.env h₂.env) c)

theorem and_ct {X : State → Mem → Prop} {K : Nat} :
    RelCT isa (R4 fun σ s => CallI (X σ) σ K s) (.block [.alu32 .and .r14 (.reg .rax)])
      (R4 fun σ s => PC (X σ) σ (K + 1) s) :=
  relInv (fun σ s _ h => andK_ok h) (taintRel [] SampleNtt.nil_regs (by taint_decide))

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
  · refine RelCT.mono (P := R4 fun σ s => PInv σ K s)
      (RelCT.seq (args_ct (X := BufT) hK c) (RelCT.seq (call_ct hK fun σ hp => bufOK_call (pre_of hp) hK) and_ct))
      (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, h₁.pinv, h₂.pinv⟩) fun _ _ h => h
  · refine RelCT.mono (P := R4 fun σ s => MI σ K s ∧ s.cf = some false)
      (relInv (I' := fun σ s => PInv σ (K + 1) s) (fun σ s _ h => WP.block_nil (skipK_ok hK h.1 h.2))
        (taintRel [] SampleNtt.nil_regs (by taint_decide)))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hc⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hc⟩, ⟨h₂, ?_⟩⟩) fun _ _ h => h
    have hc' : x.cf = some false := hc
    rw [h₂.cf, ← pub_Lt hq hK, ← h₁.cf, hc']

/-! ## The loop of `parse K` -/

/-- Two runs at group `2 i` of the loop, `n = 21 - i` iterations from its end. -/
def LI (K n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ i, n = 21 - i ∧ i < 21 ∧ RV K (8 * i) (BitVec.ofNat 64 (21 - i)) s₁ s₂

theorem sub10_ct {K t : Nat} {c : BitVec 64} :
    RelCT isa (RV K t c) (.block [.alu .sub .r10 (.imm 1)])
      (R4 fun σ s => LV σ K t s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) :=
  relInv (fun σ s _ h => WP.mono (sub10_ok s) fun s' ⟨⟨hm, h10, hz, hl⟩, k⟩ =>
      ⟨⟨h.1.lat.same' hm k, fun h' => (h.1.vc h').same hl⟩, by rw [h10, h.2], by rw [hz, h.2]⟩)
    (taintRel [.r10] (fun x y ⟨σ₁, σ₂, _, _, _, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide))

theorem loopV_ct {K : Nat} (hK : K < 4) (n : Nat) :
    RelCT isa (LI K n) (.loop Sample4.vbody .ne) (R4 fun σ s => LAt σ K 168 s) := by
  refine RelCT.loop (M := isa) (LI K) (fun n => ?_) n
  refine RelCT.mono (P := fun s₁ s₂ => ∃ i, n = 21 - i ∧ i < 21 ∧ RV K (8 * i) (BitVec.ofNat 64 (21 - i)) s₁ s₂)
    (RelCT.exists_ fun i => ?_) (fun _ _ h => by unfold LI at h; exact h) fun _ _ h => h
  by_cases hi : i < 21 ∧ n = 21 - i
  · obtain ⟨hi, hn⟩ := hi
    refine RelCT.mono (P := RV K (8 * i) (BitVec.ofNat 64 (21 - i)))
      (RelCT.seq (vgrp_ct hK (by omega)) (RelCT.seq (vgrp_ct hK (by omega)) sub10_ct))
      (fun _ _ h => h.2.2) fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, d₁, z₁⟩, ⟨l₂, d₂, z₂⟩⟩ => ?_
    rw [ofNat64_pred (by omega) (by omega)] at d₁ d₂ z₁ z₂
    rw [ofNat64_beq_zero (by omega)] at z₁ z₂
    rw [show 8 * i + 4 + 4 = 8 * (i + 1) by omega] at l₁ l₂
    refine ⟨by show x.zf.map _ = y.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
    · have : 21 - i - 1 = 0 := by
        have : x.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [show i + 1 = 21 by omega] at l₁ l₂
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁.lat, l₂.lat⟩
    · have : 21 - i - 1 ≠ 0 := by
        have : x.zf.map (!·) = some true := ht
        rw [z₁] at this; simpa using this
      exact ⟨21 - (i + 1), by omega, i + 1, rfl, by omega, σ₁, σ₂, p₁, p₂, hq,
        ⟨l₁, by rw [d₁]; congr 1⟩, ⟨l₂, by rw [d₂]; congr 1⟩⟩
  · exact RelCT.of_false fun _ _ h => hi ⟨h.2.1, h.1⟩

/-- `parse K`. -/
theorem parse_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (setup K ++ cstLoad)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) h₂).isSome = true) :
    RelCT isa (R4 fun σ s => PInv σ K s) (parse K) (R4 fun σ s => PInv σ (K + 1) s) := by
  unfold parse
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => LV σ K 0 s ∧ s.gpr .r10 = BitVec.ofNat 64 21)
      (fun σ s hp h => setup_ok (pre_of hp) hK h)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq h₁.env h₂.env
        · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]) c₁)) (fun _ _ h => h)
      (Q' := LI K 21) fun x y h => ⟨0, rfl, by decide, h⟩)
    (RelCT.seq (loopV_ct hK 21) (RelCT.seq (relInv (I' := fun σ s => LAt σ K 168 s) (fun _ _ _ h => vz_lat h)
      (taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))) (fallback_ct hK c₂)))

theorem tab_ct : RelCT isa (R4 fun σ s => SqInv σ 3 s) (.block tabBuild) (R4 fun σ s => PInv σ 0 s) :=
  relInv (fun σ s hp h => pinv0_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))

theorem ct : ConstantTime isa sample4K.pre sample4K.pub Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq start_ct (RelCT.seq sq0_ct
    (RelCT.seq (sq_ct 1 (by decide) (by taint_decide)) (RelCT.seq (sq_ct 2 (by decide) (by taint_decide))
      (RelCT.seq tab_ct ?_)))))
  refine RelCT.seq (parse_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (parse_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (parse_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (parse_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlKem.X86_64.S4
