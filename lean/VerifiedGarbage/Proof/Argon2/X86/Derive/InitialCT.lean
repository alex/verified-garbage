import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1
import VerifiedGarbage.Proof.Argon2.X86.HPrime.HashCT

/-!
# Argon2 on x86 (32-bit): H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s macros' relations
(`HPrime.init_rel`, `update_rel`, `finalize_rel`, `absorbFixed_rel`), from
the same arguments: `scratch`, the inputs' places and lengths, and the byte
count, which only the inputs' lengths fix.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.X86.HPrime (Ctx InitIn UpdateIn FinalizeIn FixedIn)
open VG.Impl.Argon2.X86.Derive (countLoOff countHiOff argOff)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `scratch`'s context in the second run, in the first run's terms. -/
theorem ctx₂ {s : State} (h : Inv s₀₂ s) (hb : s.gpr .ebx = scrP s₀₂) : Ctx (scrP s₀₁) (E s₀₁) s := by
  rw [T.pb.scrP_eq, T.pb.E]; exact ctx T.hp₂ h hb

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.X86.Derive.start fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  unfold Impl.Argon2.X86.Derive.start
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => stA_ok T.hp₁ h.1 h.2) (fun s h => stA_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW ((HPrime.init_rel (B := scrP s₀₁) (E := E s₀₁) (n := 64) (by decide) (by decide)).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, h.1.2.2.2⟩, ⟨T.ctx₂ h.2.1 h.2.2.2.1, h.2.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => stInit_ok T.hp₁ h) (fun s h => stInit_ok T.hp₂ h) ?_
  refine RelCT.seqW (T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t ∧ t.gpr .ebx = scrP s₀₁ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀₁).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀₁).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₁))
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t ∧ t.gpr .ebx = scrP s₀₂ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀₂).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀₂).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₂))
    (fun s h => (header_ok T.hp₁ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩)
    (fun s h => (header_ok T.hp₂ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩) ?_
  refine RelCT.seqW ((HPrime.absorbFixed_rel (B := scrP s₀₁) (E := E s₀₁) (offset := 768) (size := 24)
      (by omega) (by decide) (by decide) (stk_scr T.hp₁ (by decide) (by decide)) ⟨_, by taint_decide⟩).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, scr_cov T.hp₁ h.1.1 (by decide)⟩,
        ⟨T.ctx₂ h.2.1 h.2.2.2.1, by rw [T.pb.scrP_eq]; exact scr_cov T.hp₂ h.2.1 (by decide)⟩⟩) fun _ _ h => h)
    (fun s h => stFix_ok T.hp₁ h) (fun s h => stFix_ok T.hp₂ h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR₁ : (⟨(arg s₀₁ ptr).setWidth 64, (arg s₀₁ len).toNat⟩ : Region) ∈ [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁])
    (hR₂ : (⟨(arg s₀₂ ptr).setWidth 64, (arg s₀₂ len).toNat⟩ : Region) ∈ [pwR s₀₂, saltR s₀₂, secR s₀₂, adR s₀₂])
    (hfit₁ : (arg s₀₁ ptr).toNat + (arg s₀₁ len).toNat ≤ 2 ^ 32)
    (hfit₂ : (arg s₀₂ ptr).toNat + (arg s₀₂ len).toNat ≤ 2 ^ 32) {data₁ data₂ : List Byte}
    (hd : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (heq : data₁.length = data₂.length)
    (hcA : ∃ hc, (VG.Taint.check taint (τB [] [.ebx]) (.block [.mov .eax (Impl.Argon2.X86.Derive.fr (argOff len)),
      .store ⟨.ebx, 792⟩ .eax, .mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff), .mov .esi (.reg .ebx), .alu .add .esi (.imm 792),
      .mov .edi (.imm 4)]) hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check taint (τB [] []) (.block (Impl.Argon2.X86.Derive.addCount (.imm 4) ++
      ([.mov .esi (Impl.Argon2.X86.Derive.fr (argOff ptr)), .mov .edi (Impl.Argon2.X86.Derive.fr (argOff len))] :
        List Instr)))
      hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check taint (τB [] [])
      (.block (Impl.Argon2.X86.Derive.addCount (Impl.Argon2.X86.Derive.fr (argOff len)))) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) (Impl.Argon2.X86.Derive.absorb ptr len)
      fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  have ep := T.pb.arg_eq hptr
  have el := T.pb.arg_eq hlen
  have e792 : (scrP s₀₁ + 792).setWidth 64 = (scrP s₀₁).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega)
  have cov792 : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      Covers [⟨(scrP s₀ + 792).setWidth 64, 4⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h => by
    have := hp.scr_fits
    have e : (scrP s₀ + 792).setWidth 64 = (scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
      HPrime.setWidth_add (d := 792) (by omega)
    rw [e]; exact Covers.right (scr_cov hp h (by decide))
  have covIn : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      Covers [⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h hR => by
    have hR' : (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈
        [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
    rw [h.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩
  have hS : (⟨(arg s₀₁ ptr).setWidth 64, (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, memR s₀₁, scrR s₀₁, outR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  have hR' : (⟨(arg s₀₁ ptr).setWidth 64, (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, argR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.X86.Derive.absorb
  refine RelCT.seqW (T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.ebx, h.2.ebx, T.pb.scrP_eq]⟩) hcA)
    (fun s h => absA_ok T.hp₁ hlen h.hc) (fun s h => absA_ok T.hp₂ hlen h.hc) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (E := E s₀₁) (D := scrP s₀₁ + 792) (L := 4)
      (lo := BitVec.ofNat 32 data₁.length) (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))
      (by have : (scrP s₀₁ + 792).toNat = (scrP s₀₁).toNat + 792 := add_nat (k := 792) (by omega)
          omega)
      (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by rw [e792]; exact stk_scr T.hp₁ (by decide) (by decide))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁, _⟩, ⟨g₂, e₂, d₂, c₂, x₂, _⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.ebx, e₁, d₁, c₁, x₁, cov792 T.hp₁ g₁.inv⟩,
         ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [e₂, T.pb.scrP_eq], d₂, by rw [c₂, heq], by rw [x₂, heq],
           by rw [T.pb.scrP_eq]; exact cov792 T.hp₂ g₂.inv⟩⟩) fun _ _ h => h)
    (fun s h => absU1_ok T.hp₁ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun s h => absU1_ok T.hp₂ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcB)
    (fun s h => absB_ok T.hp₁ hptr hlen h) (fun s h => absB_ok T.hp₂ hptr hlen h) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (E := E s₀₁) (D := arg s₀₁ ptr)
      (L := (arg s₀₁ len).toNat) (lo := BitVec.ofNat 32 (data₁.length + 4))
      (hi := BitVec.ofNat 32 ((data₁.length + 4) / 2 ^ 32))
      hfit₁ ((T.hp₁.ro_w _ hR' (scrR s₀₁) (by simp)).sub_right (Region.sub_prefix (by decide)))
      ((T.hp₁.stk_all _ hS).sub_left fun a ha => call_stk T.hp₁ a (below60_call T.hp₁ a ha))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁⟩, ⟨g₂, e₂, d₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.ebx, e₁, d₁, c₁, x₁, covIn T.hp₁ g₁.inv hR₁⟩,
         ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [e₂, ep], by rw [d₂, el], by rw [c₂, heq], by rw [x₂, heq],
           by rw [ep, el]; exact covIn T.hp₂ g₂.inv hR₂⟩⟩) fun _ _ h => h)
    (fun s h => absU2_ok T.hp₁ hR₁ hfit₁ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun s h => absU2_ok T.hp₂ hR₂ hfit₂ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose absorbed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) Impl.Argon2.X86.Derive.finish fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.finish
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fiA_ok T.hp₁ h) (fun s h => fiA_ok T.hp₂ h) ?_
  refine RelCT.seqW ((HPrime.finalize_rel (B := scrP s₀₁) (E := E s₀₁) (lo := BitVec.ofNat 32 data₁.length)
      (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))).mono
      (fun s₁ s₂ ⟨⟨g₁, c₁, x₁⟩, ⟨g₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.ebx, c₁, x₁⟩, ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [c₂, heq], by rw [x₂, heq]⟩⟩)
      fun _ _ h => h)
    (fun s h => fiFin_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fiFin_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  exact T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- H₀'s code leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.X86.Derive.code fun _ _ => True := by
  have l1 := (arg s₀₁ 2).isLt
  have l2 := (arg s₀₁ 4).isLt
  have l3 := (arg s₀₁ 10).isLt
  have hpp := T.pb
  have a2 : (arg s₀₂ 2).toNat = (arg s₀₁ 2).toNat := by rw [hpp.arg_eq (by decide)]
  have a4 : (arg s₀₂ 4).toNat = (arg s₀₁ 4).toNat := by rw [hpp.arg_eq (by decide)]
  have a10 : (arg s₀₂ 10).toNat = (arg s₀₁ 10).toNat := by rw [hpp.arg_eq (by decide)]
  have a12 : (arg s₀₂ 12).toNat = (arg s₀₁ 12).toNat := by rw [hpp.arg_eq (by decide)]
  unfold Impl.Argon2.X86.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => start_ok T.hp₁ h.1 h.2) (fun s h => start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.pw_fits T.hp₂.pw_fits (by rw [Proof.Argon2.initialHeader_length]; omega)
      (by rw [Proof.Argon2.initialHeader_length, Proof.Argon2.initialHeader_length])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₁.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₂.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.salt_fits T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₁.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.sec_fits T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₁.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.ad_fits T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4,
        a10])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₁.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; have := (arg s₀₂ 10).isLt; omega) h) ?_
  exact T.finish_rel (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length,
    bytesAt_length, a2, a4, a10, a12])

end Two

end VG.Proof.Argon2.X86.Derive
