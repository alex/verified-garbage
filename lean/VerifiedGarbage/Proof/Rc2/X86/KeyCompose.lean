import VerifiedGarbage.Proof.Rc2.X86.KeySteps

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem fillKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi))) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      zeroFlag s' = some ((s.gpr .ecx + 1 - 128) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx))
          (Spec.Rc2.pi (s.mem (addr32 (s.gpr .edi + s.gpr .ecx - 1)) +
          s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi)))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s₁)
  intro s₂ h₂
  have k₁ : Keep keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have k₂ : Keep keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .edi (by decide)
  have index := (keep₁.reg .ecx (by decide)).trans rfl
  have index₂ : s₂.gpr .ecx = s.gpr .ecx := (h₂.2.reg .ecx (by decide)).trans index
  have write₂ : InRegions s₂.wr (addr32 (s₂.gpr .edi + s₂.gpr .ecx)) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block (piLookup ++ storeKey)) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) (Spec.Rc2.pi ((s.gpr .eax).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s)
  intro s₁ h₁
  have ptr := h₁.2.reg .edi (by decide)
  have index := h₁.2.reg .ecx (by decide)
  have valid : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := storeByte_ok s₁ valid
  refine WP.of_runBlock ⟨s₂, run₂, index₂.trans index, ?_⟩
  constructor
  · intro r hr
    rw [keep₂.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))]
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> subst r <;> decide))
  · rw [keep₂.mem, h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact keep₂.rd.trans h₁.2.rd
  · exact keep₂.wr.trans h₁.2.wr

theorem reduceKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx)) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .ecx = s.gpr .ecx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx))
          (Spec.Rc2.pi (s.mem (addr32 (s.gpr .edi + s.gpr .ecx)) &&& (s.gpr .ebx).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .edi (by decide)
  have index := keep₁.reg .ecx (by decide)
  have valid : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (piStore_ok s₁ valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h <;> subst r <;> exact hr (by decide)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem descendKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi))) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + (s.gpr .ecx - 1))) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx - 1 ∧ zeroFlag s' = some ((s.gpr .ecx - 1) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + (s.gpr .ecx - 1)))
          (Spec.Rc2.pi (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) ^^^
            s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi)))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .edi (by decide)
  have valid : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  rw [← List.append_assoc, WP.block_append_iff]
  apply WP.mono (piStore_ok s₁ valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .ecx (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.X86
