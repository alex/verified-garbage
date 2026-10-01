import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

theorem zeroWords_ok {s : State} {E : BitVec 32} {start count : Nat}
    (he : s.gpr .esp = E) (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hw : FR E ∈ s.wr) (hlen : start + count ≤ 64) :
    WP isa (.block (zeroWords start count)) s fun t => SetupStep s t ∧
      Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (addr E (4 * (start + j))) 32 = 0 := by
  induction count generalizing s start with
  | zero =>
    exact WP.block_nil ⟨SetupStep.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | succ count ih =>
    rw [zeroWords, List.replicate_succ, setup, WP.block_append_iff]
    have hs : start < 64 := by omega
    refine WP.mono (put_ok (v := .const 0) he (fun _ _ h => by cases h)
      (frame_word hf hw (by omega))) fun u ⟨hu, hm⟩ => ?_
    refine WP.mono (ih (hu.esp.trans he) (hu.wr ▸ hw) (by omega)) fun t ⟨ht, ft, vt⟩ => ?_
    refine ⟨hu.trans ht, ?_, ?_⟩
    · have fs : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * (count + 1)⟩] s.mem u.mem := by
        rw [hm, addr_eq (by omega)]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      refine fs.trans (Frame.sub ft ?_)
      rintro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero]
        have keep : t.mem.readW (addr E (4 * start)) 32 = u.mem.readW (addr E (4 * start)) 32 := by
          rw [addr_eq (by omega)]
          refine ft.readW (Region.contains_self _ _) ?_ (by decide)
          rintro r hr
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)
        rw [keep, hm, Mem.readW_writeW_self32]
        rfl
      | succ j =>
        rw [show start + (j + 1) = start + 1 + j by omega]
        exact vt j (by omega)

theorem Ctx.zeroWords {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} (hc : Ctx E g m₀ rd wr s) {start count : Nat}
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hlen : start + count ≤ 64) :
    WP isa (.block (zeroWords start count)) s fun t => Ctx E g m₀ rd wr t ∧
      Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (addr E (4 * (start + j))) 32 = 0 := by
  refine WP.mono (zeroWords_ok hc.esp hf (by rw [hc.wr]; exact List.mem_cons_self) hlen)
    fun t ⟨ht, hft, hz⟩ => ⟨hc.of_frame ht.rd ht.wr ht.esp ?_ hft ?_, hft, hz⟩
  · intro r hr _
    apply ht.regs
    rintro rfl
    simp [calleeSaved] at hr
  · rintro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (Offset.sub_base _ (by omega))

end VG.Proof.Ed25519.X86.Whole
