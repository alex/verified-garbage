import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.Framework.X86.Spill

/-!
# X448 on x86 (32-bit): saving the callee-saved registers

Four scratch words hold the incoming values of ebx, esi, edi, and ebp until
the final restore.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The callee-saved registers and their scratch words. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ savedSlots, p.2 + 4 ≤ 16 := by decide

abbrev Saved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m (off base) g savedSlots

theorem Saved.outside {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h16 : 16 ≤ o) : Saved base g m' :=
  h.of_readW fun p hp => have := savedSlots_bound p hp; ho.word (Or.inl (by omega)) (by omega)

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : 16 ≤ x) (hy : 16 ≤ y) :
    Saved base g m' :=
  h.of_readW fun p hp => have := savedSlots_bound p hp
    ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by omega)

theorem Saved.field {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {o : Nat} (hm : FieldMem base o m m') (ho : 16 ≤ o) : Saved base g m' :=
  h.of_readW fun p hp => have := savedSlots_bound p hp
    hm.word (Or.inl (by omega)) (by simp only [ACC]; omega)

/-- A frame of the first `n` bytes at `base`. -/
theorem Outside.of_frame {base : Addr} {n : Nat} {m m' : Mem} (hf : Frame [⟨base, n⟩] m m') :
    Outside base 0 n m m' :=
  fun x hx => hf x fun r hr => by
    rw [List.mem_singleton.mp hr]
    simp only [Region.Contains]
    simp only [ofs] at hx
    omega

theorem save_ok {s : State} (hp : Pre s) :
    WP isa (.block save) s fun t =>
      Scr t ((arg s 3).setWidth 64) ∧ Saved ((arg s 3).setWidth 64) s.gpr t.mem ∧
      Outside ((arg s 3).setWidth 64) 0 16 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (at_ .esp 16)) ::
    (Spill.saveCode .eax savedSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine loadArg_ok hp rfl rfl rfl (Outside.refl _ _ _ _) (by decide : 3 < 4) fun t ht => ?_
  have hfit := hp.sc_fit
  refine Spill.save_ofNat_ok savedSlots (n := 16) (by decide) (by rw [ht.gpr]; omega)
    (fun p h => by rw [ht.gpr, ht.wr]; exact ⟨_, hp.sc_in, contains_sc (by have := savedSlots_bound p h; omega)⟩)
    fun u hu => ?_
  have hm : u.mem = Spill.saveMem s.mem (off ((arg s 3).setWidth 64)) s.gpr savedSlots := by
    rw [hu.mem, ht.gpr, ht.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => ht.other _ (by revert p h; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (ht.rest (by decide)).trans
    (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u) |>.trans (hv.rest (by decide))⟩
  · rw [hv.gpr, hu.gpr, ht.gpr]
  · rw [hv.wr, hu.wr, ht.wr]; exact hp.sc_in
  · rw [hv.gpr, hu.gpr, ht.gpr]; exact hfit
  · rw [hv.mem, hm]; exact Spill.saveMem_saved_ofNat _ _ _ (n := 16) (by decide) (by decide)
  · rw [hv.mem, hm]
    exact Outside.of_frame (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      Offset.contains_base _ (savedSlots_bound p h) (by have := savedSlots_bound p h; omega))

end VG.Proof.X448.X86
