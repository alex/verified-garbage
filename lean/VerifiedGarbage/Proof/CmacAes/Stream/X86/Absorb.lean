import VerifiedGarbage.Proof.CmacAes.Stream.X86.AbsorbBlocks

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` around the calls

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`); after each call, what the code that follows needs (`AAft₁`,
`AAft₂`), and what `chain2` leaves for the second call (`AMid₂`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.CmacAes.X86 (wp_arg saveMem_congr)
open VG.Proof.Cmac.Stream (held held_le)

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) : Mem :=
  writeBytes (savedMem s₀ (aSc s₀)) ((aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)))
    (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀)))

theorem m4_frame (s₀ : State) :
    Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩]
      (savedMem s₀ (aSc s₀)) (m4 s₀) :=
  writeBytes_frame _ _ _ (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)

theorem m4_big {s₀ : State} (hp : APre s₀) : Frame (ABig s₀) s₀.mem (m4 s₀) := by
  have := f_le (aC s₀) (aL s₀)
  exact hp.savedMem_big.trans ((m4_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega)⟩)

/-- The save. -/
theorem absSave_wp {s₀ : State} (hp : APre s₀) :
    WP isa (.block absSave) s₀ fun s => ACtx s₀ s ∧ s.mem = savedMem s₀ (aSc s₀) := by
  have fS : (arg s₀ 6).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  rw [show absSave = .mov .eax (argOp 6) :: (save ++ []) from rfl]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := aSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => WP.block_nil ?_
  have hm₂ : s₂.mem = savedMem s₀ (aSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_eax p hp')
  exact ⟨ACtx.of_frame hp (by rw [g₂, u₁.other _ (by decide)]) (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])
    (hm₂ ▸ hp.savedMem_big), hm₂⟩

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ s : State) : Prop where
  args : UArgs s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 272) (aSt s₀ + BitVec.ofNat 32 288) (aSc s₀) (aR s₀)
    (b1Of (aC s₀) (aL s₀))
  ctx : ACtx s₀ s
  ebp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))
  mem : s.mem = m4 s₀

theorem absorbPre_wp {s₀ : State} (hp : APre s₀) : WP isa absorbPre s₀ (AMid₁ s₀) := by
  have hL := hp.lt
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  unfold absorbPre
  refine WP.seq (WP.mono (absSave_wp hp) fun s₁ ⟨c₁, m₁⟩ => ?_)
  refine WP.seq (held_ok (r := .eax) (by decide) (by decide) c₁.esp (by rw [c₁.rd, c₁.wr]; exact hp.arg_in (by decide))
    (by rw [c₁.rd, c₁.wr]; exact hp.arg_in (by decide)) (c₁.args 2 (by decide)) (c₁.args 3 (by decide))
    fun s₂ eax₂ g₂ m₂ rd₂ wr₂ => ?_)
  have c₂ : ACtx s₀ s₂ := ⟨by rw [g₂ _ (by decide) (by decide), c₁.esp], by rw [rd₂, c₁.rd], by rw [wr₂, c₁.wr],
    by rw [m₂]; exact c₁.args⟩
  refine WP.seq (WP.mono (fill_wp hp c₂ eax₂) fun s₃ h₃ => ?_)
  have p288 : 0 < fOf (aC s₀) (aL s₀) → (aSt s₀ + BitVec.ofNat 32 (288 + held (aC s₀))).setWidth 64 =
      (aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)) := fun _ => add_setWidth (by omega)
  refine WP.seq (WP.mono (copy_wp (L := fOf (aC s₀) (aL s₀)) (by omega) h₃.esi h₃.edi h₃.ecx (fun _ => by omega)
    (fun _ => by rw [add_toNat (by omega)]; omega)
    (fun _ => by
      rw [h₃.ctx.rd, h₃.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨adR s₀, by simp, 0, by simp, by simp; omega⟩)
    (fun h0 => by
      rw [h₃.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨astR s₀, by simp, 288 + held (aC s₀), p288 h0, by simp; omega⟩)
    (fun h0 => by
      rw [p288 h0]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 288 + held (aC s₀)) (n := fOf (aC s₀) (aL s₀)) _
        (by omega))).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  obtain ⟨m₄, g₄, rd₄, wr₄⟩ := h₄
  have hm₄ : s₄.mem = m4 s₀ := by
    rw [m₄, h₃.mem, m₂, m₁, m4]
    by_cases hf0 : fOf (aC s₀) (aL s₀) = 0
    · rw [hf0]; simp only [Spec.Aes.bytesAt, List.range_zero, List.map_nil, writeBytes_nil]
    · rw [p288 (by omega)]
  have c₄ : ACtx s₀ s₄ := ACtx.of_frame hp (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ctx.esp])
    (by rw [rd₄, h₃.ctx.rd]) (by rw [wr₄, h₃.ctx.wr]) (hm₄ ▸ m4_big hp)
  refine WP.mono (chain1_wp hp c₄ (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ebp]))
    fun s₅ h₅ => ⟨h₅.args, h₅.ctx, by rw [h₅.ebp, g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ebp],
      by rw [h₅.mem, hm₄]⟩

/-! ## After the calls -/

/-- What is known after a call. -/
structure AAft (s₀ : State) (v : Nat) (s : State) : Prop where
  ctx : ACtx s₀ s
  ebp : s.gpr .ebp = BitVec.ofNat 32 v
  frame : Frame (ABig s₀) s₀.mem s.mem

/-- A call of `vg_cmac_aes_update` keeps `AAft`. -/
theorem upd_aft {s₀ s s' : State} (hp : APre s₀) {Dd : BitVec 32} {n v : Nat}
    (hf : Frame (ABig s₀) s₀.mem s.mem) (hc : ACtx s₀ s) (hbp : s.gpr .ebp = BitVec.ofNat 32 v)
    (h : UPost s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 272) Dd (aSc s₀) (aR s₀) n s') : AAft s₀ v s' := by
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fr := h.frame
  rw [hc.esp, add_setWidth (by omega)] at fr
  have F : Frame (ABig s₀) s₀.mem s'.mem := hf.trans (fr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  exact ⟨ACtx.of_frame hp (by rw [h.saved .esp (by simp [calleeSaved]), hc.esp]) (by rw [h.rd, hc.rd])
    (by rw [h.wr, hc.wr]) F, by rw [h.saved .ebp (by simp [calleeSaved]), hbp], F⟩

theorem call1_after {s₀ s : State} (hp : APre s₀) (h : AMid₁ s₀ s) :
    WP isa (call6 ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86.update v.callee)) s (AAft s₀ (fOf (aC s₀) (aL s₀))) :=
  WP.mono ((upd_call v) h.args) fun _ h' => upd_aft hp (h.mem ▸ m4_big hp) h.ctx h.ebp h'

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ s : State) : Prop where
  args : UArgs s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 272) (d2Of s₀) (aSc s₀) (aR s₀) (nbOf (aC s₀) (aL s₀))
  aft : AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) s

theorem chain2_mid {s₀ s : State} (hp : APre s₀) (h : AAft s₀ (fOf (aC s₀) (aL s₀)) s) :
    WP isa chain2 s fun s' => AMid₂ s₀ s' ∧ s'.mem = s.mem :=
  WP.mono (chain2_wp hp h.ctx h.ebp) fun _ h' => ⟨⟨h'.args, h'.ctx, h'.ebp, h'.mem ▸ h.frame⟩, h'.mem⟩

theorem call2_after {s₀ s : State} (hp : APre s₀) (h : AMid₂ s₀ s) :
    WP isa (call6 ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86.update v.callee)) s
      (AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀))) :=
  WP.mono ((upd_call v) h.args) fun _ h' => upd_aft hp h.aft.frame h.aft.ctx h.aft.ebp h'

end VG.Proof.CmacAes.Stream.X86
