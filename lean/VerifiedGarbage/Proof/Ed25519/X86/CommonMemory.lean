import VerifiedGarbage.Proof.Ed25519.X86.CommonContract
import VerifiedGarbage.Impl.Ed25519.X86.CommonMemory

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem abiSave_ok {s₀ : State} {scidx argc : Nat} (hp : ScratchPre s₀ scidx argc) :
    WP isa (.block (abiSave scidx)) s₀ (Saved s₀ (arg s₀ scidx)) := by
  have hfit := hp.fit
  rw [show abiSave scidx = .mov .eax (.mem (at_ .esp (4 + 4 * scidx))) :: (Spill.saveCode .eax savedSlots ++
    ([.mov .edi (.reg .eax)] : List Instr)) from rfl]
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * scidx) rfl (hp.argIn hp.index) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ scidx := u₁.gpr
  refine Spill.save_ok savedSlots (fun p h => by
    rw [ea, u₁.wr]; exact ⟨_, hp.wr, scR_contains hfit (by have := savedSlots_bound p h; omega_using [this])
      (by decide)⟩) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = Spill.saveMem s₀.mem (addr (arg s₀ scidx)) s₀.gpr savedSlots := by
    rw [u₆.mem, u₅.mem, ea, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  refine ⟨by rw [u₆.gpr, u₅.gpr, ea], by rw [u₆.other _ (by decide), u₅.gpr, u₁.other _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₁.wr], ?_, ?_⟩
  · rw [hm]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      scR_contains hfit (by have := savedSlots_bound p h; omega_using [this]) (by decide)
  · rw [hm]; exact Spill.saveMem_saved_addr _ _ (n := 16) (by decide) (by omega_using [hfit])


structure CopyInv (x p : BitVec 32) (dst : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  frame : Frame [sub x dst (4 * n)] s₀.mem s.mem
  words : ∀ j < n, wd s.mem x (dst + 4 * j) = wd s₀.mem p (4 * j)

theorem copyWords_ok {x p : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (hp : s₀.gpr .esi = p) {dst N : Nat} (hd : dst + 4 * N ≤ 8192)
    (hi : ∀ j < N, InRegions (s₀.rd ++ s₀.wr) (addr p (4 * j)) 4)
    (hs : ∀ j < N, (sub p (4 * j) 4).Disjoint (sub x dst (4 * N))) :
    ∀ n ≤ N, WP isa (.block (copyWords dst n)) s₀ (CopyInv x p dst s₀ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    have he : copyWords dst (n + 1) = copyWords dst n ++
        ([.mov .eax (.mem (at_ .esi (4 * n))), .store (sc (dst + 4 * n)) .eax] : List Instr) := by
      simp only [copyWords, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [he]
    refine WP.block_append (WP.mono (copyWords_ok hc hp hd hi hs n (by omega_using [hn]))
      fun u hu => ?_)
    have cu := hu.keep.ctx hc
    refine Wp.wp_ldm (hu.keep.esi.trans hp) (by rw [hu.keep.rd, hu.keep.wr]; exact hi n (by omega_using [hn]))
      fun v hv => ?_
    have cv := (updKeep hv).ctx cu
    refine Wp.wp_stm cv.edi (cv.inW (by omega_using [hd, hn]) (by decide)) fun t ht => WP.block_nil ?_
    have et : t.mem = u.mem.writeW (addr x (dst + 4 * n)) (wd s₀.mem p (4 * n)) := by
      rw [ht.mem, hv.mem, hv.gpr]
      have hw : wd u.mem p (4 * n) = wd s₀.mem p (4 * n) :=
        wd_frame hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact (hs n (by omega_using [hn])).sub_right
            (sub_sub hc.fit (Nat.le_refl _) (by omega_using [hn]) (by omega_using [hd, hn]))
      exact congrArg (u.mem.writeW (addr x (dst + 4 * n))) hw
    refine ⟨hu.keep.trans ((updKeep hv).trans
      ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩), ?_, fun j hj => ?_⟩
    · rw [et]
      exact frame_write1 (frameWiden hu.frame hc.fit (Nat.le_refl _) (by omega_using [])
        (by omega_using [hd, hn])) hc.fit (by omega_using [hd, hn]) (by omega_using []) (by omega_using []) _
    · rw [et]
      by_cases e : j = n
      · subst e; exact wd_write_self _ _ _ _
      · rw [wd_write_ne _ _ (by have := hc.fit; omega_using [this, hd, hn, hj])
          (by have := hc.fit; omega_using [this, hd, hn]) (by omega_using [hj, e])]
        exact hu.words j (by omega_using [hj, e])

theorem restore_eq : restore =
    .mov .eax (.reg .edi) :: (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) := rfl

/-- The saved registers restored. -/
theorem abiRestore_ok {x : BitVec 32} {s : State} {g : Reg → BitVec 32} (hc : Ctx x s)
    (hs : Spill.Saved s.mem (addr x) g savedSlots) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = g r) ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.gpr .edx = s.gpr .edx ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = x := by rw [u₁.gpr, hc.edi]
  refine Spill.restore_ok (g := g) [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] (by decide)
    (fun p h => by
      rw [ea, u₁.rd, u₁.wr]
      exact hc.inRW (by have := savedSlots_bound p (by revert p h; decide); omega_using [this]) (by decide))
    (by rw [ea, u₁.mem]; exact hs.sub (by decide)) fun s' r => WP.block_nil
      ⟨fun q hq hsp => r.regs q (by revert hsp; revert hq; revert q; decide),
        by rw [r.other _ (by decide), u₁.other _ (by decide)],
        by rw [r.other _ (by decide), u₁.other _ (by decide)], by rw [r.mem, u₁.mem]⟩

theorem loadArg_ok {s₀ s : State} {scidx argc i : Nat} (hp : ScratchPre s₀ scidx argc)
    (h : Saved s₀ (arg s₀ scidx) s) (hi : i < argc) :
    WP isa (.block [.mov .esi (.mem (at_ .esp (4 + 4 * i)))]) s fun t =>
      Saved s₀ (arg s₀ scidx) t ∧ t.gpr .esi = arg s₀ i ∧ t.mem = s.mem := by
  refine Wp.wp_ldm h.esp (by rw [h.rd, h.wr]; exact hp.argIn hi) fun t ht => WP.block_nil ?_
  refine ⟨⟨(ht.other _ (by decide)).trans h.edi, (ht.other _ (by decide)).trans h.esp,
    ht.rd.trans h.rd, ht.wr.trans h.wr, by rw [ht.mem]; exact h.frame,
    by rw [ht.mem]; exact h.saved⟩, ?_, ht.mem⟩
  rw [ht.gpr]; exact hp.arg_same h.frame hi

end VG.Proof.Ed25519.X86
