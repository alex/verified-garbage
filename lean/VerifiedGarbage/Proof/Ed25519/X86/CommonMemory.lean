import VerifiedGarbage.Proof.Ed25519.X86.CommonContract
import VerifiedGarbage.Impl.Ed25519.X86.CommonMemory

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem abiSave_ok {s₀ : State} {scidx argc : Nat} (hp : ScratchPre s₀ scidx argc) : WP isa (.block (abiSave scidx)) s₀ (Saved s₀ (arg s₀ scidx)) := by
  have hfit := hp.fit
  unfold abiSave
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * scidx) rfl (hp.argIn hp.index) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ scidx := u₁.gpr
  have inW : ∀ {s : State} {d : Nat}, s.wr = s₀.wr → d + 4 ≤ 8192 → InRegions s.wr (addr (arg s₀ scidx) d) 4 :=
    fun hw hd => ⟨_, hw ▸ hp.wr, scR_contains hfit hd (by decide)⟩
  refine Wp.wp_stm ea (inW u₁.wr (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.gpr]; exact ea) (inW (by rw [u₂.wr, u₁.wr]) (by decide)) fun s₃ u₃ => ?_
  refine Wp.wp_stm (by rw [u₃.gpr, u₂.gpr]; exact ea) (inW (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide))
    fun s₄ u₄ => ?_
  refine Wp.wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact ea)
    (inW (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have hr : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  have w : ∀ {m : Mem} {d : Nat} (v : BitVec 32), d + 4 ≤ 8192 →
      Frame [scR 8192 (arg s₀ scidx)] s₀.mem m → Frame [scR 8192 (arg s₀ scidx)] s₀.mem (m.writeW (addr (arg s₀ scidx) d) v) :=
    fun v hd hf => hf.writeW (List.mem_singleton_self _) _ (scR_contains hfit hd (by decide))
  refine ⟨by rw [u₆.gpr, g₅, ea], by rw [u₆.other _ (by decide), g₅, hr _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    ?_, fun j hj => ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact w _ (by decide) (w _ (by decide) (w _ (by decide) (w _ (by decide) (Frame.refl _ _))))
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have hne : ∀ a b : Nat, a < 4 → b < 4 → a ≠ b → 4 * a + 4 ≤ 4 * b ∨ 4 * b + 4 ≤ 4 * a :=
      fun a b ha hb h => by omega_using [ha, hb, h]
    have ne : ∀ (m : Mem) (v : BitVec 32) (a : Nat), a < 4 → a ≠ j →
        wd (m.writeW (addr (arg s₀ scidx) (4 * a)) v) (arg s₀ scidx) (4 * j) = wd m (arg s₀ scidx) (4 * j) :=
      fun m v a ha h => wd_write_ne m v (by omega_using [hfit, hj]) (by omega_using [hfit, ha])
        (hne j a hj ha (Ne.symm h))
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rw [ne _ _ 3 (by decide) (by decide), ne _ _ 2 (by decide) (by decide),
        ne _ _ 1 (by decide) (by decide), show 4 * 0 = 0 from rfl, wd_write_self, hr _ (by decide)]
      rfl
    · rw [ne _ _ 3 (by decide) (by decide), ne _ _ 2 (by decide) (by decide),
        show 4 * 1 = 4 from rfl, wd_write_self, u₂.gpr, hr _ (by decide)]
      rfl
    · rw [ne _ _ 3 (by decide) (by decide), show 4 * 2 = 8 from rfl, wd_write_self, u₃.gpr, u₂.gpr,
        hr _ (by decide)]
      rfl
    · rw [show 4 * 3 = 12 from rfl, wd_write_self, u₄.gpr, u₃.gpr, u₂.gpr, hr _ (by decide)]
      rfl


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

theorem restore_eq : restore = [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 0)), .mov .esi (.mem (at_ .eax 4)),
    .mov .ebp (.mem (at_ .eax 12)), .mov .edi (.mem (at_ .eax 8))] := rfl

/-- The saved registers restored. -/
theorem abiRestore_regs_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block restore) s fun s' => s'.mem = s.mem ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebx = wd s.mem x 0 ∧ s'.gpr .esi = wd s.mem x 4 ∧ s'.gpr .ebp = wd s.mem x 12 ∧
      s'.gpr .edi = wd s.mem x 8 ∧ s'.gpr .edx = s.gpr .edx ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = x := by rw [u₁.gpr, hc.edi]
  have inr : ∀ {s' : State} (d : Nat), s'.rd = s.rd → s'.wr = s.wr → d + 4 ≤ 8192 →
      InRegions (s'.rd ++ s'.wr) (addr x d) 4 := fun d h1 h2 hd => by rw [h1, h2]; exact hc.inRW hd (by decide)
  refine Wp.wp_ldm ea (inr 0 u₁.rd u₁.wr (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_ldm (by rw [u₂.other _ (by decide), ea]) (inr 4 (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    (by decide)) fun s₃ u₃ => ?_
  refine Wp.wp_ldm (by rw [u₃.other _ (by decide), u₂.other _ (by decide), ea])
    (inr 12 (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun s₄ u₄ => ?_
  refine Wp.wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ea])
    (inr 8 (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by decide))
    fun s₅ u₅ => WP.block_nil ?_
  refine ⟨by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem abiRestore_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block restore) s fun s' => s'.mem = s.mem ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebx = wd s.mem x 0 ∧ s'.gpr .esi = wd s.mem x 4 ∧ s'.gpr .ebp = wd s.mem x 12 ∧
      s'.gpr .edi = wd s.mem x 8 :=
  WP.mono (abiRestore_regs_ok hc) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem loadArg_ok {s₀ s : State} {scidx argc i : Nat} (hp : ScratchPre s₀ scidx argc)
    (h : Saved s₀ (arg s₀ scidx) s) (hi : i < argc) :
    WP isa (.block [.mov .esi (.mem (at_ .esp (4 + 4 * i)))]) s fun t =>
      Saved s₀ (arg s₀ scidx) t ∧ t.gpr .esi = arg s₀ i ∧ t.mem = s.mem := by
  refine Wp.wp_ldm h.esp (by rw [h.rd, h.wr]; exact hp.argIn hi) fun t ht => WP.block_nil ?_
  refine ⟨⟨(ht.other _ (by decide)).trans h.edi, (ht.other _ (by decide)).trans h.esp,
    ht.rd.trans h.rd, ht.wr.trans h.wr, by rw [ht.mem]; exact h.frame,
    fun j hj => by rw [ht.mem]; exact h.saved j hj⟩, ?_, ht.mem⟩
  rw [ht.gpr]; exact hp.arg_same h.frame hi

end VG.Proof.Ed25519.X86
