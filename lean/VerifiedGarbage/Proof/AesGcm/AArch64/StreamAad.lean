import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments, with `aad_len mod 16` bytes
buffered (`aadEntry_ok`); `absorb` takes the data into GHASH and touches
nothing else of the state (`aad_run`), for any additional data so far of
that length (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- After the entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} {Ctx St D W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hD : s.gpr .x3 = D) (hn : (s.gpr .x4).toNat = n) (hW : s.gpr .x5 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block aadEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x23 = D ∧ s'.gpr .x24 = BitVec.ofNat 64 n ∧
      s'.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧ s'.mem = savedMem s.mem W s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x5 hW hperm.w
  have hn' : s.gpr .x4 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x25₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x5, mov .x20 .x1, mov .x21 .x0, mov .x23 .x3, mov .x24 .x4, imm .x9 15,
        .logic .and .x .x25 .x2 .x9] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x23 = D ∧
      s₂.gpr .x24 = BitVec.ofNat 64 n ∧ s₂.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hSt]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hD]
    · simp [gpr_write, g₁, hn']
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x23₂, x24₂, x25₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W : Addr) : List Region := savedR W :: absFrame St W 16

/-- One run of `stream_aad`, for additional data `x` so far of `o` bytes modulo 16. -/
theorem aad_run (v : GcmImpl) {s : State} (hs : streamAadAArch64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .x2).toNat % 16) :
    WP isa (streamAad v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .x0)) x →
        Absorbed s'.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (x ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ∧
      Frame (aadFrame (s.gpr .x1) (s.gpr .x5)) s.mem s'.mem := by
  simp only [streamAadAArch64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hSt : s.gpr .x1 = St at *
  generalize hD : s.gpr .x3 = D at *
  generalize hn : (s.gpr .x4).toNat = n at *
  generalize hW : s.gpr .x5 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x4).isLt
  refine WP.seq (WP.mono (aadEntry_ok hCtx hSt hD hn hW perm)
    fun s₁ ⟨he₁, hk₁, x23₁, x24₁, x25₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have dS : ∀ (d k : Nat), d + k ≤ 80 → (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR W) :=
    fun d k h => L.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR W] s.mem m →
      Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (Spec.Gcm.ctxH s.mem Ctx) x →
      Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (Spec.Gcm.ctxH s.mem Ctx) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega))
  have hIn : AbsIn Ctx St W s.sp s₁.gpr (Spec.Gcm.ctxH s.mem Ctx) x D n ((s.gpr .x2).toNat % 16) s₁ :=
    ⟨he₁, hk₁, x23₁, x24₁, x25₁, hx, ⟨covers_mem (by rw [rd₁, wr₁, hrd]; simp), hlt, wd, dds, ddw⟩, hH⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) v hIn) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame (saved_absFrame L (.inr rfl))
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_, ?_⟩
  · rw [hm, ← hdat]; exact h₂.abs (hA _ fsv ha)
  · rw [hm]
    exact (fsv.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (h₂.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp (v : GcmImpl) {s : State} (hs : streamAadAArch64.pre s) :
    WP isa (streamAad v.callees) s fun s' => GprAbi s s' ∧ streamAadAArch64.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .x2).toNat % 16)).length % 16 = (s.gpr .x2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .x0)) i.2.1 i.2.2 [] ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .x1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .x0)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) [])
    (aad_run v hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .x2).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadAArch64] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww⟩ := hs'
  have dSt : ∀ r ∈ aadFrame (s.gpr .x1) (s.gpr .x5), ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .x1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .x1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .x1 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega) (by omega)
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub (by decide))
    · exact st_off 16 16 (by decide) (by omega)
    · exact st_off 32 16 (by decide) (by omega)
    · exact (dsw.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub (by decide))
  refine WP.mono (aad_run v hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.AArch64
