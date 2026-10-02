import VerifiedGarbage.Proof.AesGcm.X86.OneEntry
import VerifiedGarbage.Proof.AesGcm.X86.J0

/-!
# AES-GCM on x86: `J₀` and the additional data of `seal` and `open`

Untrusted: everything here is checked by Lean. `oneAad` (`oneAad_pc`):
`J₀` and the first counter block (`j0`), then the additional data absorbed
(`absorb 16`) and padded (`flush 16`), all within `oF p`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32)
open VG.Proof.Gcm (Absorbed)

/-- After `oneAad`: `J₀`, the additional data absorbed and padded, and the
first counter block. -/
structure OAad (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  j : blockAt s.mem (w64 (stOf (p.2 8))) =
    Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat)
  y : Absorbed s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat ++ zeros (padLen (p.2 5).toNat))
  cb : blockAt s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat))

/-- What holds between the pieces of `oneAad`: `J₀` and the first counter
block written, within `oF p` since `sE`. -/
structure OJ (p : BitVec 32 × (Nat → BitVec 32)) (sE s₀ s : State) : Prop where
  ent : OEnt p s₀ sE
  o : OEnv p s₀ s
  fr : Frame (oF p) sE.mem s.mem
  j : blockAt s.mem (w64 (stOf (p.2 8))) =
    Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat)
  cb : blockAt s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat))

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- The arguments of a piece from two kept slots: `dO := [so]`, `nO := [sl]`, `bO := 0`. -/
theorem setP_ok {so sl : Nat} (h₁ : 128 ≤ so) (h₂ : so + 4 ≤ 240) (h₃ : 128 ≤ sl) (h₄ : sl + 4 ≤ 240)
    {s : State} (he : Env (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 s) :
    ∃ s', runBlock isa [.mov .eax (slot so), .store (at_ .ebp dO) .eax, .mov .eax (slot sl),
        .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax] s = some s' ∧
      slotv s'.mem (p.2 8) dO = slotv s.mem (p.2 8) so ∧ slotv s'.mem (p.2 8) nO = slotv s.mem (p.2 8) sl ∧
      slotv s'.mem (p.2 8) bO = 0 ∧ Frame [pslotR (p.2 8)] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have L := G.L
  have ho : so < 2560 := by omega
  have hl : sl < 2560 := by omega
  have r₁ := he.wIn' (d := so) (n := 4) (by omega)
  have r₂ := he.wIn' (d := sl) (n := 4) (by omega)
  have e₁ : (s.mem.writeW (w64 (p.2 8) + BitVec.ofNat 64 dO) (s.mem.readW (w64 (p.2 8) + BitVec.ofNat 64 so) 32)).readW
      (w64 (p.2 8) + BitVec.ofNat 64 sl) 32 = s.mem.readW (w64 (p.2 8) + BitVec.ofNat 64 sl) 32 :=
    readW_writeW_off _ _ _ (by simp only [dO]; omega) (by omega) (by decide)
  refine ⟨_, by xrun [he.ebp, L.aW ho, L.aW hl, L.aW, he.wIn, r₁, r₂, e₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq]
  · mems [slotv_eq]; rfl
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

/-- `bO := [sl] mod 16`. -/
theorem setB_ok {sl : Nat} (h₃ : 128 ≤ sl) (h₄ : sl + 4 ≤ 240) {s : State}
    (he : Env (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 s) :
    ∃ s', runBlock isa [.mov .eax (slot sl), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax] s = some s' ∧
      slotv s'.mem (p.2 8) bO = BitVec.ofNat 32 ((slotv s.mem (p.2 8) sl).toNat % 16) ∧
      Frame [pslotR (p.2 8)] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have L := G.L
  have hl : sl < 2560 := by omega
  have r₂ := he.wIn' (d := sl) (n := 4) (by omega)
  have hand := and15 (s.mem.readW (w64 (p.2 8) + BitVec.ofNat 64 sl) 32)
  refine ⟨_, by xrun [he.ebp, L.aW hl, L.aW, he.wIn, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (Frame.refl _ _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

theorem j0Frame_oF : ∀ r ∈ j0Frame (stOf (p.2 8)) (p.2 8) p.1 28, ∃ r' ∈ oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st0_sub_oF G (by decide)
  · exact w_sub_oF (by decide) (by decide)
  · exact ws_sub_oF
  · exact stk_sub_oF

theorem absFrame_oF : ∀ r ∈ absFrame (stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oF G (by decide)
  · exact st_sub_oF G (by decide)
  · exact ws_sub_oF
  · exact stk_sub_oF

theorem tFrame_oF : ∀ r ∈ tFrame (stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oF G (by decide)
  · exact w_sub_oF (by decide) (by decide)
  · exact ws_sub_oF
  · exact stk_sub_oF

/-- A block of the state that `absorb 16` and `flush 16` keep (`J₀`, the counter block). -/
theorem st_absFrame {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 80)) :
    ∀ r ∈ absFrame (stOf (p.2 8)) (p.2 8) p.1 28 16,
      (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega)).symm

theorem st_tFrame {d : Nat} (hd : d + 16 ≤ 16 ∨ (32 ≤ d ∧ d + 16 ≤ 80)) :
    ∀ r ∈ tFrame (stOf (p.2 8)) (p.2 8) p.1 28 16,
      (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega)).symm

theorem st_pslot {d : Nat} (hd : d + 16 ≤ 80) :
    ∀ r ∈ [pslotR (p.2 8)], (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

theorem oneAad_pc :
    Pc (fun (b : State × State) s => OEnt p b.1 s ∧ s = b.2) oneAad
      (fun b s' => OAad p b.1 s' ∧ Frame (oF p) b.2.mem s'.mem) := by
  have L := G.L
  have sW : (⟨w64 (stOf (p.2 8)), 80⟩ : Region).Sub ⟨w64 (p.2 8), 2560⟩ := by
    rw [stOf_w64 L.fw]; exact Lay.wSub (by decide)
  -- `J₀`.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      blockAt s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) = 0)
    (Pc.mono (Pc.lift (j0_pc L (D := p.2 2) (n := (p.2 3).toNat)) (fun _ s => s.mem) fun b s ⟨h, _⟩ =>
      ⟨⟨h.o.env, h.dO, by rw [h.nO, ofNat_toNat32], by rw [h.o.nlO, ofNat_toNat32], h.o.zO, (p.2 3).isLt,
        ⟨h.o.nIn, G.fn, G.n_w.sub_right sW, G.n_w, G.k_n⟩⟩, rfl⟩) (fun _ _ h => h)
      fun b s ⟨sE, ⟨h, hs⟩, ho, rd, wr⟩ => by
        subst hs
        exact ⟨⟨h, h.o.frameE G (Frame.oD (ho.frame.sub (j0Frame_oF G))) ho.env rd wr,
          ho.frame.sub (j0Frame_oF G), by rw [ho.j0, h.o.hk, h.iv], by rw [ho.cb, h.o.hk, h.iv]⟩, ho.y⟩) ?_
  -- The additional data's arguments.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      blockAt s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) = 0 ∧
      AbsIn (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 4) (p.2 5).toNat 0 s)
    (Pc.taint [.ebp] (fun b s ⟨h, y0⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := setP_ok G (so := aadO) (sl := alO) (by decide) (by decide)
      (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have fo : Frame (oF p) s.mem s'.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pslot_sub_oF
    have o' := h.o.frame G (Frame.oD fo) bp si sp rd wr
    refine ⟨⟨h.ent, o', h.fr.trans fo, by
        have e := blockAt_frame f (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j,
        by rw [blockAt_frame f (st_pslot G (by decide))]; exact h.cb⟩,
      by rw [blockAt_frame f (st_pslot G (by decide))]; exact y0, ⟨o'.env, by rw [d]; exact h.o.aadO,
        by rw [n, h.o.alO, ofNat_toNat32], by rw [bz]; rfl, by decide, (p.2 5).isLt,
        ⟨o'.aIn, G.fa, G.a_w.sub_right sW, G.a_w, G.k_a⟩⟩⟩
  -- Absorbed.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      Absorbed s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat))
    (Pc.mono (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (b := 0) (by decide) (p.2 5).isLt) (fun _ s => s.mem)
      fun b s ⟨_, _, ha⟩ => ⟨ha, rfl⟩) (fun _ _ h => h)
      fun b s' ⟨s, ⟨h, y0, _⟩, ho, rd, wr⟩ => ⟨⟨h.ent, h.o.frameE G
        (Frame.oD (ho.frame.sub (absFrame_oF G))) ho.env rd wr, h.fr.trans (ho.frame.sub (absFrame_oF G)), ?_, ?_⟩,
        ?_⟩) ?_
  · have := blockAt_frame ho.frame (st_absFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h.j
  · rw [blockAt_frame ho.frame (st_absFrame G (.inr ⟨by decide, by decide⟩))]; exact h.cb
  · have := ho.abs [] rfl (Proof.Gcm.absorbed_nil _ y0)
    rwa [List.nil_append, h.o.hk, h.o.aad] at this
  -- `bO`.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      Absorbed s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat) ∧
      slotv s.mem (p.2 8) bO = BitVec.ofNat 32 ((p.2 5).toNat % 16))
    (Pc.taint [.ebp] (fun b s ⟨h, ha⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bz, f, bp, si, sp, rd, wr⟩ := setB_ok G (sl := alO) (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have fo : Frame (oF p) s.mem s'.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pslot_sub_oF
    have o' := h.o.frame G (Frame.oD fo) bp si sp rd wr
    have hl := length_bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat
    refine ⟨⟨h.ent, o', h.fr.trans fo, by
        have e := blockAt_frame f (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j,
        by rw [blockAt_frame f (st_pslot G (by decide))]; exact h.cb⟩,
      ha.congr (blockAt_frame f (st_pslot G (by decide))) (bytesAt_frame f (fun r hr =>
        (st_pslot G (d := 32) (by decide) r hr).sub_left (Region.sub_prefix (by omega))) (by omega)),
      by rw [bz, h.o.alO]⟩
  -- Padded.
  refine Pc.mono (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := (p.2 5).toNat % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun b s ⟨h, _, hb⟩ => ⟨⟨h.o.env, hb⟩, rfl⟩) (fun _ _ h => h)
    fun b s' ⟨s, ⟨h, ha, _⟩, ho, rd, wr⟩ => ⟨⟨h.o.frameE G
      (Frame.oD (ho.frame.sub (tFrame_oF G))) ho.env rd wr, ?_, ?_, ?_⟩, h.fr.trans (ho.frame.sub (tFrame_oF G))⟩
  · have := blockAt_frame ho.frame (st_tFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h.j
  · have hl := length_bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat
    have := ho.abs _ (by rw [hl]) (by rw [h.o.hk]; exact ha)
    rwa [h.o.hk, hl] at this
  · rw [blockAt_frame ho.frame (st_tFrame G (.inr ⟨by decide, by decide⟩))]; exact h.cb

end

end VG.Proof.AesGcm.X86
