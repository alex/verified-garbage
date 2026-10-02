import VerifiedGarbage.Proof.AesGcm.X86.OneAad
import VerifiedGarbage.Proof.AesGcm.X86.Cmp

/-!
# AES-GCM on x86: the data and the tag of `seal` and `open`

Untrusted: everything here is checked by Lean. `oneCrypt` (`oneCrypt_pc`):
the data XORed with the keystream from a counter block; and `oneTag o`
(`oneTag_pc`): the data absorbed and padded, then the tag into `W + o`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

theorem oneCrypt_eq : (oneCrypt vg.callees) = .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax,
    .mov .eax (slot lenO), .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax]) (crypt vg.callees) := rfl

theorem oneTag_eq (o : Nat) : (oneTag vg.callees) o = .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax,
    .mov .eax (slot lenO), .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax])
  (.seq (absorb vg.callees 16)
  (.seq (.block [.mov .eax (slot lenO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush vg.callees 16) (tag vg.callees o alO zO lenO zO)))) := rfl

/-- What GHASH has absorbed before the data: the additional data, padded. -/
abbrev xA (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat ++ zeros (padLen (p.2 5).toNat)

/-- `J₀`. -/
abbrev jOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Block :=
  Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat)

/-- Before `oneTag o`. -/
structure OTIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  j : blockAt s.mem (w64 (stOf (p.2 8))) = jOf p s₀
  y : Absorbed s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (w64 (p.2 0))) (xA p s₀)

/-- The regions `oneTag o` writes: the state's first three blocks, `T`, the
tag at `W + o`, the working space and the stack. -/
abbrev oT (p : BitVec 32 × (Nat → BitVec 32)) (o : Nat) : List Region :=
  [⟨w64 (p.2 8) + BitVec.ofNat 64 16, 48⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 96, 16⟩,
    ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩, wsR (p.2 8), below p.1 28]

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

omit G in
theorem pslot_oF {m m' : Mem} (f : Frame [pslotR (p.2 8)] m m') : Frame (oF p) m m' :=
  f.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pslot_sub_oF

theorem crFrame_oF : ∀ r ∈ crFrame (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat,
    ∃ r' ∈ ⟨w64 (p.2 6), (p.2 7).toNat⟩ :: oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact d_sub_oF
  · obtain ⟨r', h₁, h₂⟩ := st_sub_oF G (d := 48) (k := 32) (by decide)
    exact ⟨r', List.mem_cons_of_mem _ h₁, h₂⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The data, writable, for `crypt`. -/
theorem dataW_of {s₀ s : State} (h : OEnv p s₀ s) :
    DataW (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 28 s (p.2 6) (p.2 7).toNat :=
  ⟨⟨covers_left h.dIn, G.fd, G.d_w.sub_right (by rw [stOf_w64 G.L.fw]; exact Lay.wSub (by decide)), G.d_w, G.k_d⟩,
    h.dIn, G.c_d⟩

theorem oneCrypt_pc (icb : State → Block) :
    Pc (fun (b : State × State) s => (OEnv p b.1 s ∧
        CtrS s.mem (stOf (p.2 8)) (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (icb b.1) 0) ∧ s = b.2) (oneCrypt vg.callees)
      (fun b s' => OEnv p b.1 s' ∧
        bytesAt s'.mem (w64 (p.2 6)) (p.2 7).toNat =
          xorKs (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (icb b.1) 0 (bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat) ∧
        Frame (crFrame (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat) b.2.mem s'.mem) := by
  have L := G.L
  rw [oneCrypt_eq]
  refine Pc.seq (Q := fun b s₁ => OEnv p b.1 s₁ ∧
      CrIn (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 1).toNat (p.2 6) (p.2 7).toNat 0 s₁ ∧
      CtrS s₁.mem (stOf (p.2 8)) (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (icb b.1) 0 ∧
      Frame [pslotR (p.2 8)] b.2.mem s₁.mem)
    (Pc.taint [.ebp] (fun b s ⟨⟨h, hc⟩, hs⟩ => ?_) (fun _ _ s₁ s₂ ⟨⟨h₁, _⟩, _⟩ ⟨⟨h₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · subst hs
    obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := setP_ok G (so := dataO) (sl := lenO) (by decide) (by decide)
      (by decide) (by decide) h.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have o' := h.frame G (Frame.oD (pslot_oF f)) bp si sp rd wr
    refine ⟨o', ⟨o'.env, by rw [d]; exact h.dataO, by rw [n, h.lenO, ofNat_toNat32], by rw [bz]; rfl,
      (p.2 7).isLt, dataW_of G o', o'.rounds⟩, ?_, f⟩
    exact hc.congr (blockAt_frame f (st_pslot G (by decide))) (blockAt_frame f (st_pslot G (by decide)))
  refine Pc.mono (Pc.lift (Pc.forall fun (c : Block) => crypt_pc L rfl (R := (p.2 1).toNat) (D := p.2 6)
    (n := (p.2 7).toNat) (P := 0) (icb := c)) (fun _ s => s.mem) fun b s ⟨_, hi, _⟩ => ⟨hi, rfl⟩)
    (fun _ _ h => h) fun b s' ⟨s₁, ⟨h₁, hi, hc, f⟩, ho, rd, wr⟩ => ?_
  have hco := ho (icb b.1)
  have hf : Frame (⟨w64 (p.2 6), (p.2 7).toNat⟩ :: oF p) s₁.mem s'.mem := hco.frame.sub (crFrame_oF G)
  refine ⟨h₁.frameE G (Frame.oDD hf) hco.env rd wr, ?_, ?_⟩
  · have := hco.out (by rw [h₁.ciph]; exact hc)
    rwa [h₁.ciph, bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact G.d_w.sub_right (Lay.wSub (by decide))) (by have := G.fd; omega)] at this
  · exact (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (p.2 8), by simp, pslot_ws _⟩).trans hco.frame

theorem tagFrame_oF {o : Nat} : ∀ r ∈ tagFrame (stOf (p.2 8)) (p.2 8) p.1 o,
    ∃ r' ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have c : ∀ {r : Region}, (∃ r' ∈ oF p, Region.Sub r r') →
      ∃ r' ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p, Region.Sub r r' :=
    fun ⟨r', h₁, h₂⟩ => ⟨r', List.mem_cons_of_mem _ h₁, h₂⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact c (st0_sub_oF G (by decide))
  · exact c (w_sub_oF (by decide) (by decide))
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact c ws_sub_oF
  · exact c stk_sub_oF

omit G in
theorem wo_oFF {o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p) m m') : Frame (oFF p) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_cons.mp hr with rfl | hr
  · rcases ho with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [BitVec.add_zero]; exact fun _ h => h⟩
    · exact ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ h => h⟩

theorem OTIn.pslot {s₀ s s' : State} (h : OTIn p s₀ s) (f : Frame [pslotR (p.2 8)] s.mem s'.mem)
    (bp : s'.gpr .ebp = s.gpr .ebp) (si : s'.gpr .esi = s.gpr .esi) (sp : s'.gpr .esp = s.gpr .esp)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : OTIn p s₀ s' := by
  have hl : (xA p s₀).length % 16 = 0 := by
    simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine ⟨h.o.frame G (Frame.oD (pslot_oF f)) bp si sp rd wr, ?_, h.y.congr (blockAt_frame f (st_pslot G
    (by decide))) (by rw [hl]; rfl)⟩
  have e := blockAt_frame f (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j

theorem st_sub_oT {o d k : Nat} (h : d + k ≤ 48) :
    ∃ r' ∈ oT p o, Region.Sub ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, k⟩ r' := by
  rw [st_eq G]; exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩

theorem st0_sub_oT {o k : Nat} (h : k ≤ 48) : ∃ r' ∈ oT p o, Region.Sub ⟨w64 (stOf (p.2 8)), k⟩ r' := by
  rw [stOf_w64 G.L.fw]; exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩

omit G in
theorem pslot_oT {o : Nat} {m m' : Mem} (f : Frame [pslotR (p.2 8)] m m') : Frame (oT p o) m m' :=
  f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (p.2 8), by simp, pslot_ws _⟩

theorem absFrame_oT {o : Nat} : ∀ r ∈ absFrame (stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oT G (by decide)
  · exact st_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tFrame_oT {o : Nat} : ∀ r ∈ tFrame (stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tagFrame_oT {o : Nat} : ∀ r ∈ tagFrame (stOf (p.2 8)) (p.2 8) p.1 o, ∃ r' ∈ oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact st0_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

omit G in
theorem oT_oF {o : Nat} {m m' : Mem} (h : Frame (oT p o) m m') :
    Frame (⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p) m m' := by
  refine h.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The counter block, apart from what `oneTag o` writes. -/
theorem cb_oT {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ oT p o, (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  rw [st_eq G]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rcases ho with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (G.L.stk_w (by decide)).symm

theorem oneTag_pc {o : Nat} (ho : o = 0 ∨ o = 112) :
    Pc (fun (b : State × State) s => OTIn p b.1 s ∧ s = b.2) (oneTag vg.callees o)
      (fun b s' => OEnv p b.1 s' ∧
        bytesAt s'.mem (w64 (p.2 8) + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom (ctxH b.1.mem (w64 (p.2 0))) (ghash (ctxH b.1.mem (w64 (p.2 0)))
            (blocks (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat ++
              zeros (padLen (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length))))
            [ofBytes (lensBlock (p.2 5).toNat (p.2 7).toNat)] ^^^
            ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat (jOf p b.1)) ∧
        Frame (oT p o) b.2.mem s'.mem) := by
  have L := G.L
  have hl : ∀ s₀, (xA p s₀).length % 16 = 0 := fun s₀ => by
    simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  rw [oneTag_eq]
  -- The data's arguments.
  refine Pc.seq (Q := fun b s₁ => OTIn p b.1 s₁ ∧
      AbsIn (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat 0 s₁ ∧
      Frame [pslotR (p.2 8)] b.2.mem s₁.mem)
    (Pc.taint [.ebp] (fun b s ⟨h, hs⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · subst hs
    obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := setP_ok G (so := dataO) (sl := lenO) (by decide) (by decide)
      (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have h' := h.pslot G f bp si sp rd wr
    exact ⟨h', ⟨h'.o.env, by rw [d]; exact h.o.dataO, by rw [n, h.o.lenO, ofNat_toNat32], by rw [bz]; rfl,
      by decide, (p.2 7).isLt, (dataW_of G h'.o).ok⟩, f⟩
  -- Absorbed.
  refine Pc.seq (Q := fun b s₂ => OEnv p b.1 s₂ ∧
      blockAt s₂.mem (w64 (stOf (p.2 8))) = jOf p b.1 ∧
      Absorbed s₂.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat) ∧
      Frame (oT p o) b.2.mem s₂.mem)
    (Pc.mono (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (b := 0) (by decide) (p.2 7).isLt) (fun _ s => s.mem)
      fun b s ⟨_, ha, _⟩ => ⟨ha, rfl⟩) (fun _ _ h => h)
      fun b s₂ ⟨s₁, ⟨h₁, _, f⟩, ho, rd, wr⟩ => ⟨h₁.o.frameE G
        (Frame.oD (ho.frame.sub (absFrame_oF G))) ho.env rd wr, ?_, ?_,
        (pslot_oT f).trans (ho.frame.sub (absFrame_oT G))⟩) ?_
  · have := blockAt_frame ho.frame (st_absFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h₁.j
  · have := ho.abs (xA p b.1) (hl b.1) (by rw [h₁.o.hk]; exact h₁.y)
    rwa [h₁.o.hk, bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact G.d_w.sub_right (Lay.wSub (by decide))) (by have := G.fd; omega)] at this
  -- `bO`.
  refine Pc.seq (Q := fun b s₃ => OEnv p b.1 s₃ ∧
      blockAt s₃.mem (w64 (stOf (p.2 8))) = jOf p b.1 ∧
      Absorbed s₃.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat) ∧
      Frame (oT p o) b.2.mem s₃.mem ∧ slotv s₃.mem (p.2 8) bO = BitVec.ofNat 32 ((p.2 7).toNat % 16))
    (Pc.taint [.ebp] (fun b s₂ ⟨h₂, hj, ha, f⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bz, f', bp, si, sp, rd, wr⟩ := setB_ok G (sl := lenO) (by decide) (by decide) h₂.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have hx : (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length % 16 < 16 :=
      Nat.mod_lt _ (by decide)
    refine ⟨h₂.frame G (Frame.oD (pslot_oF f')) bp si sp rd wr, ?_,
      ha.congr (blockAt_frame f' (st_pslot G (by decide))) (bytesAt_frame f' (fun r hr =>
        (st_pslot G (d := 32) (by decide) r hr).sub_left (Region.sub_prefix (by omega))) (by omega)),
      f.trans (pslot_oT f'), by rw [bz, h₂.lenO]⟩
    have e := blockAt_frame f' (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact hj
  -- Padded.
  refine Pc.seq (Q := fun b s₄ => OEnv p b.1 s₄ ∧
      blockAt s₄.mem (w64 (stOf (p.2 8))) = jOf p b.1 ∧
      Absorbed s₄.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat ++
          zeros (padLen (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length)) ∧
      Frame (oT p o) b.2.mem s₄.mem)
    (Pc.mono (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := (p.2 7).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun _ s => s.mem) fun b s ⟨h, _, _, _, hb⟩ => ⟨⟨h.env, hb⟩, rfl⟩) (fun _ _ h => h)
      fun b s₄ ⟨s₃, ⟨h₃, hj, ha, f, _⟩, ho, rd, wr⟩ => ⟨h₃.frameE G
        (Frame.oD (ho.frame.sub (tFrame_oF G))) ho.env rd wr, ?_, ?_, f.trans (ho.frame.sub (tFrame_oT G))⟩) ?_
  · have := blockAt_frame ho.frame (st_tFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact hj
  · have hx : (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length % 16 = (p.2 7).toNat % 16 := by
      rw [List.length_append, length_bytesAt]; have := hl b.1; omega
    have := ho.abs _ hx (by rw [h₃.hk]; exact ha)
    rwa [h₃.hk] at this
  -- The tag.
  refine Pc.mono (Pc.lift (tag_pc L ho (.inr (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)) (R := (p.2 1).toNat) (alo := p.2 5)
    (ahi := 0) (tlo := p.2 7) (thi := 0)) (fun _ s => s.mem)
    fun b s ⟨h, _, _, _⟩ => ⟨⟨h.env, ⟨h.alO, h.zO, h.lenO, h.zO⟩, h.rounds⟩, rfl⟩) (fun _ _ h => h)
    fun b s₅ ⟨s₄, ⟨h₄, hj, ha, f⟩, ho', rd, wr⟩ => ⟨h₄.frameE G
      (wo_oFF ho (ho'.frame.sub (tagFrame_oF G))) ho'.env rd wr, ?_,
      f.trans (ho'.frame.sub (tagFrame_oT G))⟩
  have hX : (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat ++
      zeros (padLen (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  rw [ho'.out, h₄.hk, h₄.ciph, hj, Proof.Gcm.Absorbed.whole_eq ha hX]
  simp only [val64, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]

end

end VG.Proof.AesGcm.X86
