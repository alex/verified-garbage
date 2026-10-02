import VerifiedGarbage.Proof.AesGcm.X86.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86.Cmp

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. The entry (`finEntry_pc`,
keeping `tag_len` too), the tag length checked (`tagLenOk_pc`), and then
either the tag zeroed or the received tag copied (`recv_ok`), the tag
computed (`finTag_pc`), compared (`cmp_ok`) and masked (`mask_ok`), as one
`Pc` (`streamVerify_pc`): correct (`streamVerify_correct`) and constant time
(`streamVerify_ct`). Only the lengths, the pointers and `rounds` affect the
branches: the comparison and the mask have none.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph fullTag zeros)

theorem streamVerify_eq : streamVerify = .seq (entry 7 ([.mov .esi (argOp 2)] ++
    ((finKeeps ++ [(8, tglO)]).flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ [])))
    (.seq tagLenOk (.seq (.ite .e (.block (zero4 0))
      (.seq recv (.seq (finTag 0) (.seq (cmp 0) (.block mask))))) (.block restore))) := rfl

/-- Where the received tag is copied. -/
abbrev rR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 rO, 16⟩

/-- The kept values, after the received tag is copied. -/
theorem FinIn.frameR {Ctx St W SP : BitVec 32} {R : Nat} {al ah xl xh : BitVec 32} {s s' : State}
    (h : FinIn Ctx St W SP R al ah xl xh s) (hf : Frame [rR W] s.mem s'.mem) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    FinIn Ctx St W SP R al ah xl xh s' := by
  have sl : ∀ o, o + 4 ≤ rO → slotv s'.mem W o = slotv s.mem W o := fun o ho => by
    have ho' : o + 4 ≤ 196 := ho
    rw [slotv_eq, slotv_eq]
    exact slot_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl ho') (by omega) (by decide)
  have hc := sl ctxO (by decide)
  rw [slotv_eq, slotv_eq] at hc
  exact ⟨h.env.keep hbp hsi hsp hrd hwr hc, by rw [sl _ (by decide)]; exact h.al, by rw [sl _ (by decide)]; exact h.ah,
    by rw [sl _ (by decide)]; exact h.xl, by rw [sl _ (by decide)]; exact h.xh,
    ⟨by rw [sl _ (by decide)]; exact h.rounds.1, h.rounds.2⟩⟩

/-- The exit of `verify`, after the pieces wrote within `rR W :: tagFrame St W SP 0`. -/
theorem fin_exitR {nA : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : FinEnt nA p s₀ s₁)
    (L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28) (he : Env (p.2 0) (p.2 2) (p.2 7) p.1 s)
    (hf : Frame (rR (p.2 7) :: tagFrame (p.2 2) (p.2 7) p.1 0) s₁.mem s.mem) (hnA : 8 ≤ nA) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax := by
  have esp := pubOf_esp h₁.pub
  have hp := h₁.pre
  have a : ∀ i, i < nA → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  have r_s := hp.r_s
  have r_w := hp.r_w
  have sp := hp.sp
  rw [esp, a 2 (by omega)] at r_s
  rw [esp, a 7 (by omega)] at r_w
  rw [esp] at sp
  have hsv : SavedAt s.mem (p.2 7) s₀ := h₁.saved.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have rT : ∀ r ∈ rR (p.2 7) :: tagFrame (p.2 2) (p.2 7) p.1 0, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_s.sub_right (Region.sub_prefix (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact ret_below sp
  have rE : ∀ r ∈ [(⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf rT, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, m', ax⟩

/-- A word of `W` outside the regions the tag is computed in. -/
theorem slot_tagFrame {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28) {m m' : Mem}
    (hf : Frame (tagFrame St W SP 0) m m') {o : Nat} (h₁ : 128 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m' W o = slotv m W o := by
  rw [slotv_eq, slotv_eq]
  refine slot_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := o) (k := 4) (by decide) (.inr ⟨by omega, by omega⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

/-- The received tag, outside the regions the tag is computed in. -/
theorem rR_tagFrame {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28) :
    ∀ r ∈ tagFrame St W SP 0, (rR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := 196) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The first bytes of `W`, outside a region further on. -/
theorem w0_disj {W : BitVec 32} {n d k : Nat} (hn : n ≤ d) (hd : d + k ≤ 2560) :
    (⟨w64 W, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := by
  have := Lay.w_w (W := W) (a := 0) (n := n) (d := d) (k := k) (.inl (by omega)) (by omega) hd
  rwa [BitVec.add_zero] at this

/-- After the entry and the tag length checked. -/
structure VT (p : BitVec 32 × (Nat → BitVec 32)) (ok : Bool) (s₀ s₁ s : State) : Prop where
  ent : FinEnt 9 p s₀ s₁
  fin : FinIn (p.2 0) (p.2 2) (p.2 7) p.1 (p.2 1).toNat (p.2 3) (p.2 4) (p.2 5) (p.2 6) s
  mem : s.mem = s₁.mem
  tgl : slotv s.mem (p.2 7) tglO = BitVec.ofNat 32 (p.2 8).toNat
  zf : s.zf = some (!ok)

/-- What `verify` ends with, before restoring our caller's registers. -/
def VOut (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop :=
  ∃ s₁, FinEnt 9 p s₀ s₁ ∧ Env (p.2 0) (p.2 2) (p.2 7) p.1 s ∧
    Frame (rR (p.2 7) :: tagFrame (p.2 2) (p.2 7) p.1 0) s₁.mem s.mem ∧ streamVerifyX86.post s₀ s

theorem streamVerify_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => verifyPre s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀) streamVerify
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamVerifyX86.post s₀ s') := by
  by_cases hex : ∃ s₀, verifyPre s₀ ∧ pubOf 9 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28 := by
    have := (verifyPre_of hz).lay
    rwa [pubOf_arg hzp (i := 0) (by decide), pubOf_arg hzp (i := 2) (by decide),
      pubOf_arg hzp (i := 7) (by decide), pubOf_esp hzp] at this
  have hR : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14 := by
    have := (verifyPre_of hz).rounds; rwa [roundsOk, pubOf_arg hzp (i := 1) (by decide)] at this
  generalize hok : Spec.Gcm.tagLenOk (p.2 8).toNat = ok
  have ht32 : (p.2 8).toNat < 2 ^ 32 := (p.2 8).isLt
  rw [streamVerify_eq]
  -- The entry, then the tag length.
  refine Pc.seq (finEntry_pc 9 (by decide) [(8, tglO)] (by decide) (by decide) verifyPre
    (fun _ h => verifyPre_of h) p (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => ∃ s₁, VT p ok s₀ s₁ s) (Pc.mono (Pc.lift (tagLenOk_pc (W := p.2 7) ht32)
    (fun _ s => s) fun s₀ s ⟨h, hv⟩ => ⟨rfl, h.fin.env.ebp, L.aW (by decide), h.fin.env.wIn' (by decide), by
      rw [hv (8, tglO) (by simp), pubOf_arg h.pub (by decide), ofNat_toNat32]⟩) (fun _ _ h => h)
    fun s₀ s ⟨s₁, ⟨h₁, hv⟩, ⟨tl, hz⟩, _, _⟩ => ⟨s₁, h₁, h₁.fin.keep (by rw [tl.other _ (by decide) (by decide)])
      (by rw [tl.other _ (by decide) (by decide)]) (by rw [tl.other _ (by decide) (by decide)]) tl.mem tl.rd tl.wr,
      tl.mem, by rw [tl.mem, hv (8, tglO) (by simp), pubOf_arg h₁.pub (by decide), ofNat_toNat32], by
        rw [hz, hok]⟩) ?_
  refine Pc.seq (Q := VOut p) (Pc.ite (!ok) (fun _ _ ⟨_, h⟩ => h.zf) (fun hb => ?_) (fun hb => ?_)) ?_
  -- A tag length §5.2.1.2 does not allow: the tag zeroed.
  · have hf : ok = false := by simpa using hb
    refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.fin.env.ebp, h₂.fin.env.ebp]) (by taint_decide)
    have he := h.fin.env
    have hz := zero4_fold s.mem (p.2 7) 0
    simp only [Nat.reduceAdd] at hz
    have fz : Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 0, 16⟩] s.mem (Cmac.zero4 s.mem (w64 (p.2 7) + BitVec.ofNat 64 0)) :=
      Cmac.frame_store4 _ _ _ _ _
    refine WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, L.aW, he.wIn, hz], ?_⟩
    refine ⟨s₁, h.ent, he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) ?_, ?_, ?_⟩
    · mems [hz]
      exact slot_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (a := 144) (n := 4) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    · mems [hz]
      rw [← h.mem]
      refine Frame.mono fz fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; simp
    · simp only [streamVerifyX86, ret32_eq]
      intro iv a c _ _ _
      have e : Spec.Gcm.tagLenOk (arg s₀ 8).toNat = false := by rw [pubOf_arg h.ent.pub (by decide), hok, hf]
      simp only [e, Bool.false_eq_true, false_and, ↓reduceIte]
      mems [hz]
      rw [pubOf_arg h.ent.pub (by decide)]
      refine ⟨rfl, ?_⟩
      have := zero4_bytes' s.mem (w64 (p.2 7) + BitVec.ofNat 64 0)
      rw [BitVec.add_zero] at this ⊢
      exact this
  -- An allowed one: the tags compared.
  · have hT : ok = true := by simpa using hb
    have ht := hok
    rw [hT] at ht
    have ht' : 1 ≤ (p.2 8).toNat ∧ (p.2 8).toNat ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ht
      omega
    obtain ⟨t1, t16⟩ := ht'
    -- The received tag copied.
    refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 7) s ∧ slotv s.mem (p.2 7) tglO = BitVec.ofNat 32 (p.2 8).toNat)
      (R := fun s s' => bytesAt s'.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16 =
          bytesAt s.mem (w64 (p.2 7)) (p.2 8).toNat ++ zeros (16 - (p.2 8).toNat) ∧
        Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
        s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
      (fun s hs => recv_ok hs.1 hs.2 t1 t16) (recv_ct fun s hs => hs) _
      (fun s₀ s ⟨s₁, h⟩ => ⟨⟨h.fin.env.ebp, h.fin.env.wW, L.fw⟩, h.tgl⟩)) ?_
    -- The tag computed.
    refine Pc.seq (Pc.lift (finTag_pc L (R := (p.2 1).toNat) (o := 0) (.inl rfl) (al := p.2 3) (ah := p.2 4)
      (xl := p.2 5) (xh := p.2 6)) (fun _ s => s.mem)
      fun s₀ s' ⟨s, ⟨s₁, h⟩, _, f, g1, g2, g3, rd, wr⟩ => ⟨h.fin.frameR f g1 g2 g3 rd wr, rfl⟩) ?_
    -- Compared.
    refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 7) s ∧ slotv s.mem (p.2 7) tglO = BitVec.ofNat 32 (p.2 8).toNat)
      (R := fun s s' => s'.gpr .eax = BitVec.ofNat 32
          (if bytesAt s.mem (w64 (p.2 7) + BitVec.ofNat 64 0) (p.2 8).toNat ++ zeros (16 - (p.2 8).toNat) =
              bytesAt s.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
        Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
        s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
      (fun s hs => cmp_ok hs.1 hs.2 t1 t16 (by decide)) (cmp_ct (.inl rfl) fun s hs => hs) _
      (fun s₀ s'' ⟨s', ⟨s, ⟨s₁, h⟩, _, f, _⟩, fo, _, _⟩ => ⟨⟨fo.env.ebp, fo.env.wW, L.fw⟩, by
        rw [slot_tagFrame L fo.frame (by decide) (by decide), slotv_eq,
          slot_frame f fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Lay.w_w (a := 180) (n := 4) (d := 196) (k := 16) (.inl (by decide)) (by decide) (by decide),
          ← slotv_eq]
        exact h.tgl⟩)) ?_
    -- Masked.
    refine Pc.taint [.ebp] (fun s₀ s₃ ⟨s₂, ⟨s', ⟨s, ⟨s₁, h⟩, b, f, g1, g2, g3, rd, wr⟩, fo, rd₂, wr₂⟩, a₃, f₃, e1, e2, e3,
        rd₃, wr₃⟩ => ?_)
      (fun _ _ s₁ s₂ ⟨_, ⟨_, _, fo₁, _⟩, _, _, e₁, _⟩ ⟨_, ⟨_, _, fo₂, _⟩, _, _, e₂, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, fo₁.env.ebp, fo₂.env.ebp]) (by taint_decide)
    have he₃ : WEnv (p.2 7) s₃ := ⟨by rw [e1, fo.env.ebp], by rw [wr₃]; exact fo.env.wW, L.fw⟩
    refine WP.mono (mask_ok he₃ (b := decide (bytesAt s₂.mem (w64 (p.2 7) + BitVec.ofNat 64 0) (p.2 8).toNat ++
        zeros (16 - (p.2 8).toNat) = bytesAt s₂.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16))
      (by rw [a₃]; simp only [decide_eq_true_eq])) fun s₄ ⟨b₄, f₄, ax₄, bp₄, si₄, sp₄, rd₄, wr₄⟩ => ?_
    have f₁ : Frame [rR (p.2 7)] s₁.mem s'.mem := by rw [← h.mem]; exact f
    refine ⟨s₁, h.ent, fo.env.keep (by rw [bp₄, e1]) (by rw [si₄, e2]) (by rw [sp₄, e3]) (by rw [rd₄, rd₃])
      (by rw [wr₄, wr₃]) ?_, ?_, ?_⟩
    · rw [slot_frame f₄ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Lay.w_w (a := 144) (n := 4) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide),
        slot_frame f₃ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Lay.w_w (a := 144) (n := 4) (d := 240) (k := 16) (.inl (by decide)) (by decide) (by decide)]
    · refine f₁.mono (fun r hr => by simp at hr; subst hr; simp) |>.trans
        (fo.frame.mono (fun r hr => List.mem_cons_of_mem _ hr) |>.trans
        (f₃.sub (fun r hr => ⟨wsR (p.2 7), by simp, by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩) |>.trans
        (f₄.mono fun r hr => by simp at hr; subst hr; simp)))
    · have hA : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h.ent.pub hi
      simp only [streamVerifyX86, ret32_eq]
      intro iv a c hr hl hc
      rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
      rw [hA 3 (by decide), hA 4 (by decide)] at hl
      rw [hA 5 (by decide), hA 6 (by decide)] at hc
      rw [hA 0 (by decide), hA 1 (by decide), hA 7 (by decide), hA 8 (by decide)]
      obtain ⟨hr₁, hC, hH⟩ := fin_repr h.ent L hR hr
      have hC' : ciphOf s'.mem (p.2 0) (p.2 1).toNat = ciphOf s₁.mem (p.2 0) (p.2 1).toNat :=
        ciph_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hR
      have hH' : Hk s'.mem (p.2 0) = Hk s₁.mem (p.2 0) :=
        blockAt_frame f₁ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
      have hr₂ : StreamRepr s'.mem (w64 (p.2 2)) (ciphOf s'.mem (p.2 0) (p.2 1).toNat) (Hk s'.mem (p.2 0)) iv a c := by
        rw [hC', hH']
        exact streamRepr_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          simpa using L.st_w (a := 0) (n := 80) (d := 196) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)) hr₁
      have tag := fo.tag iv a c hr₂ hl hc
      rw [hC', hH', hC, hH, BitVec.add_zero] at tag
      generalize fullTag (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH s₀.mem (w64 (p.2 0))) iv a c = T at tag ⊢
      have b₃ : bytesAt s₃.mem (w64 (p.2 7)) 16 = T := by
        rw [bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact w0_disj (by decide) (by decide)) (by decide), tag]
      have bW : bytesAt s₂.mem (w64 (p.2 7) + BitVec.ofNat 64 0) (p.2 8).toNat = T.take (p.2 8).toNat := by
        rw [BitVec.add_zero, ← tag, bytesAt_take _ _ t16]
      have bR : bytesAt s₂.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16 =
          bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat ++ zeros (16 - (p.2 8).toNat) := by
        rw [bytesAt_frame fo.frame (rR_tagFrame L) (by decide), b, h.mem,
          bytesAt_frame h.ent.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact w0_disj (by omega) (by decide)) (by omega)]
      simp only [bW, bR, List.append_left_inj] at b₄ a₃
      simp only [hok, hT, true_and]
      by_cases hX : T.take (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat
      · simp only [hX, ↓reduceIte, decide_true] at b₄ a₃ ⊢
        exact ⟨by rw [ax₄, a₃]; rfl, by rw [b₄, b₃]⟩
      · simp only [hX, ↓reduceIte, decide_false, Bool.false_eq_true] at b₄ a₃ ⊢
        exact ⟨by rw [ax₄, a₃]; rfl, b₄⟩
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, he, hf, hpost⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp]) (by taint_decide)
  refine WP.mono (fin_exitR h₁ L he hf (by decide)) fun s' ⟨abi, m', ax⟩ => ⟨abi, ?_⟩
  simp only [streamVerifyX86, ret32_eq] at hpost ⊢
  rw [m', ax]
  exact hpost

theorem streamVerify_correct (s : State) (hs : streamVerifyX86.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyX86.post s s' :=
  (streamVerify_pc (pubOf 9 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamVerify_ct : ConstantTime isa streamVerifyX86.pre streamVerifyX86.pub streamVerify :=
  Pc.constantTime (pubOf 9) (fun _ _ _ _ h => pubOf_eq h) streamVerify_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
