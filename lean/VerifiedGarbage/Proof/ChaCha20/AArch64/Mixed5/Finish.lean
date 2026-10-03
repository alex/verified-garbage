import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Spill

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev firstR (s : State) : Region := ⟨s.gpr .x1,256⟩

structure Finished (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  buf : ∀ r : Fin 4, s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
    VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => block (ctr (source s₀) 4)) r
  data : ∀ k < 256, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,lowBuf s₀,firstR s₀] s₀.mem s.mem

theorem finish_ok {s₀ s : State} (hp : CP s₀) (h : Spilled s₀ s) :
    WP isa finish s (Finished s₀) := by
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  apply WP.seq
  refine (restoreArgs_ok s h.saved).mono fun a
    ⟨ha1,ha2,ha3,hag,ham,har,haw,hav,hasp⟩ => ?_
  have ha0 : a.gpr .x0 = s₀.gpr .x0 := (hag _ (by decide) (by decide) (by decide)).trans hx0
  have ha₃ : a.gpr .x3 = s₀.gpr .x3 := ha3.trans hx20
  have har' : a.rd = s₀.rd := har.trans h.rd
  have haw' : a.wr = s₀.wr := haw.trans h.wr
  have hcnta : source a = ctr (source s₀) 4 := by
    rw [source,ham,hag _ (by decide) (by decide) (by decide)]; exact h.cnt
  have hc : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [har',haw',ha0]; exact hp.read 12
  have hco : InRegions a.wr (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [haw',ha0]; exact hp.counter
  apply WP.seq
  refine (counter_ok a (n := 4) (by decide) true hc hco).mono fun b
    ⟨hbm,hbg,hbr,hbw,hbv,hbsp⟩ => ?_
  have hb0 : b.gpr .x0 = s₀.gpr .x0 := (hbg _ (by decide)).trans ha0
  have hcntb : source b = source s₀ := by
    rw [source,hbg _ (by decide),hbm]
    change stateAt (a.mem.writeW (a.gpr .x0 + BitVec.ofNat 64 48)
      (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 48) 32 - BitVec.ofNat 32 4)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      ← VG.Proof.ChaCha20.AArch64.Xor.stateAt_getElem_counter]
    change (source a).set 12 ((source a)[12] - BitVec.ofNat 32 4) = _
    rw [hcnta,ctr,Vector.getElem_set_self,BitVec.add_sub_cancel,Vector.set_set,
      Vector.set_getElem_self]
  have hfb : Frame [sr s₀] a.mem b.mem := by
    rw [hbm,ha0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hv : VG.Proof.ChaCha20.AArch64.Neon4.Holds
      (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) b := by
    simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds,hbv,hav] using h.vec
  have hin : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hbr,hbw,har',haw',hb0]; exact hp.read k
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv hin).mono fun c ⟨hvc,hbc⟩ => ?_
  have hcb0 : c.gpr .x0 = s₀.gpr .x0 := (hbc.gpr _ (by decide)).trans hb0
  have hcb1 : c.gpr .x1 = s₀.gpr .x1 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha1)
  have hcb3 : c.gpr .x3 = s₀.gpr .x3 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha₃)
  have hrc : c.rd = s₀.rd := hbc.rd.trans (hbr.trans har')
  have hwc : c.wr = s₀.wr := hbc.wr.trans (hbw.trans haw')
  have hvc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => block (ctr (source s₀) j)) c := by
    intro k j hj
    rw [hvc k j hj,VG.Proof.ChaCha20.AArch64.Neon4.input_eq]
    change _ + (ctr (source b) j)[k] = _
    rw [hcntb]
    simp only [block,Vector.getElem_zipWith,Fin.getElem_fin]
  have hout : ∀ r j : Fin 4, InRegions c.wr
      (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hwc,hcb1]; exact hp.data _ _ (by omega)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hvc' hout).mono fun d ⟨hd,hfd,hcd⟩ => ?_
  have hfd' : Frame [firstR s₀] c.mem d.mem := by simpa only [hcb1] using hfd
  have hfc : Frame [sr s₀] s.mem c.mem := by rw [hbc.mem,← ham]; exact hfb
  have hpre : Frame [sr s₀,lowBuf s₀] s₀.mem c.mem :=
    h.frame.trans (hfc.mono (by simp))
  refine ⟨(congrFun hcd.gpr _).trans hcb0,(congrFun hcd.gpr _).trans hcb1,?_,
    (congrFun hcd.gpr _).trans hcb3,?_,hcd.rd.trans hrc,hcd.wr.trans hwc,
    hcd.sp.trans (hbc.sp.trans (hbsp.trans (hasp.trans h.sp))),?_,?_,?_,
    (hpre.mono (by simp)).trans (hfd'.mono (by simp))⟩
  · rw [hcd.gpr,hbc.gpr _ (by decide),hbg _ (by decide),ha2]
  · intro r hr h21 h22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n3 : r ≠ .x3 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    rw [hcd.gpr,hbc.gpr r n4,hbg r n4,hag r n1 n2 n3]
    exact h.keep r (VG.Proof.ChaCha20.AArch64.not_words_preserved hr) n1 h21 h22
  · rw [source,hcd.gpr,hcb0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfd' (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right (Region.sub_prefix (by decide : 256 ≤ 320))),hbc.mem]
    rw [← hb0]; exact hcntb
  · intro r
    rw [hfd'.read (r := lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact (hp.d_b.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))).symm.sub_left
            (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide),
      hfc.read (r := lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide)]
    exact h.read16 r
  · intro k hk
    rw [hcb1] at hd
    rw [hd k hk,hpre.bytes (R := dr s₀) (by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      · exact hp.st_d.symm
      · exact hp.d_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))
      (by change 320 ≤ 2 ^ 64; decide) (by change k < 320; omega)]

end VG.Proof.ChaCha20.AArch64.Mixed5
