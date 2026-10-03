import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Args

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock)

abbrev source (s : State) : CState := stateAt s.mem (s.gpr .x0)
abbrev sr (s : State) : Region := ⟨s.gpr .x0,64⟩
abbrev br (s : State) : Region := ⟨s.gpr .x3,320⟩
abbrev dr (s : State) : Region := ⟨s.gpr .x1,320⟩

structure CP (s : State) : Prop where
  x20 : s.gpr .x20 = s.gpr .x3
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (sr s).Disjoint (br s)
  st_d : (sr s).Disjoint (dr s)
  d_b : (dr s).Disjoint (br s)

structure Prepared (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (ctr (source s₀) j)) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock n (ctr (source s₀) 4)) s
  cnt : source s = ctr (source s₀) 4
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀] s₀.mem s.mem

 theorem prepare_ok (s : State) (hp : CP s) : WP isa prepare s (Prepared s) := by
  apply WP.seq
  refine (saveArgs_ok s).mono fun a ⟨hsaved,hg,hm₀,hr,hw,hv,hsp⟩ => ?_
  have ha : source a = source s := by
    rw [source,hm₀,hg _ (by decide) (by decide)]
  have hi : ∀ k : Fin 16, InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hg _ (by decide) (by decide),hr,hw]; exact hp.read k
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setup_ok a hi).mono fun b ⟨hb,hab,hbt⟩ => ?_
  have h0 : b.gpr .x0 = s.gpr .x0 := by rw [hab.gpr _ (by decide),hg _ (by decide) (by decide)]
  have hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.rd,hab.wr,h0,hr,hw]; exact hp.read 12
  have hco : InRegions b.wr (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.wr,hw,h0]; exact hp.counter
  apply WP.seq
  refine (counter_ok b (n := 4) (by decide) false hc hco).mono fun c
    ⟨hcm,hcg,hcr,hcw,hcv,hcsp⟩ => ?_
  have hcnt : source c = ctr (source s) 4 := by
    rw [source,hcg _ (by decide),hcm]
    change stateAt (b.mem.writeW (b.gpr .x0 + BitVec.ofNat 64 48)
      (b.mem.readW (b.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 4)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    rw [source,hab.mem,hab.gpr _ (by decide)]
    exact congrArg (fun v => ctr v 4) ha
  have hfc : Frame [sr s] b.mem c.mem := by
    rw [hcm,h0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hcs : SavedArgs (s.gpr .x2) (s.gpr .x1) c := by
    exact ⟨by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.len,
      by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.data⟩
  have hpc : VG.Proof.ChaCha20.AArch64.Pre c := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (c.rd ++ c.wr) (c.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcr,hcw,hab.rd,hab.wr,hr,hw,hcg _ (by decide),h0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcw,hab.wr,hw,hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide)]
      exact hp.data _ _ (by omega)
    · change (⟨c.gpr .x1,256⟩ : Region).Disjoint ⟨c.gpr .x0,64⟩
      rw [hcg _ (by decide),hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide),h0]
      exact hp.st_d.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i
    rfl
  refine (keeps_vectors hload (scalarLoad_ok c hpc)).mono fun d ⟨⟨hd,hm,hdrr,hdwr,hdk⟩,hdv,hdsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,hdrr.trans (hcr.trans (hab.rd.trans hr)),
    hdwr.trans (hcw.trans (hab.wr.trans hw)),hdsp.trans (hcsp.trans (hab.sp.trans hsp)),?_⟩
  · intro k j hj
    rw [hdv,hcv]
    have hbb : VG.Proof.ChaCha20.AArch64.Neon4.Holds (ctr (source a)) b := hb
    rw [ha] at hbb
    exact hbb k j hj
  · rw [hdv,hcv,hbt]
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat] using hd
  · rw [source,hm,hdk _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact hcnt
  · exact ⟨by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.len,
      by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.data⟩
  · intro r hnr h21 h22
    rw [hdk r hnr,hcg r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),
      hab.gpr r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),hg r h21 h22]
  · rw [hm]
    rw [hab.mem,hm₀] at hfc
    exact hfc

theorem compute_ok (s : State) (hp : CP s) :
    WP isa (.seq prepare (rounds 10)) s fun u => Prepared s u 10 := by
  apply WP.seq
  refine (prepare_ok s hp).mono fun a h => ?_
  refine (rounds_ok h.vec h.table h.scalar 10).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
  refine ⟨hv,ht,hc.holds,?_,?_,?_,hc.rd.trans h.rd,hc.wr.trans h.wr,hsp.trans h.sp,?_⟩
  · rw [source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact h.cnt
  · exact ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩
  · intro r hr h21 h22; rw [hc.keep r hr,h.keep r hr h21 h22]
  · rw [hc.mem]; exact h.frame

end VG.Proof.ChaCha20.AArch64.Mixed5
