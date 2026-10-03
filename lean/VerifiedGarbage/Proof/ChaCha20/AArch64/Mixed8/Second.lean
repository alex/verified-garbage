import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Spill

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs counter_ok scalarLoad_ok keeps_vectors)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

structure Second (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun j => Nat.repeat innerBlock (5 + n) (ctr (source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock (2 * n) (ctr (source s₀) 7)) s
  cnt : source s = ctr (source s₀) 7
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  first : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 6))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 →
    s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,lowBuf s₀] s₀.mem s.mem

theorem reload_ok {s₀ s : State} (hp : CP s₀) (h : Spilled s₀ s) :
    WP isa (.seq (.block (VG.Impl.ChaCha20.AArch64.Mixed5.counter 1))
      (.block VG.Impl.ChaCha20.AArch64.load)) s (Second s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 :=
    h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.rd,h.wr,hx0]; exact hp.read 12
  have ho : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.wr,hx0]; exact hp.counter
  apply WP.seq
  refine (counter_ok s (n := 1) (by decide) false hc ho).mono fun a
    ⟨hm,hg,hr,hw,hv,hsp⟩ => ?_
  have hcnt : source a = ctr (source s₀) 7 := by
    rw [source,hg _ (by decide),hm]
    change stateAt (s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 48)
      (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 1)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter]
    change ctr (source s) 1 = _
    rw [h.cnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add]
  have hf : Frame [sr s₀] s.mem a.mem := by
    rw [hm,hx0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hfirst : ∀ k (hk : k < 16),
      a.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
        (block (ctr (source s₀) 6))[k] := by
    intro k hk
    rw [hf.readW (r := lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro r hr'; have he := List.mem_singleton.mp hr'; subst r
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide)]
    exact h.words k hk
  have hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hr,hw,h.rd,h.wr,hg _ (by decide),hx0]; exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hw,h.wr,hg _ (by decide),h.x1]; exact hp.buffer _ _ (by omega)
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [hg _ (by decide),h.x1,hg _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i; rfl
  refine (keeps_vectors hload (scalarLoad_ok a hpₐ)).mono fun b
    ⟨⟨hb,hbm,hbr,hbw,hbk⟩,hbv,hbsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hbr.trans (hr.trans h.rd),
    hbw.trans (hw.trans h.wr),hbsp.trans (hsp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hv,Nat.add_zero] using h.vec
  · rw [hbv,hv]; exact h.table
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat,Nat.mul_zero] using hb
  · rw [source,hbm,hbk _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact hcnt
  · exact ⟨by rw [hbk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),hg _ (by decide)]; exact h.saved.len,
      by rw [hbk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),hg _ (by decide)]; exact h.saved.data⟩
  · rw [hbm]; exact hfirst
  · intro r hnr h1 h19 h26
    rw [hbk r hnr,hg r (by intro he; subst r; exact hnr ⟨2,by decide,rfl⟩)]
    exact h.keep r hnr h1 h19 h26
  · rw [hbk _ VG.Proof.ChaCha20.AArch64.not_words_x1,hg _ (by decide)]; exact h.x1
  · rw [hbm]; exact h.frame.trans (hf.mono (by simp))

theorem second_ok {s₀ s : State} (hp : CP s₀) (h : Prepared s₀ s 5) :
    WP isa second s (Second s₀) := by
  apply WP.seq
  exact (spill_ok hp h).mono fun _ h => reload_ok hp h

theorem compute_second_ok {s₀ s : State} (hp : CP s₀) (h : Second s₀ s) :
    WP isa (phase .x20) s fun u => Second s₀ u 5 := by
  refine (counted_phase_ok h.vec h.scalar h.table
    (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)) (by decide)
    (h.x1.trans ((h.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))
      (by decide) (by decide) (by decide)).trans hp.x20).symm)).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  have he (f : CState → CState) (x : CState) : Nat.repeat f 5 (Nat.repeat f 5 x) = Nat.repeat f 10 x := rfl
  have hv : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j))) u := by
    have he' : (fun j => Nat.repeat innerBlock 5 (Nat.repeat innerBlock 5 (ctr (source s₀) j))) =
        (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) :=
      funext fun j => he innerBlock (ctr (source s₀) j)
    rw [he'] at hu
    exact hu
  refine ⟨hv,hut,hr.holds,?_,?_,?_,?_,?_,hr.rd.trans h.rd,hr.wr.trans h.wr,hsp.trans h.sp,?_⟩
  · rw [source,hr.mem,hr.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact h.cnt
  · exact ⟨by rw [hr.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hr.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩
  · rw [hr.mem]; exact h.first
  · intro r hnr h1 h19 h26; rw [hr.keep r hnr]; exact h.keep r hnr h1 h19 h26
  · rw [hr.keep _ VG.Proof.ChaCha20.AArch64.not_words_x1]; exact h.x1
  · rw [hr.mem]; exact h.frame

end VG.Proof.ChaCha20.AArch64.Mixed8
