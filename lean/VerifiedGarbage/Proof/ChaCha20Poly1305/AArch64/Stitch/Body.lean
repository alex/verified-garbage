import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save

/-!
# ChaCha20 and Poly1305 together (AArch64): a chunk of the loop

`Stitch.body`, as `Mixed8.body_ok`: from the kernel's loop invariant
(`Mixed8.BulkInv`) after `t` chunks to the one after `t + 1`, relative to the
entry state `rebase s₀ u`, since the chunk changes the accumulator's
registers.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Chunked source sr scalarBuf dr LInv GPInv BulkInv
  cp_of_inv chunkData next_ok win win_sub guardR guardVR guard_chunk guardV_chunk)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

@[simp] theorem rebase_x0 (s₀ u : State) : (rebase s₀ u).gpr .x0 = s₀.gpr .x0 := rebase_of (by decide)
@[simp] theorem rebase_x1 (s₀ u : State) : (rebase s₀ u).gpr .x1 = s₀.gpr .x1 := rebase_of (by decide)
@[simp] theorem rebase_x2 (s₀ u : State) : (rebase s₀ u).gpr .x2 = s₀.gpr .x2 := rebase_of (by decide)
@[simp] theorem rebase_x3 (s₀ u : State) : (rebase s₀ u).gpr .x3 = s₀.gpr .x3 := rebase_of (by decide)
@[simp] theorem rebase_x19 (s₀ u : State) : (rebase s₀ u).gpr .x19 = s₀.gpr .x19 := rebase_of (by decide)
@[simp] theorem rebase_x20 (s₀ u : State) : (rebase s₀ u).gpr .x20 = s₀.gpr .x20 := rebase_of (by decide)
@[simp] theorem rebase_x26 (s₀ u : State) : (rebase s₀ u).gpr .x26 = s₀.gpr .x26 := rebase_of (by decide)
@[simp] theorem rebase_v (s₀ u : State) : (rebase s₀ u).v = s₀.v := rfl

@[simp] theorem st_rebase (s₀ u : State) : st (rebase s₀ u) = st s₀ := rebase_x0 s₀ u
@[simp] theorem dp_rebase (s₀ u : State) : dp (rebase s₀ u) = dp s₀ := rebase_x1 s₀ u
@[simp] theorem L_rebase (s₀ u : State) : L (rebase s₀ u) = L s₀ := by simp [L]
@[simp] theorem bp_rebase (s₀ u : State) : bp (rebase s₀ u) = bp s₀ := rebase_x3 s₀ u
@[simp] theorem stR_rebase (s₀ u : State) : stR (rebase s₀ u) = stR s₀ := by simp [stR]
@[simp] theorem dR_rebase (s₀ u : State) : dR (rebase s₀ u) = dR s₀ := by simp [dR]
@[simp] theorem bR_rebase (s₀ u : State) : bR (rebase s₀ u) = bR s₀ := by simp [bR]
@[simp] theorem S0_rebase (s₀ u : State) : S0 (rebase s₀ u) = S0 s₀ := by simp [S0]
@[simp] theorem D0_rebase (s₀ u : State) (k : Nat) : D0 (rebase s₀ u) k = D0 s₀ k := by simp [D0]
@[simp] theorem KS_rebase (s₀ u : State) : KS (rebase s₀ u) = KS s₀ := by simp [KS]

theorem xpre_rebase {s₀ : State} (u : State) (hp : XPre s₀) : XPre (rebase s₀ u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h6⟩

/-- The kernel's loop invariant, for states with the accumulator's registers
of `u`. -/
theorem bulkInv_rebase {s₀ s : State} {t : Nat} (h : BulkInv s₀ t s) (u : State) :
    BulkInv (rebase s₀ u) t (rebase s u) := by
  refine ⟨⟨⟨by simpa using h.x0, by simpa using h.x1, by simpa using h.x2, by simpa using h.x3,
    by simpa using h.le, ?_, by simpa using h.rd, by simpa using h.wr, by simpa using h.sp,
    by simpa using h.cnt, by simpa using h.data, by simpa using h.frame⟩,
    by simpa using h.x20, fun j => ?_⟩, by simpa using h.savedV⟩
  · intro r hr h20 h19 h26
    by_cases ha : r ∈ accRegs
    · rw [rebase_acc ha, rebase_acc ha]
    · rw [rebase_of ha, rebase_of ha]; exact h.cs r hr h20 h19 h26

  · have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
    have e := h.saved j
    rcases hj with rfl | rfl | rfl <;> simpa using e
/-- `Mixed8.body_ok` after its chunk: the counter and the pointers advanced. -/
theorem next_after {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s u : State} (h : BulkInv s₀ t s) (hu : Chunked s u) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.next) u fun v =>
      (BulkInv s₀ (t + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0)) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → v.gpr r = u.gpr r) ∧
      Frame [stR s₀] u.mem v.mem := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hx0 : u.gpr .x0 = st s₀ := hu.x0.trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * t) := hu.x1.trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t) := hu.x2.trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := hu.x3.trans h.x3
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (8 * t) := by
    have hc := hu.cnt
    change stateAt u.mem (u.gpr .x0) = stateAt s.mem (s.gpr .x0) at hc
    rw [hx0,h.x0,h.cnt] at hc
    exact hc
  have hdata := chunkData hp h hge hu
  have hw : u.wr = [stR s₀,dR s₀,bR s₀] := hu.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hu.rd,h.rd,hp.rd,hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 512 * t := by
    rw [hx2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hsaved : ∀ j : Fin 3, u.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      s₀.gpr ([.x20,.x19,.x26].getD j .x20) := by
    intro j
    rw [hu.frame.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (guard_chunk hp h hge j) (by decide),h.saved j]
  have hsavedV : ∀ j : Fin 2, u.mem.read (bp s₀ + BitVec.ofNat 64 (128 + 16 * j)) 16 =
      s₀.v (#[VReg.v8,VReg.v9][j]) := by
    intro j
    rw [hu.frame.read (r := guardVR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (guardV_chunk hp h hge j) (by decide),h.savedV j]
  refine (next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1,hv2,hv5,hkeep,hctr,hframe,hrd,hwr,hsp⟩ => ⟨?_, hkeep, by simpa only [stR, hx0] using hframe⟩
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * (t + 1)) := by
    rw [hv1,hx1,BitVec.add_assoc]
    change _ + (BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 512) = _
    rw [← BitVec.ofNat_add,show 512 * t + 512 = 512 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * (t + 1)) := by
    rw [hv2,hx2]
    change BitVec.ofNat 64 (L s₀ - 512 * t) - BitVec.ofNat 64 512 = _
    rw [Offset.ofNat_sub_ofNat (by omega),show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega]
  refine ⟨⟨⟨⟨?_,hptr,hrem,?_,by omega,?_,hrd.trans (hu.rd.trans h.rd),
    hwr.trans (hu.wr.trans h.wr),hsp.trans (hu.sp.trans h.sp),?_,?_,?_⟩,?_,?_⟩,?_⟩,?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx3]
  · intro r hr hr20 hr21 hr22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [hkeep r n1 n2 n4 n5,hu.cs r hr hr21 hr22,h.cs r hr hr20 hr21 hr22]
  · rw [hx0,hcnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega] at hctr
    exact hctr
  · intro k hk
    rw [hframe _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact fun hc => hp.st_d _ hc (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)),hdata k hk]
  · have hf' : Frame [stR s₀,dR s₀,bR s₀] s.mem u.mem := hu.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀,by simp,by change (⟨s.gpr .x0,64⟩ : Region).Sub (stR s₀); rw [h.x0]; exact fun _ hx => hx⟩
      · exact ⟨bR s₀,by simp,by simpa only [scalarBuf,h.x3] using Region.sub_prefix (base := bp s₀) (by decide : 128 ≤ 320)⟩
      · exact ⟨dR s₀,by simp,by simpa only [dr,h.x1] using win_sub hge⟩)
    have hn' : Frame [stR s₀,dR s₀,bR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hu.cs _ (by decide) (by decide) (by decide),h.x20]
  · intro j
    rw [hframe.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsaved j]
  · intro j
    rw [hframe.read (r := guardVR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; have he := List.mem_singleton.mp hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsavedV j]
  · rw [hv5,hlen,show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega]


/-- The bulk's precondition: the stream's (`vg_chacha20_xor`'s), with its
working space 64 bytes after the state, as in the ChaCha20-Poly1305 context. -/
structure BPre (s₀ : State) : Prop extends XPre s₀ where
  bp : bp s₀ = st s₀ + 64#64

theorem BPre.rebase {s₀ : State} (h : BPre s₀) (u : State) : BPre (rebase s₀ u) :=
  ⟨xpre_rebase u h.toXPre, by simpa using h.bp⟩

theorem BPre.key_sub {s₀ : State} (h : BPre s₀) : (⟨st s₀ + 224#64, 16⟩ : Region).Sub (bR s₀) := by
  simp only [bR, h.bp]
  exact Offset.sub (st s₀) (e := 64) (k := 320) (d := 224) (n := 16) (by decide) (by decide)

theorem BPre.key_in {s₀ : State} (h : BPre s₀) {d : Nat} (hd : 224 ≤ d) (hd' : d + 8 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) 8 := by
  rw [h.rd, h.wr]
  refine ⟨bR s₀, by simp, ?_⟩
  simp only [bR, h.bp]
  exact Offset.contains (st s₀) (e := 64) (k := 320) (by omega) (by omega) (by decide)

/-- A chunk of the loop, absorbing the 512 bytes at `B`. -/
theorem body_ok (enc : Bool) {s₀ : State} (hp : BPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s : State} (h : BulkInv s₀ t s) {R a : Nat} {w : Nat}
    (hw : w + 512 ≤ L s₀)
    (hB : dp s₀ + BitVec.ofNat 64 (512 * t) = dataOf enc (dp s₀ + BitVec.ofNat 64 w))
    (ha : Acc R a s) :
    WP isa (body sve enc) s fun v =>
      (BulkInv (rebase s₀ v) (t + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0)) ∧
      Acc R (absorbAll R a (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 w) 512)) v := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hBin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Sub (dR s₀) := Offset.sub_base _ hw
  have hx0 : s.gpr .x0 = st s₀ := h.x0
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hwin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (stR s₀) ∧
      (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (bR s₀) :=
    ⟨hp.st_d.symm.sub_left hBin, hp.d_b.sub_left hBin⟩
  have hsb : (scalarBuf s).Sub (bR s₀) := by
    simp only [scalarBuf, h.x3]; exact Region.sub_prefix (by decide)
  have hkey : (keyR s).Sub (bR s₀) := by simp only [keyR, hx0]; exact hp.key_sub
  have hpre : ChunkPre enc (dp s₀ + BitVec.ofNat 64 w) s := by
    refine ⟨cp_of_inv hp.toXPre h hge, by rw [h.x20, hx0, hp.bp], h.x1.trans hB, fun d hd => ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hrw, hp.rd, hp.wr]
      refine ⟨dR s₀, by simp, ?_⟩
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [hrw, hx0]; exact hp.key_in (by decide) (by decide)
    · rw [hrw, hx0]; exact hp.key_in (by decide) (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa only [sr, hx0] using hwin.1
      · exact hwin.2.sub_right hsb
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa only [sr, hx0] using (hp.st_b.symm.sub_left hkey)
      · simp only [keyR, scalarBuf, hx0, h.x3, hp.bp]
        exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
          (by decide) (by decide)
      · simp only [dr, h.x1]
        exact (hp.d_b.symm.sub_left hkey).sub_right (win_sub hge)
  unfold body
  apply WP.seq
  refine (chunk_ok enc s hpre ha).mono fun g ⟨hg, hag⟩ => ?_
  refine (next_after (xpre_rebase g hp.toXPre) (by simpa using hge) (bulkInv_rebase h g) hg).mono
    fun v ⟨⟨hv, h5⟩, hkeep, hf⟩ => ?_
  have hacc : ∀ r ∈ accRegs, v.gpr r = g.gpr r := fun r hr => hkeep r
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
  rw [rebase_congr s₀ hacc]
  refine ⟨⟨hv, by simpa using h5⟩, hag.frame (acc_regs_keep hacc) ?_⟩
  have hg0 : g.gpr .x0 = st s₀ :=
    (hkeep .x0 (by decide) (by decide) (by decide) (by decide)).symm.trans (hv.x0.trans (st_rebase _ _))
  refine rword_frame (by simpa using hf) (hkeep _ (by decide) (by decide) (by decide) (by decide)) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simp only [keyR, hg0]
  exact (hp.st_b.symm.sub_left hp.key_sub)

/-- Where `Mixed8.enter` stores: `x19`, `x20` and `x26` at `buf[256, 280)`,
and `v8` and `v9` at `buf[128, 160)`. -/
abbrev enterR (s : State) : List Region :=
  [⟨s.gpr .x3 + BitVec.ofNat 64 256, 24⟩, ⟨s.gpr .x3 + BitVec.ofNat 64 128, 32⟩]

theorem enter_frame (s : State)
    (ho : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.enter) s fun u =>
      Frame (enterR s) s.mem u.mem := by
  have c (d n : Nat) (hd : 256 ≤ d) (hn : d + n ≤ 280) :
      (⟨s.gpr .x3 + BitVec.ofNat 64 256, 24⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 d) n :=
    Offset.contains _ hd hn (by decide)
  unfold VG.Impl.ChaCha20.AArch64.Mixed8.enter VG.Impl.ChaCha20.AArch64.Mixed5.enter
  apply WP.block_cons_iff.mpr
  let m₁ := s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 256) (s.gpr .x20)
  refine ⟨{s with mem := m₁}, exec_str_x (by decide) (ho 256 8 (by decide)), ?_⟩
  apply WP.block_cons_iff.mpr
  let m₂ := m₁.writeW (s.gpr .x3 + BitVec.ofNat 64 264) (s.gpr .x19)
  refine ⟨{s with mem := m₂}, exec_str_x (s := {s with mem := m₁}) (by decide) (ho 264 8 (by decide)), ?_⟩
  apply WP.block_cons_iff.mpr
  let m₃ := m₂.writeW (s.gpr .x3 + BitVec.ofNat 64 272) (s.gpr .x26)
  refine ⟨{s with mem := m₃}, exec_str_x (s := {s with mem := m₂}) (by decide) (ho 272 8 (by decide)), ?_⟩
  apply WP.block_cons_iff.mpr
  let a := ({s with mem := m₃} : State).write .x .x20 (s.gpr .x3 + BitVec.ofNat 64 0)
  refine ⟨a, by simpa only [State.read, BitVec.setWidth_eq] using
    exec_addImm_x (s := {s with mem := m₃}) (d := .x20) (n := .x3) (imm := 0) (by decide), ?_⟩
  have f₁ : Frame (enterR s) s.mem a.mem :=
    (((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (c 256 8 (by decide) (by decide))).writeW
      (List.mem_cons_self ..) _ (c 264 8 (by decide) (by decide))).writeW (List.mem_cons_self ..) _
      (c 272 8 (by decide) (by decide))
  have ha3 : a.gpr .x3 = s.gpr .x3 := RegUpd.gpr_write_of_ne _ .x _ (by decide)
  have haw : a.wr = s.wr := rfl
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok a (by rw [haw, ha3]; exact ho 128 16 (by decide))
    (by rw [haw, ha3]; exact ho 144 16 (by decide))).mono fun u ⟨_, _, _, _, _, hf, _, _⟩ => ?_
  simp only [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR, ha3] at hf
  exact f₁.trans (hf.mono (by simp))

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
