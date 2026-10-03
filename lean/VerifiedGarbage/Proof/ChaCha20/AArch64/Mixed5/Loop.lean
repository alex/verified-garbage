import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Chunk

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (320 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 320 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 320 * t ≤ L s₀
  cs : ∀ r ∈ preserved, r ≠ .x20 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (5 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 320 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀,dR s₀,bR s₀] s₀.mem s.mem

structure BulkInv (s₀ : State) (t : Nat) (s : State) : Prop extends LInv s₀ t s where
  x20 : s.gpr .x20 = bp s₀
  saved : ∀ j : Fin 3, s.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
    s₀.gpr ([.x20,.x19,.x26].getD j .x20)

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 320 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (block (ctr (ctr S (5 * t)) ((k - 320 * t) / 64)))).getD
        ((k - 320 * t) % 64) 0 := by
  rw [keystream_getD _ hk,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show 5 * t + (k - 320 * t) / 64 = k / 64 by omega,
    show (k - 320 * t) % 64 = k % 64 by omega]

 theorem next_ok (s : State) (hlen : 320 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block next) s fun u =>
      u.gpr .x1 = s.gpr .x1 + 320 ∧ u.gpr .x2 = s.gpr .x2 - 320 ∧
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat - 320 < 320 then 1 else 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 5 ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next,counter,check,ite_false,
    List.cons_append,List.nil_append,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,ite_true,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,?_,?_,?_,trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 320 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 320) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he,less5 _ (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5; simp only [h1,h2,h4,h5,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) 5
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (320 * t),320⟩
theorem win_sub {s₀ : State} {t : Nat} (h : 320 * t + 320 ≤ L s₀) :
    Region.Sub (win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem cp_of_inv {s₀ s : State} (hp : XPre s₀) {t : Nat} (h : BulkInv s₀ t s)
    (hge : 320 * t + 320 ≤ L s₀) : CP s := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hw : s.wr = [stR s₀,dR s₀,bR s₀] := h.wr.trans hp.wr
  refine ⟨h.x20.trans h.x3.symm,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k; rw [h.rd,hp.rd,hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  · intro d n hn; rw [hw,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hn (by omega)⟩
  · intro d n hn; rw [hw,h.x1,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x0,h.x3]; exact hp.st_b
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x1,320⟩
    rw [h.x0,h.x1]; exact hp.st_d.sub_right (win_sub hge)
  · change (⟨s.gpr .x1,320⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x1,h.x3]; exact hp.d_b.sub_left (win_sub hge)

 theorem chunkData {s₀ s u : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s)
    (hge : 320 * t + 320 ≤ L s₀) (hu : Chunked s u) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 320 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  by_cases hin : 320 * t ≤ k ∧ k < 320 * t + 320
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 320 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1,BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' hin.1]
    have hh := hu.data (k - 320 * t) (by omega)
    rw [he,h.data k hk,ite_eq_right (by omega),source,h.x0,h.cnt, ← ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains,Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega),Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hu.frame (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change ¬ (⟨s.gpr .x0,64⟩ : Region).Contains _ 1
        rw [h.x0]; exact fun hc => hp.st_d _ hc (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)
      · exact fun hc => hp.d_b _ (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)
          (Region.sub_prefix (by decide : 64 ≤ 320) _ (by simpa only [lowBuf,h.x3] using hc))
      · change ¬ (⟨s.gpr .x1,320⟩ : Region).Contains _ 1
        rw [h.x1]; exact hx)
    rw [hh,h.data k hk]
    by_cases hold : k < 320 * t
    · rw [ite_eq_left hold,ite_eq_left (by omega)]
    · rw [ite_eq_right hold,ite_eq_right (by omega)]

abbrev guardR (s₀ : State) (j : Fin 3) : Region := ⟨bp s₀ + BitVec.ofNat 64 (256 + 8 * j),8⟩

theorem guard_chunk {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s)
    (hge : 320 * t + 320 ≤ L s₀) (j : Fin 3) :
    ∀ r ∈ [sr s,lowBuf s,dr s], (guardR s₀ j).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (guardR s₀ j).Disjoint ⟨s.gpr .x0,64⟩
    rw [h.x0]
    exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))
  · change (guardR s₀ j).Disjoint ⟨s.gpr .x3,64⟩
    rw [h.x3]
    exact Offset.disjoint_base _ (by have hj := j.isLt; omega) (by have hj := j.isLt; omega)
  · change (guardR s₀ j).Disjoint ⟨s.gpr .x1,320⟩
    rw [h.x1]
    exact (hp.d_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))).sub_right
      (win_sub hge)

 theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 320 * t + 320 ≤ L s₀) {s : State} (h : BulkInv s₀ t s) :
    WP isa body s fun u => BulkInv s₀ (t + 1) u ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 320 * (t + 1) < 320 then 1 else 0) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  apply WP.seq
  refine (chunk_ok s (cp_of_inv hp h hge)).mono fun u hu => ?_
  have hx0 : u.gpr .x0 = st s₀ := hu.x0.trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (320 * t) := hu.x1.trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 320 * t) := hu.x2.trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := hu.x3.trans h.x3
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (5 * t) := by
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
  have hlen : (u.gpr .x2).toNat = L s₀ - 320 * t := by
    rw [hx2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hsaved : ∀ j : Fin 3, u.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      s₀.gpr ([.x20,.x19,.x26].getD j .x20) := by
    intro j
    rw [hu.frame.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (guard_chunk hp h hge j) (by decide),h.saved j]
  refine (next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1,hv2,hv5,hkeep,hctr,hframe,hrd,hwr,hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (320 * (t + 1)) := by
    rw [hv1,hx1,BitVec.add_assoc]
    change _ + (BitVec.ofNat 64 (320 * t) + BitVec.ofNat 64 320) = _
    rw [← BitVec.ofNat_add,show 320 * t + 320 = 320 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 320 * (t + 1)) := by
    rw [hv2,hx2]
    change BitVec.ofNat 64 (L s₀ - 320 * t) - BitVec.ofNat 64 320 = _
    rw [Offset.ofNat_sub_ofNat (by omega),show L s₀ - 320 * t - 320 = L s₀ - 320 * (t + 1) by omega]
  refine ⟨⟨⟨?_,hptr,hrem,?_,by omega,?_,hrd.trans (hu.rd.trans h.rd),
    hwr.trans (hu.wr.trans h.wr),hsp.trans (hu.sp.trans h.sp),?_,?_,?_⟩,?_,?_⟩,?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx3]
  · intro r hr hr20 hr21 hr22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [hkeep r n1 n2 n4 n5,hu.cs r hr hr21 hr22,h.cs r hr hr20 hr21 hr22]
  · rw [hx0,hcnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
      show 5 * t + 5 = 5 * (t + 1) by omega] at hctr
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
      · exact ⟨bR s₀,by simp,by simpa only [lowBuf,h.x3] using Region.sub_prefix (base := bp s₀) (by decide : 64 ≤ 320)⟩
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
  · rw [hv5,hlen,show L s₀ - 320 * t - 320 = L s₀ - 320 * (t + 1) by omega]

theorem init_ok (s : State) : WP isa (.block check) s fun u =>
    LInv s 0 u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s < 320 then 1 else 0) := by
  refine (check_ok s).mono fun u ⟨h5,hg,hm,hr,hw,hv,hsp⟩ => ?_
  refine ⟨⟨hg _ (by decide),?_,?_,hg _ (by decide),by omega,?_,hr,hw,hsp,?_,?_,?_⟩,
    ?_,h5⟩
  · rw [hg _ (by decide)]; simp only [Nat.mul_zero,BitVec.add_zero]
  · rw [hg _ (by decide)]
    simp only [Nat.mul_zero,Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
  · intro r hr _ _ _
    have nr : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    exact hg r nr
  · rw [hm]; exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; rw [hm]; simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]
  · rw [hm]; exact Frame.refl _ _
  · intro r hr
    have nr : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    exact hg r nr

 theorem zero_batches {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 320 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (320 ≤ n)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s .x5,h]
  by_cases hn : n < 320
  · simp only [ite_eq_left hn]
    have hnn : ¬ 320 ≤ n := by omega
    simp [hnn]
  · simp only [ite_eq_right hn]
    have hnn : 320 ≤ n := by omega
    simp [hnn]

 theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : BulkInv s₀ 0 s)
    (hge : 320 ≤ L s₀) : WP isa (.loop body (.zero .x .x5)) s fun u =>
      ∃ t, L s₀ - 320 * t < 320 ∧ BulkInv s₀ t u := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ t, n = L s₀ - 320 * t ∧ 320 ≤ n ∧ BulkInv s₀ t s
  refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0,by omega,hge,h⟩
  intro n s ⟨t,hn,hge,hi⟩
  refine (body_ok hp (by omega) hi).mono fun u ⟨hu,h5⟩ => ?_
  have hc := zero_batches h5
  by_cases he : L s₀ - 320 * (t + 1) < 320
  · left
    refine ⟨?_,t + 1,he,hu⟩
    have hne : ¬ 320 ≤ L s₀ - 320 * (t + 1) := by omega
    simpa only [decide_eq_false hne] using hc
  · right
    refine ⟨?_,L s₀ - 320 * (t + 1),by omega,t + 1,rfl,by omega,hu⟩
    have hne : 320 ≤ L s₀ - 320 * (t + 1) := by omega
    simpa only [decide_eq_true hne] using hc

end VG.Proof.ChaCha20.AArch64.Mixed5
