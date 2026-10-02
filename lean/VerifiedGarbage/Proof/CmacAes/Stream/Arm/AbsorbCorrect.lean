import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Absorb

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd wp_ldr)
open VG.Proof.CmacAes.Arm (restoreB_ok)
open VG.Proof.Cmac.Stream (held held_le)

theorem disjoint_zero (p : Addr) (r : Region) : (⟨p, 0⟩ : Region).Disjoint r := fun a h _ => by
  simp only [Region.Contains] at h; omega

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

/-- The data of the second call: the state if no data is left. -/
abbrev d2Of (St D : BitVec 32) (c L : Nat) : BitVec 32 :=
  if leftOf c L = 0 then St else D + BitVec.ofNat 32 (fOf c L)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {s₀ s : State} {St D S : BitVec 32} {L R : Nat} (h : AMid₁ s₀ St D S L R s) :
    WP isa updCall s (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r4],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r5],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r6],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r7],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r10],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.keep _ (by simp [preserved]) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)], by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd],
      by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : BitVec 32) (L R : Nat) (m : Mem) (s : State) : Prop where
  mem : s.mem = m
  args : UArgs s St (St + BitVec.ofNat 32 272) (d2Of St D (countArm s₀).toNat L) S R (nbOf (countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (16 * nbOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem chain2_mid {s₀ s : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R s.mem) := by
  have hL := hp.lt
  have hD := hp.fD
  have hw := hp.fSt
  have ⟨hfL, _⟩ := f_le (countArm s₀).toNat L
  have hsum := nb_le (countArm s₀).toNat L
  refine WP.mono (chain2_wp (x := leftOf (countArm s₀).toNat L) (by unfold leftOf; omega) h.r7 h.r4 h.r6) fun s₇ h₇ => ?_
  obtain ⟨r9₇, r8₇, r3₇, r0₇, r1₇, r2₇, g₇, m₇, sp₇, rd₇, wr₇⟩ := h₇
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (e : r ≠ .r8) (f : r ≠ .r9) :
      s₇.gpr r = s.gpr r := g₇ r a b c d e f
  have hsp : s₇.sp = s₀.sp := by rw [sp₇, h.sp]
  have hrd : s₇.rd = s₀.rd := by rw [rd₇, h.rd]
  have hwr : s₇.wr = s₀.wr := by rw [wr₇, h.wr]
  refine ⟨m₇, ?_, by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r4],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7], r8₇,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r11], hsp, hrd, hwr⟩
  have common := @APre.uargs _ _ _ _ _ _ hp s₇ (d2Of St D (countArm s₀).toNat L) (nbOf (countArm s₀).toNat L) r0₇
    (by rw [r1₇, h.r5]) r2₇ r3₇ r9₇ (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r10]) hsp hrd hwr
  by_cases h0 : leftOf (countArm s₀).toNat L = 0
  · have hn : nbOf (countArm s₀).toNat L = 0 := by simp [nbOf, nbx, h0]
    simp only [d2Of, h0, ↓reduceIte, hn, Nat.mul_zero] at common ⊢
    refine common (by decide) (disjoint_zero _ _) (disjoint_zero _ _) ((disjoint_zero _ _).symm) (by omega)
      (Covers.right (by have := hp.inSt (d := 0) (n := 0) (by decide); rwa [BitVec.add_zero] at this))
  · simp only [d2Of, h0, ↓reduceIte] at common ⊢
    have hn : 16 * nbOf (countArm s₀).toNat L < leftOf (countArm s₀).toNat L := by
      simp only [nbOf, nbx, h0, ↓reduceIte]; omega
    have aD : State.addr (D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)) =
        State.addr D + BitVec.ofNat 64 (fOf (countArm s₀).toNat L) := addr_add (by unfold leftOf at h0; omega)
    have dD : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (fOf (countArm s₀).toNat L),
        16 * nbOf (countArm s₀).toNat L⟩ ⟨State.addr D, L⟩ := Offset.sub_base _ (by unfold leftOf at hn; omega)
    rw [aD] at common
    refine common (by omega) ((hp.st_d.sub_left (Offset.sub_base _ (by decide))).symm.sub_left dD)
      (hp.d_s.sub_left dD) (hp.b_d.sub_right dD)
      (by rw [toNat_add_ofNat (by unfold leftOf at h0; omega)]; unfold leftOf at hn; omega)
      (hp.inD (by unfold leftOf at hn; omega))

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (16 * nbOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AMid₂.after {s₀ s s' : State} {St D S : BitVec 32} {L R : Nat} {m : Mem} (h : AMid₂ s₀ St D S L R m s)
    (h₈ : UPost s St (St + BitVec.ofNat 32 272) (d2Of St D (countArm s₀).toNat L) S R (nbOf (countArm s₀).toNat L) s') :
    AAfter₂ s₀ St D S L s' :=
  ⟨by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r4],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r6],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r7],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r8],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r10],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r11], by rw [h₈.sp, h.sp], by rw [h₈.rd, h.rd],
    by rw [h₈.wr, h.wr]⟩

theorem call2_after {s₀ s : State} {St D S : BitVec 32} {L R : Nat} {m : Mem} (h : AMid₂ s₀ St D S L R m s) :
    WP isa updCall s (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₈ => h.after h₈

theorem AMid₁.after {s₀ s s' : State} {St D S : BitVec 32} {L R : Nat} (h : AMid₁ s₀ St D S L R s)
    (h₆ : UPost s St (St + BitVec.ofNat 32 272) (St + BitVec.ofNat 32 288) S R (b1Of (countArm s₀).toNat L) s') :
    AAfter₁ s₀ St D S L s' :=
  ⟨by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r4],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r5],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r6],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r7],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r10],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.keep _ (by simp [preserved]) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)], by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd],
    by rw [h₆.wr, h.wr]⟩

theorem restore_eq : restore = (saved.take 7).map (fun p => Instr.ldr p.1 .r10 p.2) ++
    ([.ldr .r10 .r10 2200] : List Instr) := rfl

theorem take7_ne : ∀ p ∈ saved.take 7, p.1 ≠ .r10 := by decide

theorem absorb_wp {s₀ : State} (h0 : absorbArm.pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ absorbArm.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = D at hp
  generalize stackArg s₀ 2 = S at hp
  generalize (stackArg s₀ 1).toNat = L at hp
  generalize (s₀.gpr .r1).toNat = R at hp
  have hL := hp.lt
  have hw := hp.fSt
  have hsw := hp.fS
  have hD := hp.fD
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (upd_call h₅.args) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (chain2_mid hp (h₅.after h₆)) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (upd_call h₇.args) fun s₈ h₈ => ?_)
  obtain ⟨c, hc⟩ : ∃ c, (countArm s₀).toNat = c := ⟨_, rfl⟩
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hrr := rest_le c L
  have hh := held_le c
  obtain ⟨r4₈, r6₈, r7₈, r8₈, r10₈, r11₈, sp₈, rd₈, wr₈⟩ := h₇.after h₈
  rw [hc] at r6₈ r7₈ r8₈
  refine WP.seq (WP.mono (rest_wp (St := St) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega) r6₈ r7₈
    r8₈ r4₈) fun s₉ h₉ => ?_)
  obtain ⟨r6₉, r7₉, r1₉, r2₉, g₉, m₉, sp₉, rd₉, wr₉⟩ := h₉
  have restEq : leftOf c L - 16 * nbOf c L = restOf c L := rfl
  rw [restEq] at r7₉ r1₉
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈]
  have a288 := hp.aS (k := 288) (by decide)
  refine WP.seq (WP.mono (copy_wp (p := D + BitVec.ofNat 32 (fOf c L) + BitVec.ofNat 32 (16 * nbOf c L))
    (c := St + BitVec.ofNat 32 288) (L := restOf c L) (x := restOf c L) (Nat.le_refl _) (by omega) r6₉ r2₉ r1₉ r7₉
    fun hpos => ?_) fun s₁₀ h₁₀ => ?_)
  · have aP : State.addr (D + BitVec.ofNat 32 (fOf c L) + BitVec.ofNat 32 (16 * nbOf c L)) =
        State.addr D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L) := by
      rw [add_ofNat32]; exact addr_add (by omega)
    exact
    { fp := by rw [add_ofNat32, toNat_add_ofNat (by omega)]; omega
      fc := by rw [toNat_add_ofNat (by omega)]; omega
      hr := by rw [rd₉', wr₉', aP]; exact hp.inD (by omega)
      hw := by rw [wr₉', a288]; exact hp.inSt (by omega)
      hd := by
        rw [aP, a288]
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Offset.sub_base _ (by omega)) }
  have r10₁₀ : s₁₀.gpr .r10 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), r10₈]
  have inS : ∀ d, d + 4 ≤ 2304 → InRegions (s₁₀.rd ++ s₁₀.wr) (State.addr S + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      exact Covers.right (hp.inS hd) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [restore_eq]
  refine restoreB_ok (saved.take 7) s₁₀ _ (by decide) (fun p hp' => ?_)
    fun s₁₁ ld₁₁ ho₁₁ m₁₁ rd₁₁ wr₁₁ sp₁₁ => ?_
  · have hb := saved_bound p (List.mem_of_mem_take hp')
    exact ⟨take7_ne p hp', by omega, by rw [r10₁₀]; omega, by rw [r10₁₀]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr S + BitVec.ofNat 64 2200) (by decide)
    (by rw [ho₁₁ _ (by decide), r10₁₀]; exact addr_add (by omega))
    (by rw [rd₁₁, wr₁₁]; exact inS _ (by decide)) fun s₁₂ u₁₂ => WP.block_nil ?_
  -- The frames.
  have hm5 : s₅.mem = m4 s₀ St D S c L := by rw [h₅.mem, hc]
  have hlr : (Spec.Aes.bytesAt s₉.mem (State.addr (D + BitVec.ofNat 32 (fOf c L) + BitVec.ofNat 32 (16 * nbOf c L)))
      (restOf c L)).length = restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨State.addr S, 2304⟩] s₀.mem (aMem s₀ S) := aMem_frame _ _
  have fC1 : Frame [⟨State.addr St + BitVec.ofNat 64 288, 16⟩] (aMem s₀ S) s₅.mem := by
    rw [hm5, m4]
    by_cases hf0 : fOf c L = 0
    · rw [hf0, show Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) 0 = [] from rfl, writeBytes_nil]
      exact Frame.refl _ _
    · have hlt : 288 + held c < 304 := by unfold fOf at hf0; omega
      refine writeBytes_frame _ _ _ ?_
      rw [Proof.Cmac.bytesAt_length, hp.aS hlt]
      exact Offset.contains (State.addr St) (d := 288 + held c) (n := fOf c L) (e := 288) (k := 16) (by omega)
        (by omega) (by omega)
  have hb5 : blw16 s₅ = blw16 s₀ := by rw [blw16, h₅.sp]
  have hb7 : blw16 s₇ = blw16 s₀ := by rw [blw16, h₇.sp]
  have f6 : Frame [⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, blw16 s₀] s₅.mem s₆.mem := by
    have := h₆.frame; rwa [hb5] at this
  have f8 : Frame [⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, blw16 s₀] s₆.mem s₈.mem := by
    have := h₈.frame; rwa [hb7, h₇.mem] at this
  have fC2 : Frame [⟨State.addr St + BitVec.ofNat 64 288, 16⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    refine writeBytes_frame _ _ _ ?_
    rw [← m₉, hlr, a288]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  let K : List Region := [⟨State.addr S, 2304⟩, ⟨State.addr St + BitVec.ofNat 64 288, 16⟩,
    ⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, blw16 s₀]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  have a272 := hp.aS (k := 272) (by decide)
  have m₁₂ : s₁₂.mem = s₁₀.mem := by rw [u₁₂.mem, m₁₁]
  refine ⟨⟨fun r hr => ?_, by rw [u₁₂.sp, sp₁₁, h₁₀.sp, sp₉, sp₈]⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (aMem s₀ S) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 4 ≤ 2208) :
        s₁₀.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 =
          (aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
      have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 2304⟩ := Offset.sub_base _ (by omega)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
      · rw [a272]; exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hp.b_s.symm.sub_left sub
    have ld (q : Reg) (d : Nat) (hq : (q, d) ∈ saved.take 7) : s₁₂.gpr q = s₀.gpr q := by
      have hb := saved_bound _ (List.mem_of_mem_take hq)
      rw [u₁₂.other _ (take7_ne _ hq), ld₁₁ _ hq, r10₁₀, slot d hb.1 hb.2,
        aMem_slot s₀ S (List.mem_of_mem_take hq)]
    have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ld _ 2176 (by decide)
    · exact ld _ 2180 (by decide)
    · exact ld _ 2184 (by decide)
    · exact ld _ 2188 (by decide)
    · exact ld _ 2192 (by decide)
    · exact ld _ 2196 (by decide)
    · rw [u₁₂.gpr, m₁₁, slot 2200 (by decide) (by decide), aMem_slot s₀ S (r := .r10) (d := 2200) (by decide)]
    · rw [u₁₂.other _ (by decide), ho₁₁ _ (by decide), h₁₀.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), r11₈]
    · exact ld _ 2204 (by decide)
  · intro key msg hr hR hcnt hlen
    rw [hp.r0] at hr ⊢
    rw [hp.a0, hp.a1, m₁₂]
    rw [hp.a1] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat64 (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r1]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    have dK : ∀ r ∈ K, (⟨State.addr St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.st_s.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · rw [a272]; exact Offset.base_disjoint _ (by decide) (by decide)
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    have dDat : ∀ r ∈ K, (⟨State.addr D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s
      · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
      · rw [a272]; exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.b_d.symm
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m (State.addr St) (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (State.addr D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem (State.addr D) L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m (State.addr D) hab, Proof.Cmac.bytesAt_frame hf dDat (by omega)]
    have fS' : Frame K s₀.mem (aMem s₀ S) := fS.mono (by simp [K])
    have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 272) 16 := by
      rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (State.addr St) (d := 272) (n := 16) (e := 288) (k := 16) (by decide) (by decide)
            (by decide)) (by decide),
        Proof.Cmac.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_s.sub_left (Offset.sub_base _ (by decide))) (by decide)]
    have cv10 : Spec.Aes.bytesAt s₁₀.mem (State.addr St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (State.addr St + BitVec.ofNat 64 272) 16 :=
      Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint (State.addr St) (d := 272) (n := 16) (e := 288) (k := 16) (by decide) (by decide)
          (by decide)) (by decide)
    have out6 := h₆.out
    rw [a272, a288, ciph _ F5, hc] at out6
    have out8 := h₈.out
    rw [a272, h₇.mem, ciph _ F6, hc] at out8
    have hk : ∀ i < 272, s₁₀.mem (State.addr St + BitVec.ofNat 64 i) = s₀.mem (State.addr St + BitVec.ofNat 64 i) :=
      fun i hi => F10.bytes (R := ⟨State.addr St, 272⟩) dK (by show 272 ≤ 2 ^ 64; decide) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem (State.addr D) L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem (State.addr D) L).take (fOf msg.length L) := by
      have e₀ : Spec.Aes.bytesAt (aMem s₀ S) (State.addr St + BitVec.ofNat 64 288) (held msg.length) =
          Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 288) (held msg.length) :=
        Proof.Cmac.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_s.sub_left (Offset.sub_base _ (by omega))) (by omega)
      rw [hm5, m4]
      by_cases hf0 : fOf msg.length L = 0
      · rw [hf0, show Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) 0 = [] from rfl, writeBytes_nil, Nat.add_zero, e₀,
          List.take_zero, List.append_nil]
      · have hlt : 288 + held msg.length < 304 := by unfold fOf at hf0; omega
        have hlf : (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf msg.length L)).length = fOf msg.length L :=
          Proof.Cmac.bytesAt_length _ _ _
        have e := bytesAt_writeBytes (aMem s₀ S) (State.addr St + BitVec.ofNat 64 288) (held msg.length)
          (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf msg.length L)) (by rw [hlf]; omega)
        rw [hlf] at e
        rw [hp.aS hlt, ← Offset.add_add, e, e₀]
        refine congrArg (_ ++ ·) ?_
        have := dat _ fS' 0 (fOf msg.length L) (by omega)
        rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem (State.addr D) L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, nbx, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem _ 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _ =
          Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ =
          Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨State.addr St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨State.addr St, 304⟩ :=
          Offset.sub_base _ (by omega)
        have dj : ∀ r ∈ [⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, blw16 s₀],
            (⟨State.addr St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [a272]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · exact (hp.b_st.sub_right sub).symm
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, Proof.Cmac.bytesAt_frame f8 dj (by omega), Proof.Cmac.bytesAt_frame f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega
      have hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega
      have hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, nbx, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have aD2 : State.addr (d2Of St D msg.length L) = State.addr D + BitVec.ofNat 64 (fOf msg.length L) := by
        simp only [d2Of, hx, ↓reduceIte]; exact addr_add (by unfold leftOf at hx; omega)
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' (held_le _)] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv10, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, aD2, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        have aP : State.addr (D + BitVec.ofNat 32 (fOf msg.length L) + BitVec.ofNat 32 (16 * nbOf msg.length L)) =
            State.addr D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L) := by
          have hpos : 0 < restOf msg.length L := by
            unfold restOf nbOf nbx; simp only [hx, ↓reduceIte]; omega
          rw [add_ofNat32]; exact addr_add (by omega)
        have e := bytesAt_writeBytes_self s₈.mem (State.addr (St + BitVec.ofNat 32 288))
          (xs := Spec.Aes.bytesAt s₈.mem (State.addr (D + BitVec.ofNat 32 (fOf msg.length L) +
            BitVec.ofNat 32 (16 * nbOf msg.length L))) (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ = _
        rw [hr', h₁₀.mem, m₉, ← a288, e, aP, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.Arm
