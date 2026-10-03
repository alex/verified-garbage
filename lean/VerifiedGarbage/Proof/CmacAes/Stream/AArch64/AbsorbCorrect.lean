import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Absorb

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ : State} (h0 : absorbAArch64.pre s₀) :
    WP isa (absorb v.callee) s₀ fun s' => GprAbi s₀ s' ∧ absorbAArch64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x3 = D at hp
  generalize s₀.gpr .x5 = S at hp
  generalize (s₀.gpr .x4).toNat = L at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x19₅, x20₅, x21₅, x22₅, x23₅, o₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x21₅ x22₅ m₅
  refine WP.seq (WP.mono (upd_call v _ args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₆.gpr r = s₅.gpr r := h₆.saved r hr h30
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega)
    (by rw [k₆ .x22 (by simp [preserved]) (by decide), x22₅])) fun s₇ h₇ => ?_)
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x24) (h30 : r ≠ .x30) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr h30]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x1₇, k₆ .x20 (by simp [preserved]) (by decide), x20₅])
    (by rw [x2₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x3₇, k₆ .x21 (by simp [preserved]) (by decide), x21₅]) x4₇
    (by rw [x5₇, k₆ .x23 (by simp [preserved]) (by decide), x23₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega⟩
  refine WP.seq (WP.mono (upd_call v _ args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₈.gpr r = s₇.gpr r := h₈.saved r hr h30
  obtain ⟨s₉, run₉, x21₉, x22₉, x6₉, x7₉, x8₉, sv₉, sp₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D)
    (a := fOf c L) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega)
    (by rw [k₈ .x21 (by simp [preserved]) (by decide), k₇ .x21 (by simp [preserved]) (by decide) (by decide),
      x21₅])
    (by rw [k₈ .x24 (by simp [preserved]) (by decide), x24₇])
    (by rw [k₈ .x22 (by simp [preserved]) (by decide), k₇ .x22 (by simp [preserved]) (by decide) (by decide),
      x22₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  have hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega) x7₉
    (by rw [x6₉, k₈ .x19 (by simp [preserved]) (by decide), k₇ .x19 (by simp [preserved]) (by decide) (by decide),
      x19₅]) x8₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have x23₁₀ : s₁₀.gpr .x23 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide),
      sv₉ _ (by simp [preserved]) (by decide) (by decide),
      k₈ .x23 (by simp [preserved]) (by decide), k₇ .x23 (by simp [preserved]) (by decide) (by decide), x23₅]
  obtain ⟨s₁₁, run₁₁, slot₁₁, keep₁₁, sp₁₁, m₁₁⟩ := restore_ok s₁₀ x23₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key and the data are in none of these.
  have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint St (by omega) (by omega)
  have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₁, h₁₀.sp, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2232) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega) (by omega)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
    have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₁₁.gpr r = s₀.gpr r := by
      have hd : 2176 ≤ d ∧ d + 8 ≤ 2232 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        omega
      rw [slot₁₁ r d h, slot d hd.1 hd.2, absSaved_slot s₀ S h]
    have hc' : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x24 → r ≠ .x30 →
        r ≠ .x23 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := by decide
    have oth (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x19) (b : r ≠ .x20) (c : r ≠ .x21) (d : r ≠ .x22)
        (e : r ≠ .x24) (f : r ≠ .x30) (g : r ≠ .x23) : s₁₁.gpr r = s₀.gpr r := by
      obtain ⟨n6, n7, n8, n9⟩ := hc' r hr a b c d e f g
      rw [keep₁₁ r a b c d e f g, h₁₀.other r n6 n7 n8 n9, sv₉ r hr c d, k₈ r hr f, k₇ r hr e f,
        o₅ r hr a b c d g]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2176) (by simp [saved])
    · exact sl (d := 2184) (by simp [saved])
    · exact sl (d := 2192) (by simp [saved])
    · exact sl (d := 2200) (by simp [saved])
    · exact sl (d := 2224) (by simp [saved])
    · exact sl (d := 2208) (by simp [saved])
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact sl (d := 2216) (by simp [saved])
  · intro key msg hr hR hcnt hlen
    rw [hp.x0] at hr ⊢
    rw [hp.x3, hp.x4]
    rw [hp.x4] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.x1]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega)]
    have fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Offset.sub_base S (by decide)))
          (by omega)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega)
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, bytesAt_frame f8 dj (by omega), bytesAt_frame f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega
      have hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega
      have hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.AArch64
