import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem bytesAt_zero (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 0 = [] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbX86.pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ absorbX86.post s₀ s' := by
  have hp := APre.of h0
  have hL := hp.lt
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  have fS : (aSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e56 := hp.esp56
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  have hsum := nb_le (aC s₀) (aL s₀)
  have hrr := rest_le (aC s₀) (aL s₀)
  have hh := held_le (aC s₀)
  unfold absorb
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (upd_call h₅.args) fun s₆ h₆ => ?_)
  have a₆ := upd_aft hp (h₅.mem ▸ m4_big hp) h₅.ctx h₅.ebp h₆
  refine WP.seq (WP.mono (chain2_mid hp a₆) fun s₇ ⟨h₇, m₇⟩ => ?_)
  refine WP.seq (WP.mono (upd_call h₇.args) fun s₈ h₈ => ?_)
  have a₈ := upd_aft hp h₇.aft.frame h₇.aft.ctx h₇.aft.ebp h₈
  unfold absorbPost
  refine WP.seq (WP.mono (rest_wp hp a₈.ctx a₈.ebp) fun s₉ h₉ => ?_)
  -- The last copy.
  have hsrc : 0 < restOf (aC s₀) (aL s₀) →
      (aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀))).setWidth 64 =
        (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) :=
    fun _ => add_setWidth (by omega)
  have p288 : (aSt s₀ + BitVec.ofNat 32 288).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
    add_setWidth (by omega)
  refine WP.seq (WP.mono (copy_wp (L := restOf (aC s₀) (aL s₀)) (by omega) h₉.esi h₉.edi h₉.ecx
    (fun _ => by rw [add_toNat (by omega)]; omega) (fun _ => by rw [add_toNat (by omega)]; omega)
    (fun h => by
      rw [h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨adR s₀, by simp, _, hsrc h, by simp; omega⟩)
    (fun _ => by
      rw [h₉.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨astR s₀, by simp, 288, p288, by simp; omega⟩)
    (fun h => by
      rw [hsrc h, p288]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 288) (n := restOf (aC s₀) (aL s₀)) _ (by omega))).symm.sub_left
        (Offset.sub_base (d := fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) (n := restOf (aC s₀) (aL s₀)) _
          (by omega)))) fun s₁₀ h₁₀ => ?_)
  obtain ⟨m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := h₁₀
  -- The frames.
  have f6 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩,
      below (aE s₀) 56] s₅.mem s₆.mem := by
    have := h₆.frame; rw [h₅.ctx.esp, add_setWidth (by omega)] at this; exact this
  have f8 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩,
      below (aE s₀) 56] s₆.mem s₈.mem := by
    have := h₈.frame; rw [h₇.aft.ctx.esp, add_setWidth (by omega), m₇] at this; exact this
  have m₁₀' : s₁₀.mem = writeBytes s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
      (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)))
        (restOf (aC s₀) (aL s₀))) := by
    rw [m₁₀, h₉.mem, p288]
    by_cases hr0 : restOf (aC s₀) (aL s₀) = 0
    · rw [hr0, bytesAt_zero, bytesAt_zero]
    · rw [hsrc (by omega)]
  have hlr : (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
      16 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))).length = restOf (aC s₀) (aL s₀) :=
    Proof.Cmac.bytesAt_length _ _ _
  have fC2 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, restOf (aC s₀) (aL s₀)⟩] s₈.mem s₁₀.mem := by
    rw [m₁₀']; exact writeBytes_frame _ _ _ (by rw [hlr]; exact Region.contains_self _ _)
  have fSv : Frame [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩] s₀.mem (savedMem s₀ (aSc s₀)) :=
    savedMem_frame _ _
  have fC1 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩]
      (savedMem s₀ (aSc s₀)) s₅.mem := by rw [h₅.mem]; exact m4_frame s₀
  let K : List Region := [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩, below (aE s₀) 56,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, restOf (aC s₀) (aL s₀)⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fSv.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  have KB : Frame (ABig s₀) s₀.mem s₁₀.mem := F10.sub fun r hr => by
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ascR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega)⟩
  -- The saved registers.
  have slots : ∀ r d, (r, d) ∈ saved →
      s₁₀.mem.readW ((aSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have Fp : Frame K.tail (savedMem s₀ (aSc s₀)) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have sub : Region.Sub ⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (ascR s₀) := Offset.sub_base _ (by omega)
    rw [Fp.readW (Region.contains_self _ _) (fun q hq => ?_) (by decide)]
    · exact saveMem_slot _ _ _ hrd
    simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).symm.sub_left sub
  have esp₁₀ : s₁₀.gpr .esp = aE s₀ := by
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), h₉.ctx.esp]
  refine WP.mono (restore_wp (s₀ := s₀) (i := 6) (Sc := aSc s₀) esp₁₀
    (by rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr]; exact hp.arg_in (by decide)) (hp.keep KB (by decide)) fS (by
      rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₁₁ ⟨hcs, m₁₁⟩ => ?_
  have F11 : Frame K s₀.mem s₁₁.mem := m₁₁ ▸ F10
  -- The key, the data and the return address are in none of these.
  have dK : ∀ r ∈ K, (⟨(aSt s₀).setWidth 64, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact Offset.base_disjoint _ (by omega) (by omega)
    · exact Offset.base_disjoint _ (by omega) (by omega)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint _ (by omega) (by omega)
  have dDat : ∀ r ∈ K, (adR s₀).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega))
  have dRet : ∀ r ∈ K, (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact ret_below e56
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega))
  refine ⟨⟨hcs, F11.readW (r := ⟨(aE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  intro key msg hr hRk hcnt hlen
  show Spec.Cmac.Repr s₁₁.mem ((aSt s₀).setWidth 64) key
    (msg ++ Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀))
  have hcm : aC s₀ = msg.length := by
    show (countX86 s₀).toNat = _
    rw [hcnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hR : aR s₀ = Spec.Aes.rounds (key.length / 4) := hRk
  have hRb : 16 * (aR s₀ + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
  have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
  rw [← hR] at hsch
  have ciph : ∀ m : Mem, Frame K s₀.mem m →
      Spec.Cmac.aesWith (aR s₀) (Spec.Aes.bytesAt m ((aSt s₀).setWidth 64) (16 * (aR s₀ + 1))) =
        Spec.Cmac.aes key := fun m hf => by
    rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
      Spec.Cmac.aes, ← hR]
  -- The data, wherever it is read.
  have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ aL s₀ →
      Spec.Aes.bytesAt m ((aD s₀).setWidth 64 + BitVec.ofNat 64 a) b =
        ((Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).drop a).take b := fun m hf a b hab => by
    rw [Proof.Cmac.Stream.bytesAt_offset m _ hab, Proof.Cmac.bytesAt_frame hf dDat (by omega)]
  have fS' : Frame K s₀.mem (savedMem s₀ (aSc s₀)) := fSv.mono (by simp [K])
  -- The chaining value.
  have cv5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 := by
    rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide),
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
  have cv11 : Spec.Aes.bytesAt s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 =
      Spec.Aes.bytesAt s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 := by
    rw [m₁₁]
    exact Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by decide)
  have out6 := h₆.out
  rw [add_setWidth (by omega), add_setWidth (by omega), ciph _ F5] at out6
  have out8 := h₈.out
  rw [add_setWidth (by omega), m₇, ciph _ F6] at out8
  have hk : ∀ i < 272, s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) =
      s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => frame_at F11 dK (by simp only [BitVec.toNat_setWidth]; omega) hi
  have hdl : (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).length = aL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  have hlf : (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))).length =
      fOf (aC s₀) (aL s₀) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes held back so far, and the first `f` bytes of data after them.
  have hb5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
      (held (aC s₀) + fOf (aC s₀) (aL s₀)) =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) (held (aC s₀)) ++
        (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).take (fOf (aC s₀) (aL s₀)) := by
    have e := bytesAt_writeBytes (savedMem s₀ (aSc s₀)) ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) (held (aC s₀))
      (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))) (by rw [hlf]; omega)
    rw [hlf] at e
    rw [h₅.mem, m4, ← Offset.add_add, e,
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide)))
        (by omega)]
    refine congrArg (_ ++ ·) ?_
    have := dat _ fS' 0 (fOf (aC s₀) (aL s₀)) (by omega)
    rwa [BitVec.add_zero, List.drop_zero] at this
  generalize hd : Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀) = d at hdl hb5 dat ⊢
  by_cases hx : leftOf (aC s₀) (aL s₀) = 0
  · -- Everything fits in the block held back.
    have hfL' : fOf (aC s₀) (aL s₀) = aL s₀ := by unfold leftOf at hx; omega
    have hb : b1Of (aC s₀) (aL s₀) = 0 := by simp [b1Of, hx]
    have hn : nbOf (aC s₀) (aL s₀) = 0 := by simp [nbOf, hx]
    have hr0 : restOf (aC s₀) (aL s₀) = 0 := rest_zero hx
    have m118 : s₁₁.mem = s₈.mem := by
      rw [m₁₁, m₁₀', hr0, bytesAt_zero, writeBytes_nil]
    refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl, ← hcm]; omega) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _
      rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
      exact cv5
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ ++ _
      rw [← hcm, hdl]
      have sub : Region.Sub ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, held (aC s₀) + aL s₀⟩ (astR s₀) :=
        Offset.sub_base _ (by omega)
      have dj : ∀ r ∈ [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩,
          below (aE s₀) 56], (⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, held (aC s₀) + aL s₀⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right sub).symm
      have hb5' := hb5
      rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
      rw [m118, Proof.Cmac.bytesAt_frame f8 dj (by omega), Proof.Cmac.bytesAt_frame f6 dj (by omega), hb5']
  · -- The block held back is complete, and more blocks may follow.
    have hlt : 16 - held (aC s₀) < aL s₀ := by unfold leftOf fOf at hx; omega
    have hf' : fOf (aC s₀) (aL s₀) = 16 - held (aC s₀) := by unfold fOf; omega
    have hb : b1Of (aC s₀) (aL s₀) = 1 := by simp [b1Of, hx]
    have hn : nbOf (aC s₀) (aL s₀) = Proof.Cmac.Stream.nblocks (aC s₀) (aL s₀) := by
      simp only [nbOf, hx, ↓reduceIte]
      unfold leftOf Proof.Cmac.Stream.nblocks
      rw [hf']
    have hd2 : (d2Of s₀).setWidth 64 = (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)) := by
      simp only [d2Of, hx, ↓reduceIte]; exact add_setWidth (by omega)
    have hb5' := hb5
    rw [hf', Nat.add_sub_cancel' hh] at hb5'
    refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl, ← hcm]; exact hlt) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _ =
        Spec.Cmac.chain _ (Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _)
          ([Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ ++ _] ++ _)
      rw [← hcm, hdl]
      rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, hd2, Proof.Cmac.Stream.blocksAt_eq,
        dat _ F6 _ _ (by omega), hb5', hf', hn]
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ = _
      rw [← hcm, hdl]
      have e := bytesAt_writeBytes_self s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
        (xs := Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
          16 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))) (by rw [hlr]; omega)
      rw [hlr] at e
      have hr' : aL s₀ - (16 - held (aC s₀)) - 16 * Proof.Cmac.Stream.nblocks (aC s₀) (aL s₀) =
          restOf (aC s₀) (aL s₀) := by
        rw [← hn, ← hf']; rfl
      rw [hr', m₁₁, m₁₀', e, dat _ F8 _ _ (by omega),
        List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega),
        List.drop_drop, ← hn, hf']

end VG.Proof.CmacAes.Stream.X86
