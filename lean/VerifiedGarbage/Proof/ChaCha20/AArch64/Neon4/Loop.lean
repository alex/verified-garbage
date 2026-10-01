import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

/-- Before four-block chunk t. x0/x3 and all but the two scratch registers
are retained, except the advancing data pointer and remaining length. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (256 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 256 * t ≤ L s₀
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (4 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 256 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem shr8 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 8 = BitVec.ofNat 64 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem ctr_add (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.getElem_set_self, Vector.set_set, BitVec.ofNat_add, BitVec.add_assoc]

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 256 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (block (ctr (ctr S (4 * t)) ((k - 256 * t) / 64)))).getD
        ((k - 256 * t) % 64) 0 := by
  rw [keystream_getD _ hk, ctr_add, show 4 * t + (k - 256 * t) / 64 = k / 64 by omega,
    show (k - 256 * t) % 64 = k % 64 by omega]

theorem next_ok (s : State) (hlen : 256 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block next) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 + 256 ∧
      s'.gpr .x2 = s.gpr .x2 - 256 ∧
      s'.gpr .x5 = BitVec.ofNat 64 (((s.gpr .x2).toNat - 256) / 256) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 4 ∧
      Frame [⟨s.gpr .x0, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, runBlock_cons, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, ite_true, ite_false, State.load, hin, State.read, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.sp_write,
    Option.bind_some, Option.map_some, isa, runStep_some, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, State.store, hout, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 256 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 256) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he, shr8 (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5
    simp only [h1, h2, h4, h5, ite_false]
  · have hv : (stateAt s.mem (s.gpr .x0))[12] = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
      simp only [stateAt, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]
    have ht := Xor.stateAt_writeW_counter s.mem (s.gpr .x0)
      (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 48) 4 + BitVec.ofNat 32 4)
    simp only [Mem.writeW, BitVec.setWidth_eq] at ht
    unfold ctr
    rw [hv]
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (256 * t), 256⟩

theorem win_sub {s₀ : State} {t : Nat} (h : 256 * t + 256 ≤ L s₀) :
    Region.Sub (win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h := Xor.L_lt s₀; omega)

theorem chunkData {s₀ s u : State} {t : Nat} (h : LInv s₀ t s)
    (hge : 256 * t + 256 ≤ L s₀)
    (hu : ∀ k < 256, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
      s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0)
    (hf : Frame [⟨s.gpr .x1, 256⟩] s.mem u.mem) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 256 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := Xor.L_lt s₀
  by_cases hin : 256 * t ≤ k ∧ k < 256 * t + 256
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 256 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    have hh := hu (k - 256 * t) (by omega)
    rw [he, h.data k hk, ite_eq_right (by omega), h.x0, h.cnt, ← ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains, Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hf (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; rw [h.x1]; exact hx)
    rw [hh, h.data k hk]
    by_cases hold : k < 256 * t
    · rw [ite_eq_left hold, ite_eq_left (by omega)]
    · rw [ite_eq_right hold, ite_eq_right (by omega)]

theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 256 * t + 256 ≤ L s₀) {s : State} (h : LInv s₀ t s) :
    WP isa body s fun s' => LInv s₀ (t + 1) s' ∧
      s'.gpr .x5 = BitVec.ofNat 64 ((L s₀ - 256 * (t + 1)) / 256) := by
  have hL := Xor.L_lt s₀
  have hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [h.rd, h.wr, hp.rd, hp.wr, h.x0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [h.wr, hp.wr, h.x1, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine (chunk_ok s hin hout).mono fun u ⟨hu, hf, hs⟩ => ?_
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (4 * t) := by
    rw [← h.cnt]
    apply Xor.stateAt_frame hf
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [h.x1]; exact hp.st_d.sub_right (win_sub hge)
  have hdata := chunkData h hge hu hf
  have hx0 : u.gpr .x0 = st s₀ := (hs.gpr _ (by decide)).trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (256 * t) := (hs.gpr _ (by decide)).trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256 * t) := (hs.gpr _ (by decide)).trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := (hs.gpr _ (by decide)).trans h.x3
  have hw : u.wr = [stR s₀, dR s₀, bR s₀] := hs.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hs.rd, h.rd, hp.rd, hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 256 * t := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine (next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1, hv2, hv5, hkeep, hctr, hframe, hrd, hwr, hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (256 * (t + 1)) := by
    rw [hv1, hx1, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (256 * t) + BitVec.ofNat 64 256 = _
    rw [← BitVec.ofNat_add, show 256 * t + 256 = 256 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256 * (t + 1)) := by
    rw [hv2, hx2]
    change BitVec.ofNat 64 (L s₀ - 256 * t) - BitVec.ofNat 64 256 = _
    rw [Offset.ofNat_sub_ofNat (by omega), show L s₀ - 256 * t - 256 = L s₀ - 256 * (t + 1) by omega]
  refine ⟨⟨?_, hptr, hrem, ?_, by omega, ?_, hrd.trans (hs.rd.trans h.rd),
    hwr.trans (hs.wr.trans h.wr), hsp.trans (hs.sp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx3]
  · intro r h1 h2 h4 h5
    rw [hkeep r h1 h2 h4 h5, hs.gpr r h4]; exact h.keep r h1 h2 h4 h5
  · rw [hx0, hcnt, ctr_add, show 4 * t + 4 = 4 * (t + 1) by omega] at hctr
    exact hctr
  · intro k hk
    rw [hframe _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact fun hn => hp.st_d _ hn (data_in hk)), hdata k hk]
  · have hf' : Frame [stR s₀, dR s₀] s.mem u.mem := hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      refine ⟨dR s₀, by simp, ?_⟩; rw [h.x1]; exact win_sub hge)
    have hn' : Frame [stR s₀, dR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hv5, hlen, show L s₀ - 256 * t - 256 = L s₀ - 256 * (t + 1) by omega]

theorem init_ok (s : State) :
    WP isa (.block [.lsr .x .x5 .x2 8]) s fun s' =>
      LInv s 0 s' ∧ s'.gpr .x5 = BitVec.ofNat 64 (L s / 256) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, exec, State.read,
    Size.bits, ite_true, Option.some.injEq, isa, runStep_some, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, by omega, ?_, rfl, rfl, rfl, ?_, ?_, Frame.refl _ _⟩, ?_⟩
  · exact RegUpd.gpr_write_of_ne _ _ _ (by decide)
  · simp only [RegUpd.gpr_write, show Reg.x1 ≠ .x5 by decide, ite_false]
    simp [dp]
  · simp only [RegUpd.gpr_write, show Reg.x2 ≠ .x5 by decide, ite_false, Nat.mul_zero, Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
  · exact RegUpd.gpr_write_of_ne _ _ _ (by decide)
  · intro r _ _ _ h5; exact RegUpd.gpr_write_of_ne _ _ _ h5
  · exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]; rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    have he : s.gpr .x2 = BitVec.ofNat 64 (L s) := by
      simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
    rw [he, BitVec.setWidth_eq, shr8 (Xor.L_lt s)]

theorem zero_chunks {s : State} {n : Nat} (hn : n < 2 ^ 64)
    (h : s.gpr .x5 = BitVec.ofNat 64 (n / 256)) :
    isa.eval (.zero .x .x5) s = some (decide (n < 256)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from Xor.eval_zero s .x5,
    h, Xor.ofNat_beq_zero (by omega)]
  congr 2
  apply propext; omega

theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : LInv s₀ 0 s)
    (hx5 : s.gpr .x5 = BitVec.ofNat 64 (L s₀ / 256)) :
    WP isa (.ite (.zero .x .x5) (.block []) (.loop body (.nonzero .x .x5))) s fun s' =>
      ∃ t, L s₀ - 256 * t < 256 ∧ LInv s₀ t s' := by
  have hL := Xor.L_lt s₀
  apply WP.ite (decide (L s₀ < 256)) (zero_chunks hL hx5)
  · intro hb
    have hb' : L s₀ < 256 := of_decide_eq_true hb
    exact WP.block_nil ⟨0, by simpa using hb', h⟩
  · intro hb
    have hge : 256 ≤ L s₀ := by have := of_decide_eq_false hb; omega
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = L s₀ - 256 * t ∧ 256 ≤ n ∧ LInv s₀ t s
    refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0, by omega, hge, h⟩
    intro n s ⟨t, hn, hge, hi⟩
    refine (body_ok hp (by omega) hi).mono fun u ⟨hu, h5⟩ => ?_
    have hc := Xor.eval_nonzero_ofNat u .x5
      (by omega : (L s₀ - 256 * (t + 1)) / 256 < 2 ^ 64) h5
    by_cases he : L s₀ - 256 * (t + 1) < 256
    · left
      refine ⟨?_, t + 1, he, hu⟩
      simpa only [Nat.div_eq_of_lt he, ne_eq, not_true_eq_false, decide_false] using hc
    · right
      refine ⟨?_, L s₀ - 256 * (t + 1), by omega, t + 1, rfl, by omega, hu⟩
      have hne : (L s₀ - 256 * (t + 1)) / 256 ≠ 0 := by omega
      simpa only [decide_eq_true hne] using hc

end VG.Proof.ChaCha20.AArch64.Neon4
