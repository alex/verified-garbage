import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

namespace VG.Proof.ChaCha20.AArch64.Rows6

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

theorem less6 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n >>> 6) - BitVec.ofNat 64 6) >>> 63 =
      BitVec.ofNat 64 (if n < 384 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  have hd : n / 2 ^ 6 < 2 ^ 58 := by omega
  by_cases h : n < 384
  · rw [ite_eq_left h]
    have hb : n / 2 ^ 6 < 6 := by omega
    omega
  · rw [ite_eq_right h]
    have hb : 6 ≤ n / 2 ^ 6 := by omega
    omega

theorem check_ok (s : State) :
    WP isa (.block check) s fun u =>
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < 384 then 1 else 0) ∧
      (∀ r, r ≠ .x5 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, ite_true, isa, runStep_some, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_,fun r hr => by simp only [hr,ite_false],rfl,rfl,rfl,rfl,rfl⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using less6 (s.gpr .x2).toNat (s.gpr .x2).isLt


/-- Before six-block chunk t. x0/x3 and all but the two scratch registers
are retained, except the advancing data pointer and remaining length. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (384 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 384 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 384 * t ≤ L s₀
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (6 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 384 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem ctr_add (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.getElem_set_self, Vector.set_set, BitVec.ofNat_add, BitVec.add_assoc]

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 384 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (block (ctr (ctr S (6 * t)) ((k - 384 * t) / 64)))).getD
        ((k - 384 * t) % 64) 0 := by
  rw [keystream_getD _ hk, ctr_add, show 6 * t + (k - 384 * t) / 64 = k / 64 by omega,
    show (k - 384 * t) % 64 = k % 64 by omega]

 theorem next_ok (s : State) (hlen : 384 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block next) s fun u =>
      u.gpr .x1 = s.gpr .x1 + 384 ∧ u.gpr .x2 = s.gpr .x2 - 384 ∧
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat - 384 < 384 then 1 else 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 6 ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next,check,ite_false,
    List.cons_append,List.nil_append,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,ite_true,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,?_,?_,?_,trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 384 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 384) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he,less6 _ (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5; simp only [h1,h2,h4,h5,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter s.mem (s.gpr .x0)
      (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 48) 4 + BitVec.ofNat 32 6)
    simp only [Mem.writeW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (384 * t), 384⟩

theorem win_sub {s₀ : State} {t : Nat} (h : 384 * t + 384 ≤ L s₀) :
    Region.Sub (win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h := Xor.L_lt s₀; omega)

theorem chunkData {s₀ s u : State} {t : Nat} (h : LInv s₀ t s)
    (hge : 384 * t + 384 ≤ L s₀)
    (hu : ∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
      s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0)
    (hf : Frame [⟨s.gpr .x1, 384⟩] s.mem u.mem) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 384 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := Xor.L_lt s₀
  by_cases hin : 384 * t ≤ k ∧ k < 384 * t + 384
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 384 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    have hh := hu (k - 384 * t) (by omega)
    rw [he, h.data k hk, ite_eq_right (by omega), h.x0, h.cnt, ← ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains, Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hf (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; rw [h.x1]; exact hx)
    rw [hh, h.data k hk]
    by_cases hold : k < 384 * t
    · rw [ite_eq_left hold, ite_eq_left (by omega)]
    · rw [ite_eq_right hold, ite_eq_right (by omega)]

theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 384 * t + 384 ≤ L s₀) {s : State} (h : LInv s₀ t s) :
    WP isa body s fun s' => LInv s₀ (t + 1) s' ∧
      s'.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 384 * (t + 1) < 384 then 1 else 0) := by
  have hL := Xor.L_lt s₀
  have hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [h.rd,h.wr,hp.rd,hp.wr,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.rd,h.wr,hp.rd,hp.wr,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [h.wr,hp.wr,h.x1,BitVec.add_assoc,← BitVec.ofNat_add]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine (chunk_ok s hin hctr hout).mono fun u ⟨hu, hf, hs⟩ => ?_
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (6 * t) := by
    rw [← h.cnt]
    apply Xor.stateAt_frame hf
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [h.x1]; exact hp.st_d.sub_right (win_sub hge)
  have hdata := chunkData h hge hu hf
  have hx0 : u.gpr .x0 = st s₀ := (hs.gpr _ (by decide)).trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (384 * t) := (hs.gpr _ (by decide)).trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 384 * t) := (hs.gpr _ (by decide)).trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := (hs.gpr _ (by decide)).trans h.x3
  have hw : u.wr = [stR s₀, dR s₀, bR s₀] := hs.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hs.rd, h.rd, hp.rd, hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 384 * t := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine (next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1, hv2, hv5, hkeep, hctr, hframe, hrd, hwr, hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (384 * (t + 1)) := by
    rw [hv1, hx1, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (384 * t) + BitVec.ofNat 64 384 = _
    rw [← BitVec.ofNat_add, show 384 * t + 384 = 384 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 384 * (t + 1)) := by
    rw [hv2, hx2]
    change BitVec.ofNat 64 (L s₀ - 384 * t) - BitVec.ofNat 64 384 = _
    rw [Offset.ofNat_sub_ofNat (by omega), show L s₀ - 384 * t - 384 = L s₀ - 384 * (t + 1) by omega]
  refine ⟨⟨?_, hptr, hrem, ?_, by omega, ?_, hrd.trans (hs.rd.trans h.rd),
    hwr.trans (hs.wr.trans h.wr), hsp.trans (hs.sp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx3]
  · intro r h1 h2 h4 h5
    rw [hkeep r h1 h2 h4 h5, hs.gpr r h4]; exact h.keep r h1 h2 h4 h5
  · rw [hx0, hcnt, ctr_add, show 6 * t + 6 = 6 * (t + 1) by omega] at hctr
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
  · rw [hv5, hlen, show L s₀ - 384 * t - 384 = L s₀ - 384 * (t + 1) by omega]

theorem init_ok (s : State) :
    WP isa (.block check) s fun u => LInv s 0 u ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s < 384 then 1 else 0) := by
  refine (check_ok s).mono fun u ⟨h5,hg,hm,hr,hw,hv,hsp⟩ => ⟨?_,h5⟩
  refine ⟨hg _ (by decide),?_,?_,hg _ (by decide),by omega,?_,hr,hw,hsp,?_,?_,?_⟩
  · rw [hg _ (by decide)]; simp [dp]
  · rw [hg _ (by decide)]; simp [L]
  · intro r _ _ _ h5; exact hg r h5
  · rw [hm]; exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; rw [hm]; simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]
  · rw [hm]; exact Frame.refl _ _

theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : LInv s₀ 0 s)
    (hx5 : s.gpr .x5 = BitVec.ofNat 64 (if L s₀ < 384 then 1 else 0)) :
    WP isa (.ite (.nonzero .x .x5) (.block []) (.loop body (.zero .x .x5))) s fun u =>
      ∃ t, L s₀ - 384 * t < 384 ∧ LInv s₀ t u := by
  have hL := Xor.L_lt s₀
  have he := Xor.eval_nonzero_ofNat s .x5 (by split <;> omega) hx5
  have he' : isa.eval (.nonzero .x .x5) s = some (decide (L s₀ < 384)) := by
    by_cases hl : L s₀ < 384 <;> simpa [hl] using he
  apply WP.ite (decide (L s₀ < 384)) he' 
  · intro hb
    have hb' := of_decide_eq_true hb
    exact WP.block_nil ⟨0,by simpa using hb',h⟩
  · intro hb
    have hge : 384 ≤ L s₀ := by have := of_decide_eq_false hb; omega
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = L s₀ - 384 * t ∧ 384 ≤ n ∧ LInv s₀ t s
    refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0,by omega,hge,h⟩
    intro n s ⟨t,hn,hge,hi⟩
    refine (body_ok hp (by omega) hi).mono fun u ⟨hu,h5⟩ => ?_
    have hc : isa.eval (.zero .x .x5) u =
        some (decide ((if L s₀ - 384 * (t + 1) < 384 then 1 else 0) = 0)) := by
      change eval (.zero .x .x5) u = _
      rw [Xor.eval_zero u .x5,h5,Xor.ofNat_beq_zero (by split <;> omega)]
    by_cases hl : L s₀ - 384 * (t + 1) < 384
    · left
      refine ⟨?_,t + 1,hl,hu⟩
      simpa [hl] using hc
    · right
      refine ⟨?_,L s₀ - 384 * (t + 1),by omega,t + 1,rfl,by omega,hu⟩
      simpa [hl] using hc

end VG.Proof.ChaCha20.AArch64.Rows6
