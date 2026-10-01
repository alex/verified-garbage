import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Step
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt serialize block)
open VG.Proof.ChaCha20.AArch64.Neon4 (data_in)

theorem ks_shift (S : CState) {len n k : Nat} (hk : k < len) (ht : 64*n ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (block (ctr (ctr S n) ((k-64*n)/64)))).getD ((k-64*n)%64) 0 := by
  rw [keystream_getD _ hk,Neon4.ctr_add,
    show n+(k-64*n)/64=k/64 by omega,show (k-64*n)%64=k%64 by omega]

abbrev tailR (s₀ : State) (n : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (64 * n), L s₀ - 64 * n⟩

theorem tail_sub {s₀ : State} {n : Nat} (ht : 64 * n ≤ L s₀) :
    Region.Sub (tailR s₀ n) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {n k : Nat} (hk : k < 64 * n) (ht : 64 * n ≤ L s₀) :
    ¬ (tailR s₀ n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

theorem tail_ok {s₀ : State} (hp : XPre s₀) {n : Nat} {s : State} (h : Prefix s₀ n s) (hle : 64*n ≤ L s₀) :
    WP isa Impl.ChaCha20.AArch64.Xor.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hn : (BitVec.ofNat 64 (L s₀ - 64 * n)).toNat = L s₀ - 64 * n :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, tailR s₀ n, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := tail_sub hle
    exact ⟨trivial, rfl, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts, by
      have := hp.nowrap
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega⟩
  have hc : Covers wr s.wr := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s₀, by simp, 64 * n, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hw : WP isa Impl.ChaCha20.AArch64.Xor.xor (s.withRegions [] wr) fun u =>
      abiPreserved (s.withRegions [] wr) u ∧ xorAArch64.post (s.withRegions [] wr) u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
    Xor.xor_x1 BlockImpl.scalar _ hs
  refine WP.narrow hw ?_ hc ?_ BlockImpl.scalar.xorNoFrames
  · rw [h.rd, hp.rd]; exact hc
  · intro u _ _ hsp hf ⟨ha, hpost, h0, h1⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, abiPreserved] at ha
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      h.x0, h.x1, h.x2, hn, h.cnt] at hpost
    refine ⟨⟨?_, hsp.trans h.sp⟩, ?_, h0.trans h.x0, h1.trans h.x3⟩
    · intro r hr
      rw [ha.1 r hr]
      exact h.cs r hr
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < L s₀ := hk
      have ns : ¬ (stR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.st_d _ hh (data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (data_in hk) hh
      by_cases hk' : k < 64 * n
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact not_tail hk' hle
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (64 * n) + BitVec.ofNat 64 (k - 64 * n) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 64 * n) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, ks_shift _ hk (n := n) (by omega)]
        simp


structure CheckKeep (s a : State) : Prop where
  gpr : ∀ r, r ≠ .x5 → a.gpr r = s.gpr r
  mem : a.mem = s.mem
  rd : a.rd = s.rd
  wr : a.wr = s.wr
  sp : a.sp = s.sp

theorem CheckKeep.pre {s a : State} (h : CheckKeep s a) (hp : xorAArch64.pre s) :
    xorAArch64.pre a := by
  simpa only [xorAArch64,h.rd,h.wr,h.gpr .x0 (by decide),h.gpr .x1 (by decide),
    h.gpr .x2 (by decide),h.gpr .x3 (by decide)] using hp

theorem CheckKeep.finish {s a u : State} (h : CheckKeep s a)
    (hu : GprAbi a u ∧ xorAArch64.post a u ∧ u.gpr .x0=a.gpr .x0 ∧ u.gpr .x1=a.gpr .x3) :
    GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  obtain ⟨hab,hp,h0,h1⟩ := hu
  refine ⟨⟨?_,hab.2.trans h.sp⟩,?_,h0.trans (h.gpr _ (by decide)),h1.trans (h.gpr _ (by decide))⟩
  · intro r hr
    have hn : r ≠ .x5 := by revert hr; decide +revert
    exact (hab.1 r hr).trans (h.gpr r hn)
  · simpa only [xorAArch64,h.mem,h.gpr .x0 (by decide),h.gpr .x1 (by decide),
      h.gpr .x2 (by decide)] using hp

theorem check_ok (s : State) (b : Nat) (hb : b < 64) :
    WP isa (.block [.lsr .x .x5 .x2 b]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (L s / 2^b) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,hb,ite_true,Option.some.injEq,isa,runStep_some,exists_eq_left']
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · intro r hr; exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.gpr_write_self,BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.setWidth_eq,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x2).isLt)).symm

theorem check_zero {s : State} {n b : Nat} (_hb : b < 64) (hn : n < 2^64)
    (h : s.gpr .x5=BitVec.ofNat 64 (n/2^b)) :
    isa.eval (.zero .x .x5) s = some (decide (n < 2^b)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from Xor.eval_zero s .x5,h,Xor.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
  congr 2
  simp only [Nat.div_eq_zero_iff,show 2^b ≠ 0 from Nat.ne_of_gt (Nat.two_pow_pos b),false_or]

theorem check3_ok (s : State) (hl : L s < 256) :
    WP isa (.block [.lsr .x .x5 .x2 6,.subImm .x .x5 .x5 3,.lsr .x .x5 .x5 63]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (if L s < 192 then 1 else 0) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,ite_true,Option.some.injEq,isa,runStep_some,exists_eq_left',
    RegUpd.gpr_write_self]
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · intro r hr;simp only [RegUpd.gpr_write,hr,ite_false]
  · simp only [BitVec.setWidth_eq]
    have he : s.gpr .x2 >>> 6 = BitVec.ofNat 64 (L s/64) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [he]
    have hq : L s/64 < 4 := by omega
    have hcases : L s/64=0 ∨ L s/64=1 ∨ L s/64=2 ∨ L s/64=3 := by omega
    rcases hcases with h|h|h|h <;>
      simp only [show (L s < 192) ↔ (L s/64 < 3) by omega,h] <;> decide

theorem check3_nonzero {s : State} {n : Nat}
    (h : s.gpr .x5=BitVec.ofNat 64 (if n < 192 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 192)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 192 <;> simp [hn]

theorem stepped (s : State) (hp : xorAArch64.pre s) (n : Nat) (hn : n ≤ 4) (hl : 64*n ≤ L s) :
    WP isa (.seq (Impl.ChaCha20.AArch64.Small.step n) Impl.ChaCha20.AArch64.Xor.xor) s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.seq
  exact (step_ok s (XPre.of s hp) n hn hl).mono fun _ h => tail_ok (XPre.of s hp) h hl

theorem short_ok (s : State) (hp : xorAArch64.pre s) (hl : L s < 256) :
    WP isa Impl.ChaCha20.AArch64.Small.short s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.seq
  refine (check_ok s 7 (by decide)).mono fun a ⟨ha,h5⟩ => ?_
  apply WP.ite (decide (L s < 128)) (check_zero (by decide) (Xor.L_lt s) h5)
  · intro _
    have hw : WP isa Impl.ChaCha20.AArch64.Xor.xor a fun u =>
      abiPreserved a u ∧ xorAArch64.post a u ∧ u.gpr .x0=a.gpr .x0 ∧ u.gpr .x1=a.gpr .x3 :=
        Xor.xor_x1 BlockImpl.scalar a (ha.pre hp)
    exact hw.mono fun _ h => ha.finish ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩
  · intro hshort
    have hge : 128 ≤ L s := by have := of_decide_eq_false hshort;omega
    apply WP.seq
    apply WP.seq
    refine (check3_ok a (by simpa only [L,ha.gpr .x2 (by decide)] using hl)).mono fun b ⟨hb,hb5⟩ => ?_
    have hla : L a=L s := by simp only [L,ha.gpr .x2 (by decide)]
    rw [hla] at hb5
    apply WP.ite (decide (L s < 192)) (check3_nonzero hb5)
    · intro h192
      have hlen : 128 ≤ L b := by simp only [L,hb.gpr .x2 (by decide),ha.gpr .x2 (by decide)];exact hge
      exact ((step_ok b (XPre.of b (hb.pre (ha.pre hp))) 2 (by decide) hlen).mono fun c hc =>
        (tail_ok (XPre.of b (hb.pre (ha.pre hp))) hc hlen).mono fun _ hu => ha.finish (hb.finish hu))
    · intro h192
      have hge192 : 192 ≤ L s := by have := of_decide_eq_false h192;omega
      have hlen : 192 ≤ L b := by simp only [L,hb.gpr .x2 (by decide),ha.gpr .x2 (by decide)];exact hge192
      exact ((step_ok b (XPre.of b (hb.pre (ha.pre hp))) 3 (by decide) hlen).mono fun c hc =>
        (tail_ok (XPre.of b (hb.pre (ha.pre hp))) hc hlen).mono fun _ hu => ha.finish (hb.finish hu))

theorem correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun u =>
      abiPreserved s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.withPreservedV (hc := by lit_decide)
  apply WP.seq
  refine (check_ok s 8 (by decide)).mono fun a ⟨ha,h5⟩ => ?_
  apply WP.ite (decide (L s < 256)) (check_zero (by decide) (Xor.L_lt s) h5)
  · intro hshort
    have hlen : L a < 256 := by simp only [L,ha.gpr .x2 (by decide)];exact of_decide_eq_true hshort
    exact (short_ok a (ha.pre hp) hlen).mono fun _ hu => ha.finish hu
  · intro _
    exact (Neon4.correct a (ha.pre hp)).mono fun _ h => ha.finish ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩

theorem xor_noFrames : Impl.ChaCha20.AArch64.Small.xor.noFrames=true := by lit_decide

end VG.Proof.ChaCha20.AArch64.Small
