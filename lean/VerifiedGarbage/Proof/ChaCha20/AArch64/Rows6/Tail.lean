import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends

namespace VG.Proof.ChaCha20.AArch64.Rows6

open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

abbrev tailR (s₀ : State) (t : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (384 * t), L s₀ - 384 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 384 * t ≤ L s₀) :
    Region.Sub (tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 384 * t) (ht : 384 * t ≤ L s₀) :
    ¬ (tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
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

theorem tail_ok {s₀ : State} (hp : XPre s₀) {t : Nat} {s : State} (h : LInv s₀ t s) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hle := h.le
  have hn : (BitVec.ofNat 64 (L s₀ - 384 * t)).toNat = L s₀ - 384 * t :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, tailR s₀ t, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := tail_sub h.le
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
    · exact ⟨dR s₀, by simp, 384 * t, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hw : WP isa Impl.ChaCha20.AArch64.Small.xor (s.withRegions [] wr) fun u =>
      abiPreserved (s.withRegions [] wr) u ∧ xorAArch64.post (s.withRegions [] wr) u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
    VG.Proof.ChaCha20.AArch64.Small.correct _ hs
  refine WP.narrow hw ?_ hc ?_ VG.Proof.ChaCha20.AArch64.Small.xor_noFrames
  · rw [h.rd, hp.rd]; exact hc
  · intro u _ _ hsp hf ⟨ha, hpost, h0, h1⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, abiPreserved] at ha
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      h.x0, h.x1, h.x2, hn, h.cnt] at hpost
    refine ⟨⟨?_, hsp.trans h.sp⟩, ?_, h0.trans h.x0, h1.trans h.x3⟩
    · intro r hr
      rw [ha.1 r hr]
      apply h.keep r <;> intro he <;> subst r <;> simp [preserved] at hr
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < L s₀ := hk
      have ns : ¬ (stR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.st_d _ hh (data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (data_in hk) hh
      by_cases hk' : k < 384 * t
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact not_tail hk' h.le
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (384 * t) + BitVec.ofNat 64 (k - 384 * t) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 384 * t) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, ks_shift _ hk (t := t) (by omega)]

theorem raw_correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Rows6.raw s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  apply WP.seq
  refine (init_ok s).mono fun u ⟨hi,h5⟩ => ?_
  apply WP.seq
  refine (bulk_ok (XPre.of s hp) hi h5).mono fun v ⟨t,_,hv⟩ => ?_
  exact tail_ok (XPre.of s hp) hv

end VG.Proof.ChaCha20.AArch64.Rows6
