import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)
open VG.Proof.ChaCha20.AArch64.Neon4 (data_in)

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

abbrev tailR (s₀ : State) (t : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (320 * t), L s₀ - 320 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 320 * t ≤ L s₀) :
    Region.Sub (tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 320 * t) (ht : 320 * t ≤ L s₀) :
    ¬ (tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem tail_ok {s₀ : State} (hp : XPre s₀) {t : Nat} {s : State} (h : LInv s₀ t s) (hcs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hle := h.le
  have hn : (BitVec.ofNat 64 (L s₀ - 320 * t)).toNat = L s₀ - 320 * t :=
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
    · exact ⟨dR s₀, by simp, 320 * t, rfl, by dsimp; omega⟩
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
      exact hcs r hr
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < L s₀ := hk
      have ns : ¬ (stR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.st_d _ hh (data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (data_in hk) hh
      by_cases hk' : k < 320 * t
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact not_tail hk' h.le
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (320 * t) + BitVec.ofNat 64 (k - 320 * t) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 320 * t) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, ks_shift _ hk (t := t) (by omega)]

theorem nonzero_short {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 320 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 320)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 320 <;> simp [hn]

theorem correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Mixed5.xor s fun u =>
      abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  apply WP.withPreservedV (hc := by lit_decide)
  apply WP.seq
  refine (init_ok s).mono fun a ⟨hi,hcs,h5⟩ => ?_
  apply WP.seq
  have hb : WP isa (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block Impl.ChaCha20.AArch64.Mixed5.enter)
        (.seq (.loop Impl.ChaCha20.AArch64.Mixed5.body (.zero .x .x5))
          (.block Impl.ChaCha20.AArch64.Mixed5.leave)))) a fun u =>
      ∃ t, LInv s t u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) := by
    apply WP.ite (decide (L s < 320)) (nonzero_short h5)
    · intro _; exact WP.block_nil ⟨0,hi,hcs⟩
    · intro hshort
      have hge : 320 ≤ L s := by have hh := of_decide_eq_false hshort; omega
      apply WP.seq
      refine (enter_ok (XPre.of s hp) hi hcs).mono fun b hb => ?_
      apply WP.seq
      refine (bulk_ok (XPre.of s hp) hb hge).mono fun c ⟨t,_,hc⟩ => ?_
      exact (leave_ok (XPre.of s hp) hc).mono fun _ ⟨hd,hcs⟩ => ⟨t,hd,hcs⟩
  refine hb.mono fun u ⟨t,hu,hcs⟩ => tail_ok (XPre.of s hp) hu hcs

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa Impl.ChaCha20.AArch64.Mixed5.xor s t u ∧ abiPreserved s u ∧
      xorAArch64.post s u :=
  (correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : Impl.ChaCha20.AArch64.Mixed5.xor.noFrames = true := by lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub
    Impl.ChaCha20.AArch64.Mixed5.xor := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => VG.Proof.ChaCha20.AArch64.Xor.agree₀ hp) (by taint_decide)

theorem xor_verified : Verified AArch64.target Impl.ChaCha20.AArch64.Mixed5.xor
    (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract,Spec.ChaCha20.xorSig,AArch64.abi,AArch64.argRegs,
      xorAArch64] [VG.Proof.ChaCha20.AArch64.Xor.sat] using VG.Proof.ChaCha20.AArch64.Xor.sat)

end VG.Proof.ChaCha20.AArch64.Mixed5
