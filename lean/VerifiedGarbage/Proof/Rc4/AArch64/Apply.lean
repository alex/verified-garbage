import VerifiedGarbage.Proof.Rc4.AArch64.ApplyFinish
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The PRGA

`apply_ok`: `vg_rc4_apply` XORs the next `len` keystream bytes into the
data and leaves the context `len` steps on, preserving the low halves of
`v8`–`v15`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem stepN_i (c : Context) (n : Nat) : (stepN c n).i = c.i + BitVec.ofNat 8 n := by
  induction n with
  | zero => exact (BitVec.add_zero _).symm
  | succ n ih =>
    show (stepN c n).i + 1 = _
    rw [ih, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 8).toNat = 1 from rfl]
    omega

theorem final_i (i : BitVec 8) (x : BitVec 64) :
    (i.setWidth 64 + x).setWidth 8 = i + BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := i.isLt
  omega

theorem saved_kept : ∀ p ∈ saved true, p.2 ≠ .x1 ∧ p.2 ≠ .x2 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x6 ∧
    p.2 ≠ .x7 ∧ p.2 ≠ .x8 := by decide

theorem saved_v : ∀ r ∈ preservedV, r = .v15 ∨ ∃ p ∈ saved true, p.1 = r := by decide

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x0) 258)
    (hd : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region) ∈ s.wr)
    (hs : Mem.Sep (s.gpr .x0) 258 (s.gpr .x1) (s.gpr .x2).toNat) :
    WP isa VG.Impl.Rc4.AArch64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .x0)) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (contextAt t.mem (s.gpr .x0) = result.1 ∧
        bytesAt t.mem (s.gpr .x1) (s.gpr .x2).toNat = result.2) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  unfold VG.Impl.Rc4.AArch64.apply applyRest
  have hN := (s.gpr .x2).isLt
  have x2 : s.gpr .x2 = BitVec.ofNat 64 (s.gpr .x2).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply WP.ite _ (eval_zero' s .x2 x2 hN)
  · intro hz
    have h0 : (s.gpr .x2).toNat = 0 := by simpa using hz
    refine WP.block_nil ⟨?_, fun _ _ => rfl⟩
    rw [h0]
    exact ⟨rfl, rfl⟩
  intro hnz
  have hpos : 0 < (s.gpr .x2).toNat := by simp at hnz; omega
  refine WP.seq (WP.mono (WP.block_append_iff.mp (applySetup_ok hp)) fun _ h => WP.seq (WP.mono h
    fun t ⟨hl, t4, t9, tsv, tg, t15, tm, trd, twr, tsp⟩ => ?_))
  let g := glob s t
  have hg : DataOk g := ⟨by show _ ∈ t.wr; rw [twr]; exact hd, hN⟩
  refine WP.seq (WP.mono (loop_ok g hg _ ⟨_, 0, _, base0_mod _, rfl, hpos,
    by have := sk0_lt (contextAt s.mem (s.gpr .x0)).i; omega, hl⟩) fun u ⟨B, sk, hB, hu⟩ => ?_)
  have hdN : doneAt g g.N sk 0 = g.N := by simp only [doneAt]; omega
  have hpr := hu.prga
  have hdat := hu.data
  rw [hdN] at hpr hdat
  have u0 : u.gpr .x0 = s.gpr .x0 := by
    rw [hu.kept.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact tg _ (by decide)
  have hpu : InRegions u.wr (u.gpr .x0) 258 := by rw [hu.kept.wr, u0]; show InRegions t.wr _ _; rw [twr]; exact hp
  have u9 : u.gpr .x9 = 255#64 := by
    rw [hu.kept.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact t9
  have u4 : (u.gpr .x4).setWidth 8 = (stepN g.c₀ g.N).i := by
    rw [hu.kept.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    show (t.gpr .x4).setWidth 8 = _
    rw [t4, final_i, stepN_i]; rfl
  refine WP.mono (finish_ok hB hu.x8 u9 hpu hpr.table hpr.j u4)
    fun w ⟨wc, wm, wsv, w15, _, _, _⟩ => ?_
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_⟩
  · have wc' : contextAt w.mem (s.gpr .x0) = ⟨(stepN g.c₀ g.N).table, (stepN g.c₀ g.N).i,
        (stepN g.c₀ g.N).j⟩ := by rw [← u0]; exact wc
    rw [wc', update_fst, bytes_length]; rfl
  · refine update_bytes _ _ _ _ _ fun k hk => ?_
    have hsep : ¬ (s.gpr .x1 + BitVec.ofNat 64 k - u.gpr .x0).toNat < 258 := fun h => by
      rw [u0] at h
      refine hs _ h ?_
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk
    have hb : u.mem (g.D + BitVec.ofNat 64 k) = g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k :=
      (hdat.bytes k hk).trans (ite_eq_left hk)
    rw [wm _ hsep]; exact hb
  · rcases saved_v r hr with rfl | ⟨p, hp, rfl⟩
    · rw [w15, hu.vkept _ (by decide) (by decide)]; exact congrArg _ t15
    · obtain ⟨a1, a2, a5, a6, a7, a8⟩ := saved_kept p hp
      rw [wsv p hp, hu.kept.gpr _ a1 a2 a5 a6 a7 a8]
      exact tsv p hp

end VG.Proof.Rc4.AArch64
