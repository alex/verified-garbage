import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VMem wp_strq)

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v := by
  have h := Mem.readW_writeW_self m p 16 v (by decide)
  exact h

/-- Store paired states while framing the rest of the sampler's scratch space. -/
theorem store_ok {s : State} {p : Addr} {r : Reg} {A B : Spec.Sha3.State}
    (hr : s.gpr r = p) (hp : Pairs s A B)
    (hw : ∀ i < 25, InRegions s.wr (wordAddr p i) 16) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.store r)) s fun s' =>
      VMem s s' s'.mem ∧ PairAt s'.mem p A B ∧ Frame [pairR p] s.mem s'.mem := by
  unfold Impl.Sha3.AArch64.Neon.Pair.store
  rw [List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VMem s s' s'.mem ∧ Frame [pairR p] s.mem s'.mem ∧
      ∀ i < k, s'.mem.read (wordAddr p i) 16 = ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hmem,hframe,hvals⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun s' ⟨hmem,hframe,hvals⟩ => ⟨hmem,hvals,hframe⟩
  refine wp_strq (t := vreg k) (a := wordAddr p k) (by omega)
    (by rw [hmem.gpr,hr]; rfl) (by rw [hmem.wr]; exact hw k hk)
    fun s'' h => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨h.gpr.trans hmem.gpr,h.v.trans hmem.v,rfl,h.rd.trans hmem.rd,h.wr.trans hmem.wr,h.sp.trans hmem.sp⟩
  · rw [h.mem]
    exact hframe.write (List.mem_singleton_self _) _ (pair_contains p hk)
  · intro i hi
    rw [h.mem]
    by_cases he : i = k
    · subst i
      rw [read_write16,hmem.v,hp k hk]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega)
end VG.Proof.Sha3.AArch64.Neon
