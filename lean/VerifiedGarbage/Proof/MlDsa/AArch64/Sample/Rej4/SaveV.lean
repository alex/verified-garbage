import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_str WP.cons)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (saveV oSave)

def vSaveR (σ : State) : Region := ⟨at' σ (oSave+80),64⟩

theorem saveV_step {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x2 = p)
    (hw : InRegions s.wr (p+BitVec.ofNat 64 (oSave+80+8*i)) 8) :
    WP isa (.block ([.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x2 (oSave+80+8*i)] : List Instr)) s
      fun t => RegKeep [.x8] s t ∧ t.v = s.v ∧
        t.mem = s.mem.writeW (p+BitVec.ofNat 64 (oSave+80+8*i)) (vdword (s.v (vreg (8+i))) 0) := by
  refine WP.cons (s' := s.write .x .x8 (vdword (s.v (vreg (8+i))) 0)) rfl ?_
  have h1 := Upd.write64 s .x8 (vdword (s.v (vreg (8+i))) 0)
  refine wp_str ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [h1.other .x2 (by decide),hp]) (by rw [h1.wr]; exact hw)
    fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact (RegKeep.upd h1).trans (RegKeep.mupd h2) |>.mono (by simp)
  · exact h2.vec.trans h1.vec
  · rw [h2.mem,h1.mem,h1.gpr]

theorem saveV_ok {σ s : State} (hp : Pre σ) (hw : s.wr = σ.wr) (hs : s.gpr .x2 = scr σ) :
    WP isa (.block saveV) s fun t => RegKeep [.x8] s t ∧ t.v = s.v ∧
      Frame [vSaveR σ] s.mem t.mem ∧ ∀ i < 8,
        t.mem.readW (at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0 := by
  unfold saveV
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.v = s.v ∧ Frame [vSaveR σ] s.mem t.mem ∧ ∀ i < k,
      t.mem.readW (at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (saveV_step hk ((ht.gpr .x2 (by decide)).trans hs)
    (in_scr hp (ht.wr.trans hw) (by dsimp only [oSave]; omega))) fun u ⟨hu,hvu,hm⟩ => ?_
  change u.mem = t.mem.writeW (at' σ (oSave+80+8*k)) (vdword (t.v (vreg (8+k))) 0) at hm
  refine ⟨(ht.trans hu).mono (by simp),hvu.trans hv,?_,?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (scr σ) (d := oSave+80+8*k) (e := oSave+80) (n := 8) (k := 64)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm,hv]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (at' σ (oSave+80+8*i)) 8 (at' σ (oSave+80+8*k)) 8 :=
        Offset.sep (scr σ) (d := oSave+80+8*i) (e := oSave+80+8*k) (n := 8) (k := 8)
          (by omega) (by dsimp only [oSave]; omega) (by dsimp only [oSave]; omega)
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
