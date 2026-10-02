import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64 (wp_str Mupd)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (saveG oSave saved)

theorem saveG_ok {σ : State} (hp : Pre σ) :
    WP isa (.block saveG) σ fun t => Mupd σ t t.mem ∧ Frame [saveR σ] σ.mem t.mem ∧
      ∀ i < 10,t.mem.readW (at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!) := by
  unfold saveG
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Mupd σ t t.mem ∧ Frame [saveR σ] σ.mem t.mem ∧
      ∀ i < k,t.mem.readW (at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!))
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 10 (Nat.le_refl _) σ
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_str (a := at' σ (oSave+8*k)) ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [ht.gpr]; rfl) (in_scr hp ht.wr (by dsimp only [oSave]; omega)) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains (scr σ) (d := oSave+8*k) (e := oSave) (n := 8) (k := 144) (by omega) (by omega) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (at' σ (oSave+8*i)) 8 (at' σ (oSave+8*k)) 8 :=
        Offset.sep (scr σ) (d := oSave+8*i) (e := oSave+8*k) (n := 8) (k := 8) (by omega) (by dsimp only [oSave]; omega) (by dsimp only [oSave]; omega)
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
