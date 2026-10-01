import VerifiedGarbage.Proof.Ed25519.X86.CopyWords

/-! Untrusted: saving and loading four consecutive field coordinates. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def tablePoint (m : Mem) (x : BitVec 32) (o : Nat) : Spec.Ed25519.Point :=
  ⟨F m x o, F m x (o + 32), F m x (o + 64), F m x (o + 96)⟩

theorem fields_of_words {m m' : Mem} {x : BitVec 32} {a o : Nat}
    (h : ∀ k < 32, wd m' x (o + 4 * k) = wd m x (a + 4 * k))
    (j : Nat) (hj : j < 4) : F m' x (o + 32 * j) = F m x (a + 32 * j) := by
  apply congrArg VG.Proof.X25519.toFe
  apply num_congr
  intro k hk
  have hv := h (8 * j + k) (by omega)
  have he : o + 32 * j + 4 * k = o + 4 * (8 * j + k) := by omega
  have he' : a + 32 * j + 4 * k = a + 4 * (8 * j + k) := by omega
  exact congrArg BitVec.toNat (he.symm ▸ he'.symm ▸ hv)

theorem point_mk_congr {a b c d a' b' c' d' : Spec.X25519.Fe}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    Spec.Ed25519.Point.mk a b c d = Spec.Ed25519.Point.mk a' b' c' d' := by
  cases ha; cases hb; cases hc; cases hd; rfl

theorem table_point_of_words {m m' : Mem} {x : BitVec 32} {a o : Nat}
    (h : ∀ k < 32, wd m' x (o + 4 * k) = wd m x (a + 4 * k)) :
    tablePoint m' x o = tablePoint m x a := by
  have h0 := fields_of_words h 0 (by decide)
  have h1 := fields_of_words h 1 (by decide)
  have h2 := fields_of_words h 2 (by decide)
  have h3 := fields_of_words h 3 (by decide)
  exact point_mk_congr h0 h1 h2 h3

theorem pointToTable_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 192 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      CopyKeep x o 128 s t ∧ tablePoint t.mem x o = point (env s.mem x) 0 1 2 3 := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edi .edx (by decide) (by decide) 0 o 64 0 32
    hb hp (by decide) (by omega) (Or.inl hlo) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  refine ⟨hk, ?_⟩
  exact table_point_of_words hv

theorem pointFromTable_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 192 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      CopyKeep x 64 128 s t ∧ point (env t.mem x) 0 1 2 3 = tablePoint s.mem x o := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edx .edi (by decide) (by decide) o 0 0 64 32
    hp hb (by omega) (by decide) (Or.inr hlo) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  exact ⟨hk, table_point_of_words hv⟩

theorem table_env {x : BitVec 32} {o n : Nat} {m m' : Mem}
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h : Frame [sub x o n] m m')
    (ho : 768 ≤ o) (hn : o + n ≤ 8192) : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h hx hn (by simp only [offset]; omega)
    (Or.inl (by simp only [offset]; omega))

theorem tablePoint_frame {x : BitVec 32} {o n a : Nat} {m m' : Mem}
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h : Frame [sub x o n] m m')
    (ho : o + n ≤ 8192) (ha : a + 128 ≤ 8192) (hsep : a + 128 ≤ o ∨ o + n ≤ a) :
    tablePoint m' x a = tablePoint m x a := by
  apply table_point_of_words
  intro k hk
  exact wd_frame1 h hx ho (by omega) (by omega)

theorem CopyKeep.high {x : BitVec 32} {s t : State} (h : CopyKeep x 64 128 s t)
    (hc : Ctx x s) (i : Slot) (hi : 4 ≤ i.val) : env t.mem x i = env s.mem x i := by
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h.frame hc.fit (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.X86
