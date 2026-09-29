import VerifiedGarbage.Proof.MlKem.AArch64.NttBfly

/-!
# ML-KEM on AArch64: the butterflies of a block

Untrusted: everything here is checked by Lean. The innermost loop of the NTT
and of its inverse: `len` butterflies from `start` with one zeta, for either
butterfly (`inner_ok`).
-/

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- The first `t` butterflies `op` of a block. -/
def blockN (op : Poly → Nat → Nat → Zq → Poly) (P : Poly) (len : Nat) (Z : Zq) (start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => op f j len Z) P

/-- What one butterfly `body` computing `op` does, as `bfly_step` and `ibfly_step` say. -/
def BflySpec (body : List Instr) (op : Poly → Nat → Nat → Zq → Poly) : Prop :=
  ∀ {s₀ : State}, Pre s₀ → ∀ {P : Poly} {Z : Zq} {j len : Nat}, 0 < len → j + len < 256 →
    ∀ {t : State}, St s₀ t → t.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * j) →
      t.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (j + len)) → (t.gpr .x17).toNat = Z.val →
      PolyIs t.mem (fP s₀) P →
      WP isa (.block body) t (BflyPost s₀ (fun P => op P j len Z) j len P t)

theorem bfly_spec : BflySpec bflyBody bfly := fun hp _ _ _ _ hlen hj _ h h2 h3 h17 hP =>
  bfly_step hp hlen hj h h2 h3 h17 hP

theorem ibfly_spec : BflySpec ibflyBody bflyInv := fun hp _ _ _ _ hlen hj _ h h2 h3 h17 hP =>
  ibfly_step hp hlen hj h h2 h3 h17 hP

/-- The registers the butterflies of a block change. -/
abbrev bRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8]

/-- After `t` butterflies of the block from `start`. -/
structure IInv (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (P : Poly) (len : Nat) (Z : Zq)
    (start : Nat) (s : State) (t : Nat) (u : State) : Prop where
  st : St s₀ u
  keep : Keep bRegs s u
  x2 : u.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (start + t))
  x3 : u.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (start + len + t))
  x5 : (u.gpr .x5).toNat = len - t
  poly : PolyIs u.mem (fP s₀) (blockN op P len Z start t)

/-- The `len` butterflies of a block. -/
theorem inner_ok {body : List Instr} {op : Poly → Nat → Nat → Zq → Poly} (hb : BflySpec body op)
    {s₀ : State} (hp : Pre s₀) {P : Poly} {Z : Zq} {len start : Nat} (hlen : 0 < len)
    (hs : start + 2 * len ≤ 256) {s : State} (h : St s₀ s)
    (h2 : s.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * start))
    (h3 : s.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (start + len))) (h5 : (s.gpr .x5).toNat = len)
    (h17 : (s.gpr .x17).toNat = Z.val) (hP : PolyIs s.mem (fP s₀) P) :
    WP isa (.loop (.block body) (.nonzero .x .x5)) s fun s' => St s₀ s' ∧ Keep bRegs s s' ∧
      s'.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (start + len)) ∧
      s'.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (start + 2 * len)) ∧
      PolyIs s'.mem (fP s₀) (blockN op P len Z start len) := by
  refine WP.mono (count_loop hlen (IInv s₀ op P len Z start s) (fun t ht u hu => ?_)
    ⟨h, Keep.refl _ _, by rw [h2, Nat.add_zero], by rw [h3, Nat.add_zero], by rw [h5, Nat.sub_zero],
      hP⟩) fun s' hI => ⟨hI.st, hI.keep, hI.x2, by rw [hI.x3, show start + len + len = start + 2 * len by
        omega], hI.poly⟩
  refine WP.mono (hb hp hlen (j := start + t) (by omega) hu.st hu.x2
    (by rw [hu.x3, show start + len + t = start + t + len by omega])
    (by rw [hu.keep.get .x17, h17]) hu.poly) fun u' hq => ?_
  have x5 : (u'.gpr .x5).toNat = len - (t + 1) := by
    rw [hq.x5, toNat_sub_n (by rw [hu.x5]; simp; omega), hu.x5]
    simp
    omega
  refine ⟨⟨hq.st, (hu.keep.trans hq.keep).mono, by rw [hq.x2, Nat.add_assoc],
    by rw [hq.x3, show start + t + len + 1 = start + len + (t + 1) by omega], x5, ?_⟩, by rw [x5]; omega⟩
  rw [blockN, foldl_range'_succ]
  exact hq.poly

end VG.Proof.MlKem.AArch64.Ntt
