import VerifiedGarbage.Proof.X448.Arm.Mem
import VerifiedGarbage.Proof.X25519.Arm.Pass

/-!
# X448 on ARMv7: arithmetic steps

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_ldr)

/-- Load a coefficient and propagate its carry. -/
def carryBlock (o a i : Nat) : List Instr :=
  [ld .r3 (a + 4 * i)] ++ VG.Impl.X448.Arm.carryStep .r0 (o + 4 * i)

theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 4 * i + 4 ≤ 4096) (ha : a + 4 * i + 4 ≤ 4096)
    (hb : (word s.mem base (a + 4 * i)).toNat + (s.gpr .r5).toNat < 2 ^ 32) :
    let v := (word s.mem base (a + 4 * i)).toNat + (s.gpr .r5).toNat
    WP isa (.block (carryBlock o a i)) s fun s' =>
      (s'.gpr .r5).toNat = v / radix ∧
      s'.mem = s.mem.writeW (off base (o + 4 * i)) (BitVec.ofNat 32 (v % radix)) ∧
      Keeps [.r3, .r5, .r4] s s' := by
  intro v
  unfold carryBlock ld
  refine wp_ldr (a := off base (a + 4 * i)) (by omega) (hs.ea (by omega))
    (hs.read (by omega)) fun t ht => ?_
  have h5 : t.gpr .r5 = s.gpr .r5 := ht.other _ (by decide)
  have h3 : (t.gpr .r3).toNat = (word s.mem base (a + 4 * i)).toNat := by rw [ht.gpr]
  refine WP.mono (VG.Proof.X25519.Arm.carryStep_ok
    (a := off base (o + 4 * i)) (by decide) (by omega)
    (by rw [ht.other .r0 (by decide)]; exact hs.ea (by omega))
    (by rw [ht.wr]; exact hs.write (by omega))
    (by rw [ht.other .r6 (by decide)]; exact hs.mask)
    (by rw [h3, h5]; exact hb)) fun u ⟨hc, ⟨w, hw, hm⟩, hk⟩ => ?_
  rw [h3, h5] at hc hw
  refine ⟨hc, ?_, (fun r hr => ?_), hk.rd.trans ht.rd, hk.wr.trans ht.wr⟩
  · have he : w = BitVec.ofNat 32 (v % radix) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % radix)
        (Nat.lt_trans (Nat.mod_lt v (by decide : 0 < radix)) (by decide : radix < 2 ^ 32))]
      rfl
    rw [hm, ht.mem, he]
  · have hr' : r ∉ [Reg.r3, .r4, .r5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨hr.1, hr.2.2, hr.2.1⟩
    rw [hk.gpr r hr']
    apply ht.other
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact hr.1

end VG.Proof.X448.Arm
