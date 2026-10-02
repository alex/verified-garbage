import VerifiedGarbage.Proof.Ed25519.X86.BitsExpandStep
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure ExpandedBits (x p : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  frame : Frame [sub x 7168 n] s₀.mem s.mem
  bits : ∀ k < n, s.mem (addr x (7168 + k)) =
    BitVec.ofNat 8 ((s₀.mem (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2)

theorem expandPrefix_ok {x p : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (hp : s₀.gpr .esi = p) {bytes : Nat} (hb : bytes ≤ 64)
    (hr : ∀ i < bytes, InRegions (s₀.rd ++ s₀.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (sub p i 1).Disjoint (sub x 7168 (8 * bytes))) :
    ∀ n ≤ 8 * bytes, WP isa (.block ((List.range n).flatMap expandScalarBit)) s₀ (ExpandedBits x p s₀ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (expandPrefix_ok hc hp hb hr hs n (by omega_using [hn]))
      fun u hu => ?_)
    have cu := hu.keep.ctx hc
    have hnb : n / 8 < bytes := by omega_using [hn]
    have input : u.mem (addr p (n / 8)) = s₀.mem (addr p (n / 8)) := by
      apply hu.frame
      intro r hmem; rw [List.mem_singleton.mp hmem]
      have hd := (hs (n / 8) hnb).sub_right
        (sub_sub (o := 7168) (n := n) (o' := 7168) (n' := 8 * bytes)
          hc.fit (Nat.le_refl _) (by omega_using [hn]) (by decide))
      exact hd _ (Region.contains_self _ _)
    refine WP.mono (expandScalarBit_ok cu (hu.keep.esi.trans hp) (by omega_using [hn, hb])
      (by rw [hu.keep.rd, hu.keep.wr]; exact hr _ hnb)) fun t ⟨kt, mt⟩ => ?_
    rw [input] at mt
    refine ⟨hu.keep.trans kt, ?_, fun k hk => ?_⟩
    · rw [mt]
      have hf := frameWiden hu.frame hc.fit (Nat.le_refl _) (by omega_using []) (by decide)
        (n' := n + 1)
      exact hf.writeW (List.mem_singleton_self _) _
        (sub_contains (by omega_using [hc.fit, hn, hb]) (by omega_using []) (by omega_using []) (by decide))
    · rw [mt]
      by_cases he : k = n
      · subst he; exact bits_byte_write_self _ _ _
      · rw [bits_byte_write_ne _ _ (by omega_using [hc.fit, hb, hn, hk])
          (by omega_using [hc.fit, hb, hn]) (by omega_using [he])]
        exact hu.bits k (by omega_using [hk, he])

theorem expanded_scalar_bit {p : BitVec 32} (m : Mem) {bytes k : Nat}
    (hp : p.toNat + bytes ≤ 2 ^ 32) (hk : k < 8 * bytes) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (p.setWidth 64) bytes) / 2 ^ k % 2 =
      (m (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2 := by
  rw [decodeLE_eq]
  have he := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt m (p.setWidth 64) bytes) k
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at he
  rw [he]
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega_using [hk] : k / 8 < bytes), Option.map_some, Option.getD_some]
  rw [addr_eq (by omega_using [hp, hk])]

theorem expandScalarBits_ok {x p : BitVec 32} {s : State} (hc : Ctx x s)
    (hp : s.gpr .esi = p) {bytes : Nat} (hb : bytes ≤ 64)
    (hfit : p.toNat + bytes ≤ 2 ^ 32)
    (hr : ∀ i < bytes, InRegions (s.rd ++ s.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (sub p i 1).Disjoint (sub x 7168 (8 * bytes))) :
    WP isa (.block (expandScalarBits bytes)) s fun t => Keep s t ∧ Frame [sub x 7168 (8 * bytes)] s.mem t.mem ∧
      ∀ k < 8 * bytes, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (p.setWidth 64) bytes) / 2 ^ k % 2) := by
  refine WP.mono (expandPrefix_ok hc hp hb hr hs (8 * bytes) (Nat.le_refl _)) fun t ht =>
    ⟨ht.keep, ht.frame, fun k hk => ?_⟩
  rw [ht.bits k hk, expanded_scalar_bit s.mem hfit hk]
theorem loadScalarBits_ok {x p : BitVec 32} {s : State} (hc : Ctx x s)
    (hp : wd s.mem x 20 = p) {bytes : Nat} (hb : bytes ≤ 64)
    (hfit : p.toNat + bytes ≤ 2 ^ 32)
    (hr : ∀ i < bytes, InRegions (s.rd ++ s.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (sub p i 1).Disjoint (sub x 7168 (8 * bytes))) :
    WP isa (.block (loadScalarBits bytes)) s fun t => ScalarKeep s t ∧
      Frame [sub x 7168 (8 * bytes)] s.mem t.mem ∧
      ∀ k < 8 * bytes, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (p.setWidth 64) bytes) / 2 ^ k % 2) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  have ku := scalarUpd hu
  refine WP.mono (expandScalarBits_ok (ku.ctx hc) (hu.gpr.trans hp) hb hfit
    (by intro i hi; rw [hu.rd, hu.wr]; exact hr i hi) hs) fun t ⟨kt, ft, bt⟩ => ?_
  rw [hu.mem] at ft bt
  exact ⟨ku.trans (Keep.scalar kt), ft, bt⟩

end VG.Proof.Ed25519.X86
