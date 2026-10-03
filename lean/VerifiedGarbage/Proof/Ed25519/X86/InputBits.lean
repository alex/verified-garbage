import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Impl.Ed25519.X86.BitsExpand
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Impl.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.CommonInput

/-! Merged from `Proof.Ed25519.X86.BitsExpand`. -/
section
/-! Merged from `Proof.Ed25519.X86.BitsExpandStep`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalar_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ t, Wp.Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  change (s.gpr b + BitVec.ofNat 32 o).setWidth 64 = a at ha
  simp only [exec, State.store8, State.ea, ha, hout, ite_true]

theorem doubled_byte_bit (b : Byte) (j : Nat) :
    ((((b.setWidth 32 + b.setWidth 32) >>> (j + 1)) &&& 1).setWidth 8) =
      BitVec.ofNat 8 (b.toNat / 2 ^ j % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  change (((b.setWidth 32 + b.setWidth 32) >>> (j + 1)).toNat &&& (2 ^ 1 - 1)) % 2 ^ 8 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat + b.toNat) (b := 2 ^ 32) (by omega_using [hb]),
    show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ'], ← Nat.div_div_eq_div_mul,
    show (b.toNat + b.toNat) / 2 = b.toNat by omega_using []]
  rfl

theorem expandScalarBit_ok {x p : BitVec 32} {s : State} (hc : Ctx x s) (hp : s.gpr .esi = p)
    {k : Nat} (hk : k < 512) (hr : InRegions (s.rd ++ s.wr) (addr p (k / 8)) 1) :
    WP isa (.block (expandScalarBit k)) s fun t => Keep s t ∧
      t.mem = s.mem.writeW (addr x (7168 + k))
        (BitVec.ofNat 8 ((s.mem (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2)) := by
  refine scalar_ld8 (by rw [hp]) hr fun u₁ h₁ => ?_
  refine Wp.wp_add fun u₂ h₂ _ => Wp.wp_shr
    (by have h := Nat.mod_lt k (by decide : 0 < 8); omega_using [h]) fun u₃ h₃ _ => ?_
  refine Wp.wp_andi fun u₄ h₄ => ?_
  have k₄ := (updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans (updKeep h₄)))
  have c₄ := k₄.ctx hc
  refine scalar_store8 (by rw [c₄.edi]) (c₄.inW (by omega_using [hk]) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨k₄.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩
  rw [ht.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  change s.mem.writeW _ ((u₄.gpr .eax).setWidth 8) = _
  rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, doubled_byte_bit]

theorem bits_byte_write_self (m : Mem) (a : Addr) (v : Byte) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem bits_byte_write_ne (m : Mem) {x : BitVec 32} (v : Byte) {d e : Nat}
    (hd : x.toNat + d + 1 ≤ 2 ^ 32) (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) :
    (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])
end VG.Proof.Ed25519.X86
end

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
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem inputByte_contains {s₀ : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    {k : Nat} (hk : k < 4 * n) : (sub (arg s₀ i) 0 (4 * n)).Contains (addr (arg s₀ i) k) 1 :=
  sub_contains (by have := hp.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)

theorem inputBytes_same {s₀ s : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) :
    Spec.Ed25519.bytesAt s.mem ((arg s₀ i).setWidth 64) (4 * n) =
      Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n) := by
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← addr_eq (by have := hp.fit; omega_using [this, hk'])]
  apply hs.frame
  intro r hr; rw [List.mem_singleton.mp hr]
  exact hp.sep _ (inputByte_contains hp hk')

theorem inputBits_ok {s₀ s : State} {scidx argc i n : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : n ≤ 16) :
    WP isa (.block (inputBits i (4 * n))) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < 32 * n, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n)) / 2 ^ k % 2)) := by
  refine WP.block_append (WP.mono (loadArg_ok hp hs hia) fun u ⟨hu, eu, _⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < 4 * n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i) k) 1 := by
    intro k hk; refine ⟨_, ?_, inputByte_contains hi hk⟩
    rw [hu.rd, hu.wr]; exact hi.rd
  have hsep : ∀ k < 4 * n, (sub (arg s₀ i) k 1).Disjoint (sub (arg s₀ scidx) 7168 (8 * (4 * n))) := by
    intro k hk
    refine (hi.sep.sub_left ?_).sub_right ?_
    · rw [sub, sub, addr_eq (by have := hi.fit; omega_using [this, hk]), addr_zero]
      exact Offset.sub_base _ (by omega_using [hk])
    · rw [scR_eq]; exact sub_sub hp.fit (by decide) (by omega_using [hn]) (by decide)
  refine WP.mono (expandScalarBits_ok cu eu (by omega_using [hn]) hi.fit hr hsep)
    fun t ⟨kt, ft, bt⟩ => ?_
  refine ⟨hu.of_offset hp.fit (Keep.scalar kt) ft (by decide) (by omega_using [hn]) (by decide), fun k hk => ?_⟩
  rw [bt k (by omega_using [hk]), inputBytes_same hi hu]

end VG.Proof.Ed25519.X86
