import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Bytes
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Bits

/-!
# Deterministic ECDSA on x86-64: `h = bits2octets(digest)`

The digest, big-endian in four words, less `n` if that does not borrow
(`reduce_math`: it is below `2^256 < 2n`, so this is the digest modulo `n`),
stored big-endian in the frame (`reduce_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.X25519.X86_64 (sub_borrow sbb_borrow)

theorem sel_mask (x d : BitVec 64) (y : BitVec 64) (c : Bool) :
    ((x ^^^ d) &&& (y - y - (BitVec.ofBool c).setWidth 64)) ^^^ d = if c then x else d := by
  cases c
  · simp
  · have : y - y - (BitVec.ofBool true).setWidth 64 = BitVec.allOnes 64 := by simp
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp

theorem mod_math (X N D : Nat) (c : Bool) (hsum : D + N = X + 2 ^ 256 * c.toNat) (hD : D < 2 ^ 256)
    (hX : X < 2 ^ 256) (hN : 2 ^ 255 ≤ N) : (if c then X else D) = X % N := by
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hsum
    simp only [Bool.false_eq_true, ite_false]
    have hge : N ≤ X := by omega
    have hlt : X - N < N := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    omega
  · simp only [Bool.toNat_true, Nat.mul_one] at hsum
    simp only [ite_true]
    have hlt : X < N := by omega
    rw [Nat.mod_eq_of_lt hlt]

theorem reduce_math (x0 x1 x2 x3 n0 n1 n2 n3 : BitVec 64) {c1 c2 c3 c4 : Bool}
    (h1 : c1 = decide (x0.toNat < n0.toNat)) (h2 : c2 = decide (x1.toNat < n1.toNat + c1.toNat))
    (h3 : c3 = decide (x2.toNat < n2.toNat + c2.toNat)) (h4 : c4 = decide (x3.toNat < n3.toNat + c3.toNat))
    {N : Nat} (hN : n3.toNat * 2 ^ 192 + n2.toNat * 2 ^ 128 + n1.toNat * 2 ^ 64 + n0.toNat = N)
    (hN' : 2 ^ 255 ≤ N) :
    (((x3 ^^^ (x3 - n3 - (BitVec.ofBool c3).setWidth 64)) &&& (n3 - n3 - (BitVec.ofBool c4).setWidth 64)) ^^^
          (x3 - n3 - (BitVec.ofBool c3).setWidth 64)).toNat * 2 ^ 192 +
        (((x2 ^^^ (x2 - n2 - (BitVec.ofBool c2).setWidth 64)) &&& (n3 - n3 - (BitVec.ofBool c4).setWidth 64)) ^^^
          (x2 - n2 - (BitVec.ofBool c2).setWidth 64)).toNat * 2 ^ 128 +
        (((x1 ^^^ (x1 - n1 - (BitVec.ofBool c1).setWidth 64)) &&& (n3 - n3 - (BitVec.ofBool c4).setWidth 64)) ^^^
          (x1 - n1 - (BitVec.ofBool c1).setWidth 64)).toNat * 2 ^ 64 +
        (((x0 ^^^ (x0 - n0)) &&& (n3 - n3 - (BitVec.ofBool c4).setWidth 64)) ^^^ (x0 - n0)).toNat =
      (x3.toNat * 2 ^ 192 + x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) % N := by
  simp only [sel_mask]
  have e0 := sub_borrow x0 n0
  have e1 := sbb_borrow x1 n1 c1
  have e2 := sbb_borrow x2 n2 c2
  have e3 := sbb_borrow x3 n3 c3
  rw [← h1] at e0; rw [← h2] at e1; rw [← h3] at e2; rw [← h4] at e3
  clear h1 h2 h3 h4
  generalize x0 - n0 = D0 at *
  generalize x1 - n1 - (BitVec.ofBool c1).setWidth 64 = D1 at *
  generalize x2 - n2 - (BitVec.ofBool c2).setWidth 64 = D2 at *
  generalize x3 - n3 - (BitVec.ofBool c3).setWidth 64 = D3 at *
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have := D0.isLt; have := D1.isLt; have := D2.isLt; have := D3.isLt
  have := n0.isLt; have := n1.isLt; have := n2.isLt; have := n3.isLt
  have b1 := Bool.toNat_le c1; have b2 := Bool.toNat_le c2; have b3 := Bool.toNat_le c3
  have hX : x3.toNat * 2 ^ 192 + x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat < 2 ^ 256 := by omega
  have hsum : (D3.toNat * 2 ^ 192 + D2.toNat * 2 ^ 128 + D1.toNat * 2 ^ 64 + D0.toNat) + N =
      (x3.toNat * 2 ^ 192 + x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) + 2 ^ 256 * c4.toNat := by
    rw [← hN]
    omega_using [e0, e1, e2, e3]
  have hD : D3.toNat * 2 ^ 192 + D2.toNat * 2 ^ 128 + D1.toNat * 2 ^ 64 + D0.toNat < 2 ^ 256 := by
    omega_using [D0.isLt, D1.isLt, D2.isLt, D3.isLt]
  have key := mod_math _ _ _ c4 hsum hD hX hN'
  cases c4 <;> simpa using key

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

theorem bswap64_bswap64 (a : BitVec 64) : bswap64 (bswap64 a) = a := Proof.Gcm.byteRev64_byteRev64 a

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- Four words stored in the frame's `h`, big-endian. -/
theorem store4 (m : Mem) (B : Addr) (a b c d : BitVec 64) :
    let m' := (((m.writeW (B + BitVec.ofNat 64 88) a).writeW (B + BitVec.ofNat 64 96) b).writeW
      (B + BitVec.ofNat 64 104) c).writeW (B + BitVec.ofNat 64 112) d
    Frame [⟨B + BitVec.ofNat 64 88, 32⟩] m m' ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m' (B + BitVec.ofNat 64 88) 32) =
        (bswap64 a).toNat * 2 ^ 192 + (bswap64 b).toNat * 2 ^ 128 + (bswap64 c).toNat * 2 ^ 64 +
          (bswap64 d).toNat := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 160 → y + 8 ≤ 160 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 88 ≤ x → x + 8 ≤ 120 →
      (⟨B + BitVec.ofNat 64 88, 32⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨(((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 88 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 96 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 104 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 112 (by omega) (by omega))), ?_⟩
  rw [ofBytes_32, Offset.add_add, Offset.add_add, Offset.add_add]
  simp only [Nat.reduceAdd]
  rw [Mem.readW_writeW_sep (sep 88 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 88 104 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 88 96 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 96 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 96 104 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 104 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64, Mem.readW_writeW_self64]

theorem nWords (v : Compress) :
    ((cfgOf v).nWord 3).toNat * 2 ^ 192 + ((cfgOf v).nWord 2).toNat * 2 ^ 128 +
      ((cfgOf v).nWord 1).toNat * 2 ^ 64 + ((cfgOf v).nWord 0).toNat = Spec.P256.n := by
  simp only [Cfg.nWord, cfgOf]
  decide +kernel

theorem n_ge : 2 ^ 255 ≤ Spec.P256.n := by decide +kernel

theorem dg_ofBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 32) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg 32) := by
  congr 1
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => (hc.dg_byte hL (List.mem_range.mp hi)).symm

/-- `digest` in `rsi`. -/
theorem digestPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.digestPtr) t (Upd L g m₀ t .rsi L.dg) := by
  have p := hc.inFr (d := 136) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.digestPtr, fDigest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    hc.rsp, Offset.add_add, Nat.reduceAdd, p, ite_true, Option.map_some, hc.pDg, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .rsi) (by decide) rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl,
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `h`: the digest (at `rsi`) modulo `n`, big-endian in the frame. -/
theorem reduce_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) :
    WP isa (.block (cfgOf v).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 88, 32⟩] t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 88) 32) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 32) % Spec.P256.n := by
  have d0 := hc.inDg (o := 0) (n := 8) (by omega)
  have d8 := hc.inDg (o := 8) (n := 8) (by omega)
  have d16 := hc.inDg (o := 16) (n := 8) (by omega)
  have d24 := hc.inDg (o := 24) (n := 8) (by omega)
  have w0 := hc.inFrW (d := 88) (n := 8) (by omega) (by omega)
  have w1 := hc.inFrW (d := 96) (n := 8) (by omega) (by omega)
  have w2 := hc.inFrW (d := 104) (n := 8) (by omega) (by omega)
  have w3 := hc.inFrW (d := 112) (n := 8) (by omega) (by omega)
  rw [add_ofNat_zero] at d0
  rw [dg_ofBytes hL hc, ofBytes_32, ← nWords v]
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  apply WP.of_runBlock
  simp only [Cfg.reduce, fH, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, State.store64, ea_stk, ea_at,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_ofNat_zero,
    Offset.add_add, Nat.reduceAdd, hsi, d0, d8, d16, d24, w0, w1, w2, w3, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (store4 _ _ _ _ _ _).1, ?_⟩
  rw [(store4 _ _ _ _ _ _).2]
  simp only [bswap64_bswap64]
  exact reduce_math _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl (by rw [nWords]; exact n_ge)

end VG.Proof.Ecdsa.Rfc6979.X86_64
