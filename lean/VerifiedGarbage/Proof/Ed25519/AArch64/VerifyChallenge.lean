import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyInputs
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarBatch
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

/-!
# `[k]A` for a challenge below `2^256`

Untrusted. When the challenge's upper 32 bytes are zero, its lower 32 bytes
are the whole challenge, so sixteen batches of bits give the specification's
`pointMul` of the 64-byte challenge: the powers above bit 255 are never
added, and the specification does not compute them either.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

open VG.Spec.Ed25519 (bytesAt decodeLE)

theorem challenge_split (m : Mem) (k : Addr) :
    decodeLE (bytesAt m k 64) =
      decodeLE (bytesAt m k 32) + 2 ^ 256 * decodeLE (bytesAt m (off k 32) 32) := by
  have hlen : (bytesAt m k 32).length = 32 := Proof.X25519.length_bytesAt m k 32
  rw [signatureBytes_split, decodeLE_append, hlen, show (256 : Nat) ^ 32 = 2 ^ 256 by decide]

theorem challenge_lt_iff (m : Mem) (k : Addr) :
    decodeLE (bytesAt m k 64) < 2 ^ 256 ↔ decodeLE (bytesAt m (off k 32) 32) = 0 := by
  have hl := decodeLE_lt (bytesAt m k 32)
  have hlen : (bytesAt m k 32).length = 32 := Proof.X25519.length_bytesAt m k 32
  rw [hlen, show (256 : Nat) ^ 32 = 2 ^ 256 by decide] at hl
  rw [challenge_split]
  generalize decodeLE (bytesAt m k 32) = a at hl
  generalize decodeLE (bytesAt m (off k 32) 32) = b
  constructor
  · intro h
    by_contra hb
    have : 2 ^ 256 ≤ 2 ^ 256 * b := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb)
    omega
  · intro h
    rw [h, Nat.mul_zero, Nat.add_zero]
    exact hl

theorem challenge_low {m : Mem} {k : Addr} (h : decodeLE (bytesAt m k 64) < 2 ^ 256) :
    decodeLE (bytesAt m k 64) = decodeLE (bytesAt m k 32) := by
  rw [challenge_split, (challenge_lt_iff m k).mp h, Nat.mul_zero, Nat.add_zero]

theorem or4_zero (a b c d : Word) :
    ((a ||| b ||| (c ||| d)) == 0) = decide (val4 a b c d = 0) := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_or,
    BitVec.toNat_or, BitVec.toNat_or, show (0 : Word).toNat = 0 from rfl, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff,
    Nat.or_eq_zero_iff, val4]
  omega

theorem challengeHighAdd_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x1 32]) s fun t =>
      t.gpr .x2 = off (s.gpr .x1) 32 ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (32 : Nat) < 4096 from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem challengeHighOr_ok (s : State) :
    WP isa (.block [.logic .orr .x .x8 .x4 .x5, .logic .orr .x .x9 .x6 .x7,
      .logic .orr .x .x8 .x8 .x9]) s fun t =>
      t.gpr .x8 = (s.gpr .x4 ||| s.gpr .x5 ||| (s.gpr .x6 ||| s.gpr .x7)) ∧ Keeps [.x8, .x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, reduceCtorEq, ite_false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [RegUpd.gpr_write, hk.1, hk.2, ite_false]

theorem challengeHigh_ok {s : State} {k : Addr} (hp : s.gpr .x1 = k)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off k 32) d) 8) :
    WP isa (.block challengeHigh) s fun t =>
      eval (.zero .x .x8) t = some (decide (decodeLE (bytesAt s.mem k 64) < 2 ^ 256)) ∧
      Keeps [.x2, .x4, .x5, .x6, .x7, .x8, .x9] s t := by
  rw [challengeHigh, List.append_assoc, WP.block_append_iff]
  refine WP.mono (challengeHighAdd_ok s) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok a (off k 32) ap (by
    intro d hd; rw [ka.rd, ka.wr]; exact hr d hd)) fun b ⟨bv, kb⟩ => ?_
  refine WP.mono (challengeHighOr_ok b) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  change some (t.gpr .x8 == 0) = _
  rw [tv, or4_zero]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [challenge_lt_iff, ← ka.mem, ← bv]
  exact Iff.rfl

theorem challengeMul_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hw : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off k 32) d) 8)
    (hr : ∀ q < 64, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 64, 8192 ≤ ofs base (off k q)) :
    WP isa challengeMul s fun t => PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem k 64)) (point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = Spec.Ed25519.d := by
  rw [challengeMul]
  refine WP.seq (WP.mono (challengeHigh_ok hp hw) fun a ⟨az, ka⟩ => ?_)
  have kap : PowersKeep base 56 7368 s a := PowersKeep.of_keeps ka (by decide)
  have as := kap.scratch hs
  have ap : a.gpr .x1 = k := (ka.gpr _ (by decide)).trans hp
  have ar : ∀ q < 64, InRegions (a.rd ++ a.wr) (off k q) 1 := by
    intro q hq; rw [ka.rd, ka.wr]; exact hr q hq
  refine WP.ite _ az (fun h => ?_) (fun _ => ?_)
  · have hlt := of_decide_eq_true h
    refine WP.mono (pointFromScalarVar_ok as ap 16 (by decide) (by decide)
      (fun q hq => ar q (by omega)) (fun q hq => hd q (by omega))) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨kap.trans kt, ?_, td⟩
    rw [tp, ka.mem, challenge_low hlt]
  · refine WP.mono (pointFromScalarVar_ok as ap 32 (by decide) (by decide) ar hd)
      fun t ⟨kt, tp, td⟩ => ?_
    exact ⟨kap.trans kt, by rw [tp, ka.mem], td⟩

end VG.Proof.Ed25519.AArch64
