import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import Mathlib.Tactic.Module

/-!
# Verification's bytes: two windows per byte of the scalars

Untrusted. Byte `i` of `k` (and of `S`) gives two digits, high nibble
first; after it, the accumulator represents `[k / 256^i]A - [S / 256^i]B`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

theorem decodeLE_byte : ∀ (bs : List Byte) (i : Nat),
    Spec.Ed25519.decodeLE bs / 256 ^ i % 256 = (bs.getD i 0).toNat
  | [], i => by simp [Spec.Ed25519.decodeLE]
  | b :: bs, 0 => by
    simp only [Spec.Ed25519.decodeLE, pow_zero, Nat.div_one, List.getD_cons_zero]
    have := b.isLt; omega
  | b :: bs, i + 1 => by
    rw [List.getD_cons_succ, ← decodeLE_byte bs i, Spec.Ed25519.decodeLE, pow_succ,
      Nat.mul_comm (256 ^ i), ← Nat.div_div_eq_div_mul]
    congr 2
    have := b.isLt; omega

theorem div_split (x i : Nat) : x / 256 ^ i = 256 * (x / 256 ^ (i + 1)) + x / 256 ^ i % 256 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega

theorem window_algebra (A N : EPoint dZ) (q qs hA lA hS lS : Nat) :
    (16 : Nat) • ((16 : Nat) • (q • A + qs • N) + hA • A + hS • N) + lA • A + lS • N =
      (256 * q + (16 * hA + lA)) • A + (256 * qs + (16 * hS + lS)) • N := by
  module

/-- What a byte of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 712 s.mem t.mem

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.mem.word (Or.inr (by decide)) (by decide)).trans h.kHeader,
    (k.mem.word (Or.inr (by decide)) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win k.mem (by decide) (by decide), h.bTab.of_win k.mem (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem ByteKeep.bytesK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) : Spec.Ed25519.bytesAt t.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 :=
  outside_bytes k.mem (by decide) h.kFar

theorem ByteKeep.bytesS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) :
    Spec.Ed25519.bytesAt t.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 :=
  outside_bytes k.mem (by decide) h.sFar

/-! ## Digits from the inputs -/

theorem digitKHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7952 0) ((s.mem (off kp i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7952 0 (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitKLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7952 0) ((s.mem (off kp i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7952 0 (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitSHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7944 32) ((s.mem (off (off sp 32) i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7944 32 (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [h.byteS kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitSLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7944 32) ((s.mem (off (off sp 32) i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7944 32 (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [h.byteS kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

/-! ## A byte -/

theorem counterCmp_ok {s : State} {base : Addr} (hs : Scratch s base) (i : Nat) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rbx (.mem (Impl.X25519.X86_64.sc 56)), .alu .cmp .rbx (.imm 32)]) s
      fun t => t.zf = some (decide (i = 32)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hz : (BitVec.ofNat 64 i - (32 : BitVec 32).signExtend 64 == 0) = decide (i = 32) := by
    rw [show (32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 32 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hi]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem byte_split (K i : Nat) (b : Byte) (hb : (b.toNat) = K / 256 ^ i % 256) :
    K / 256 ^ i = 256 * (K / 256 ^ (i + 1)) + (16 * (b.toNat / 16) + b.toNat % 16) := by
  have := div_split K i; omega

theorem scalar_byte {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) :
    (m (off p i)).toNat = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ i % 256 := by
  rw [decodeLE_byte, input_byte m p n i hi]

theorem high_zero {S i : Nat} (hS : S < 256 ^ 32) (hi : 32 ≤ i) : S / 256 ^ i = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) hi))

theorem byteStepA_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi32 : 32 ≤ i) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) {S : Nat} (hS : S < 256 ^ 32)
    (ha : Rep (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (S / 256 ^ (i + 1)) • (-baseAff))) :
    WP isa byteStepA s fun t => t.zf = some (decide (i = 32)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      Rep (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (S / 256 ^ i) • (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_)
  have ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  have hb : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) hi, ka.bytesK h]
  refine WP.seq (WP.mono (windowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.div_lt_of_lt_mul (by have := (a.mem (off kp i)).isLt; omega)) (digitKHigh ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowA_ok hb' bd br (Nat.mod_lt _ (by decide))
    (digitKLow hb' hi (kb.counter.trans av))) fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (counterCmp_ok hc'.scratch i hi (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.2.1]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb hi] at cr
    rw [kt.2.1]
    convert cr using 1
    rw [byte_split K i _ hb, high_zero hS hi32, high_zero hS (by omega : 32 ≤ i + 1)]
    module

theorem byteStepAB_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : Rep (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ (i + 1)) •
          (-baseAff))) :
    WP isa byteStepAB s fun t => t.zf = some (decide (i = 0)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      Rep (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ i) •
            (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_)
  have ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  set S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) with hSdef
  have hbK : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) (by omega), ka.bytesK h]
  have hbS : (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256 := by
    rw [scalar_byte (n := 32) hi, ka.bytesS h]
  have lt16 (b : Byte) : b.toNat / 16 < 16 := Nat.div_lt_of_lt_mul (by have := b.isLt; omega)
  refine WP.seq (WP.mono (windowAB_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (lt16 _) (lt16 _)
    (digitKHigh ha' (by omega) av) (digitSHigh ha' hi av)) fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowAB_ok hb' bd br (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (digitKLow hb' (by omega) (kb.counter.trans av)) (digitSLow hb' hi (kb.counter.trans av)))
    fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (batchTest_ok hc'.scratch i (by omega) (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.2.1]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb (by omega), ha'.byteS kb hi] at cr
    rw [kt.2.1]
    convert cr using 1
    rw [byte_split K i _ hbK, byte_split S i _ hbS]
    module

end VG.Proof.Ed25519.X86_64
