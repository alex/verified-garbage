import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.Window

/-! Merged from `Proof.Ed25519.AArch64.WindowByte`. -/
section
/-!
# Verification's bytes: two windows per byte of the scalars

Byte `i` of `k` (and of `S`) gives two digits, high nibble first; after it,
the accumulator represents `[k / 256^i]A - [S / 256^i]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- What a byte of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 56 712 s.mem t.mem

theorem ByteKeep.refl (base : Addr) (s : State) : ByteKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.of_counter {base : Addr} {s t : State}
    (ag : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r) (ar : t.rd = s.rd) (aw : t.wr = s.wr) (asp : t.sp = s.sp)
    (am : Outside base 56 8 s.mem t.mem) : ByteKeep base s t :=
  ⟨fun r _ hb _ => ag r hb, ar, aw, asp, am.mono (by decide) (by decide)⟩

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

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
  refine WP.mono (digitHigh_ok ht.scratch 7952 0 (by decide) (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv
  exact ⟨uv, ku⟩

theorem digitKLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7952 0) ((s.mem (off kp i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7952 0 (by decide) (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv
  exact ⟨uv, ku⟩

theorem digitSHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7944 32) ((s.mem (off (off sp 32) i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7944 32 (by decide) (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [h.byteS kt hi] at uv
  exact ⟨uv, ku⟩

theorem digitSLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7944 32) ((s.mem (off (off sp 32) i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7944 32 (by decide) (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [h.byteS kt hi] at uv
  exact ⟨uv, ku⟩

/-! ## A byte -/

private theorem above_cmp : ∀ i < 65,
    (BitVec.ofNat 64 i - BitVec.ofNat 64 32 != 0) = decide (i ≠ 32) := by decide

theorem aboveLow_ok {s : State} {base : Addr} (hs : Scr s base) (i : Nat) (hi : i ≤ 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block aboveLow) s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 32)) ∧
      Keeps [.x19] s t := by
  rw [aboveLow, show ([ld .x19 56, .subImm .x .x19 .x19 32] : List Instr) =
    [ld .x19 56] ++ [.subImm .x .x19 .x19 32] from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x19 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (32 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write, ka.mem],
    by simp only [RegUpd.rd_write, ka.rd], by simp only [RegUpd.wr_write, ka.wr],
    by simp only [RegUpd.sp_write, ka.sp]⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, av, hc, above_cmp i (by omega)]
  · have h : r ≠ .x19 := by simpa only [List.mem_singleton] using hr
    rw [RegUpd.gpr_write_of_ne _ _ _ h, ka.gpr r hr]

theorem scalar_byte {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) :
    (m (off p i)).toNat = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ i % 256 := by
  rw [decodeLE_byte, input_byte m p n i hi]

theorem byteStepA_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi32 : 32 ≤ i) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) {S : Nat} (hS : S < 256 ^ 32)
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (S / 256 ^ (i + 1)) • (-baseAff))) :
    WP isa byteStepA s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 32)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (S / 256 ^ i) • (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  have hb : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) hi, ka.bytesK h]
  refine WP.seq (WP.mono (windowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha)
    (Nat.div_lt_of_lt_mul (by have := (a.mem (off kp i)).isLt; omega)) (digitKHigh ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowA_ok hb' bd br (Nat.mod_lt _ (by decide))
    (digitKLow hb' hi (kb.counter.trans av))) fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (aboveLow_ok hc'.scratch i (by omega) (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb hi] at cr
    rw [kt.mem]
    convert cr using 1
    rw [byte_split K i _ hb, high_zero hS hi32, high_zero hS (by omega : 32 ≤ i + 1)]
    module

theorem byteStepAB_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ (i + 1)) •
          (-baseAff))) :
    WP isa byteStepAB s fun t => t.gpr .x19 = BitVec.ofNat 64 i ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ i) •
            (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
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
  refine WP.mono (batchTest_ok hc'.scratch i (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb (by omega), ha'.byteS kb hi] at cr
    rw [kt.mem, ← window_step A (-baseAff) K S i _ _ hbK hbS]
    exact cr

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's loops over the bytes of the scalars

The leading zero bytes of `k` above its low 32 are skipped, as the sum before
them is zero; bytes 63 down to 32 hold digits of `k` alone, bytes 31 down to 0
of both scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- The loops' invariant, with `c` bytes left. -/
structure WinLoop (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : RepP (point (env s.mem base) 0 1 2 3) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

theorem WinLoop.of_keeps {s₀ s t : State} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    {rs : List Reg} (h : WinLoop s₀ base kp sp A K S c s) (k : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : WinLoop s₀ base kp sp A K S c t := by
  have kb : ByteKeep base s t := ByteKeep.of_keeps k hrs
  exact ⟨h.ctx.of_byte kb, by rw [k.mem]; exact h.d, by rw [k.mem]; exact h.counter,
    by rw [k.mem]; exact h.kVal, by rw [k.mem]; exact h.sVal, by rw [k.mem]; exact h.value,
    h.keep.trans kb⟩

/-- A byte of `k` alone, from `32 + j + 1` bytes left to `32 + j`. -/
theorem stepA_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (32 + (j + 1)) t) :
    WP isa byteStepA t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base kp sp A K S (32 + j) u := by
  have hS : S < 256 ^ 32 := ht.sVal ▸ decodeLE_lt32 _ _
  refine WP.mono (byteStepA_ok (i := 32 + j) ht.ctx ht.d (by omega) (by omega)
    (by rw [ht.counter]; rfl) hS (by rw [ht.kVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal] at uv; exact uv, ht.keep.trans uk⟩

/-- A byte of both scalars, from `j + 1` bytes left to `j`. -/
theorem stepB_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (j + 1) t) :
    WP isa byteStepAB t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base kp sp A K S j u := by
  refine WP.mono (byteStepAB_ok (i := j) ht.ctx ht.d hj ht.counter
    (by rw [ht.kVal, ht.sVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by simp only [eval, read_x, uz, counter_nonzero (by omega : j < 2 ^ 64)], ht.ctx.of_byte uk, ud, uc,
    by rw [uk.bytesK ht.ctx, ht.kVal], by rw [uk.bytesS ht.ctx, ht.sVal],
    by rw [ht.kVal, ht.sVal] at uv; exact uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) (h : WinLoop s₀ base kp sp A K S (32 + n) s) :
    WP isa (.loop byteStepA (.nonzero .x .x19)) s (WinLoop s₀ base kp sp A K S 32) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S (32 + n) t ∧ 0 < n ∧ n ≤ 32)
    (n := n)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, hn0, hn⟩

theorem windowsA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) (h : WinLoop s₀ base kp sp A K S c s) :
    WP isa windowsA s (WinLoop s₀ base kp sp A K S 32) := by
  rw [windowsA]
  refine WP.seq (WP.mono (aboveLow_ok h.ctx.scratch c (by omega) h.counter) fun a ⟨az, ka⟩ => ?_)
  have ha := h.of_keeps ka (by decide)
  refine WP.ite (decide (c ≠ 32)) az (fun hy => ?_) (fun hn => ?_)
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    exact loopA_ok n (by have := of_decide_eq_true hy; omega) (by omega) ha
  · have : c = 32 := by simpa using hn
    subst this
    exact WP.block_nil ha

theorem loopB_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 32 s) :
    WP isa (.loop byteStepAB (.nonzero .x .x19)) s (WinLoop s₀ base kp sp A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S n t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem subOne_ok (s : State) (r : Reg) (n : Nat) (hc : s.gpr r = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x r r 1]) s fun t => t.gpr r = BitVec.ofNat 64 n ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem byte_ext : ∀ b : BitVec 8, (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  decide

theorem skipLoad_ok {s : State} {base kp : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7952) 64 = kp) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1))
    (hr : InRegions (s.rd ++ s.wr) (off kp j) 1) :
    WP isa (.block skipLoad) s fun t => t.gpr .x8 = BitVec.ofNat 64 j ∧
      t.gpr .x19 = BitVec.ofNat 64 (s.mem (off kp j)).toNat ∧ Keeps [.x2, .x8, .x19] s t := by
  rw [skipLoad, show ([ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952, .add .x .x2 .x2 .x8,
      .ldrb .x19 .x2 0] : List Instr) = [ld .x8 56] ++ ([.subImm .x .x8 .x8 1] ++
      ([ld .x2 7952] ++ [.add .x .x2 .x2 .x8, .ldrb .x19 .x2 0])) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun b ⟨bv, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .x2 7952
    (by decide) (by decide)) fun c ⟨cp, kc⟩ => ?_
  have hm : c.mem = s.mem := kc.mem.trans (kb.mem.trans ka.mem)
  have hrd : c.rd ++ c.wr = s.rd ++ s.wr := by rw [kc.rd, kc.wr, kb.rd, kb.wr, ka.rd, ka.wr]
  have c2 : c.gpr .x2 = kp := by rw [cp, kb.mem, ka.mem, hp]
  have c8 : c.gpr .x8 = BitVec.ofNat 64 j := by rw [kc.gpr _ (by decide), bv]
  have hea : kp + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off kp j := BitVec.add_zero _
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    c2, c8, hea, hrd, hm, hr, read_byte, byte_ext,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, hm, by simp only [RegUpd.rd_write, kc.rd, kb.rd, ka.rd],
    by simp only [RegUpd.wr_write, kc.wr, kb.wr, ka.wr],
    by simp only [RegUpd.sp_write, kc.sp, kb.sp, ka.sp]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]
  rw [kc.gpr r (by simp [hr.1]), kb.gpr r (by simp [hr.2.1]), ka.gpr r (by simp [hr.2.1])]

theorem skipStore_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 (32 + n)) :
    WP isa (.block [st .x8 56, .subImm .x .x19 .x8 32]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (32 + n) ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have he : BitVec.ofNat 64 (32 + n) - BitVec.ofNat 64 32 = BitVec.ofNat 64 n := by
    rw [Nat.add_comm, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc hs (by decide) (by decide), runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (32 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, h8, he]
  refine ⟨trivial, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, ?_⟩
  · rw [RegUpd.mem_write, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write]; exact writeW_outside _ _ _ (by decide)

private theorem byte_nonzero : ∀ b : BitVec 8,
    (BitVec.ofNat 64 b.toNat != 0) = decide (b.toNat ≠ 0) := by decide

theorem movzZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => eval (.nonzero .x .x19) t = some false ∧
      Keeps [.x19] s t :=
  WP.mono (movzW_ok s .x19 0) fun t ⟨tv, kt⟩ => ⟨by simp only [eval, read_x, tv]; rfl, kt⟩

/-- Skipping: `c = 32 + n` bytes are left, and the bytes of `k` from `c` on are zero. -/
def SkipInv (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  WinLoop s₀ base kp sp A K S (32 + n) s ∧ K / 256 ^ (32 + n) = 0 ∧ 0 < n ∧ n ≤ 32

/-- Whether the skipping goes on below `32 + j + 1` bytes left: byte `32 + j` of `k` is zero,
and more than 32 bytes are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 256 ^ (32 + j) % 256 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `32 + j + 1` bytes left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 256 ^ (32 + j) % 256 = 0 then 32 else 32 + (j + 1)

theorem skipBody_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base kp sp A K S (j + 1) t) :
    WP isa skipBody t fun u => eval (.nonzero .x .x19) u = some (skipOn K j) ∧
      (skipOn K j = false → WinLoop s₀ base kp sp A K S (skipEnd K j) u) ∧
      (skipOn K j = true → SkipInv s₀ base kp sp A K S j u) := by
  obtain ⟨hl, hz, _, hn⟩ := h
  have hS : S < 256 ^ 32 := hl.sVal ▸ decodeLE_lt32 _ _
  rw [skipBody]
  refine WP.seq (WP.mono (skipLoad_ok hl.ctx.scratch hl.ctx.kHeader (32 + j)
    (by rw [hl.counter]; rfl) (hl.ctx.kRead _ (by omega))) fun a ⟨a8, av, ka⟩ => ?_)
  have ha := hl.of_keeps ka (by decide)
  have hb : (t.mem (off kp (32 + j))).toNat = K / 256 ^ (32 + j) % 256 := by
    rw [scalar_byte (n := 64) (by omega), hl.kVal]
  refine WP.ite (decide ((t.mem (off kp (32 + j))).toNat ≠ 0))
    (by simp only [eval, read_x, av, byte_nonzero]) (fun hy => ?_) (fun hy => ?_)
  · have h0 : K / 256 ^ (32 + j) % 256 ≠ 0 := by rw [← hb]; simpa using hy
    have hoff : skipOn K j = false := by simp only [skipOn, h0, false_and, decide_false]
    refine WP.mono (movzZero_ok a) fun u ⟨uz, ku⟩ => ⟨by rw [uz, hoff], fun _ => ?_,
      fun ht => absurd ht (by rw [hoff]; decide)⟩
    have e : skipEnd K j = 32 + (j + 1) := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact ha.of_keeps ku (by decide)
  · have h0 : K / 256 ^ (32 + j) % 256 = 0 := by rw [← hb]; simpa using hy
    refine WP.mono (skipStore_ok ha.ctx.scratch j a8) fun u ⟨uv, uc, ug, ur, uw, usp, um⟩ => ?_
    have ku : ByteKeep base a u := ByteKeep.of_counter ug ur uw usp um
    have hK : K / 256 ^ (32 + j) = 0 := by
      have := div_split K (32 + j)
      rw [show 32 + j + 1 = 32 + (j + 1) by omega, hz] at this
      omega
    have hw : WinLoop s₀ base kp sp A K S (32 + j) u := by
      refine ⟨ha.ctx.of_byte ku, by rw [header_env um]; exact ha.d, uc,
        by rw [ku.bytesK ha.ctx, ha.kVal], by rw [ku.bytesS ha.ctx, ha.sVal], ?_, ha.keep.trans ku⟩
      have v := ha.value
      rw [hz, high_zero hS (by omega)] at v
      rw [header_env um, hK, high_zero hS (by omega)]
      exact v
    have he : skipOn K j = decide (j ≠ 0) := by simp only [skipOn, h0, true_and]
    have hj32 : j < 32 := by omega
    refine ⟨by simp only [eval, read_x, uv]; rw [counter_nonzero (by omega : j < 2 ^ 64), he], fun hf => ?_,
      fun ht => ⟨hw, hK, by rw [he] at ht; have := of_decide_eq_true ht; omega, by omega⟩⟩
    have hj : j = 0 := by rw [he] at hf; simpa using hf
    subst hj
    have e : skipEnd K 0 = 32 := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact hw

theorem skipEnd_range (K j : Nat) (hj : j < 32) : 32 ≤ skipEnd K j ∧ skipEnd K j ≤ 64 := by
  unfold skipEnd; split <;> omega

theorem skipZero_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 64 s) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ WinLoop s₀ base kp sp A K S c t := by
  have hK : K / 256 ^ 64 = 0 := Nat.div_eq_of_lt (h.kVal ▸ decodeLE_lt64 _ _)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base kp sp A K S) (n := 32)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega : n ≠ 0)
    have hj : j < 32 := by have := ht.2.2.2; omega
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨uz.trans (by rw [hs]), skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2,
        uf hs⟩
    · exact Or.inr ⟨uz.trans (by rw [hs]), j, by omega, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩

end VG.Proof.Ed25519.AArch64
