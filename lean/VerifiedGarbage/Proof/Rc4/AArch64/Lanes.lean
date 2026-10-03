import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
import VerifiedGarbage.Proof.Rc4.Iterate

/-!
# A group of sixteen bytes

In a group whose base is `B`, lane `n` is skipped while `x5` counts lanes to
skip (the first group starts at lane `sk = (i + 1) mod 16`), does nothing
once the data has ended, and otherwise produces the next byte of the stream
(`lane_ok`). `p` bytes of the `N` at `D` are done after lane `n`:
`p = min N (p₀ + (n - sk))` (`LaneInv`).
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The stream's fixed parameters: the context it starts from, the data and
its original bytes, and the state the loop starts in. -/
structure Glob where
  c₀ : Context
  D : Addr
  N : Nat
  M₀ : Mem
  s₀ : State

/-- `p` bytes of the data done. -/
structure DataAt (g : Glob) (p : Nat) (s : State) : Prop where
  le : p ≤ g.N
  x1 : s.gpr .x1 = g.D + BitVec.ofNat 64 p
  x2 : s.gpr .x2 = BitVec.ofNat 64 (g.N - p)
  bytes : ∀ k < g.N, s.mem (g.D + BitVec.ofNat 64 k) =
    if k < p then g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k else g.M₀ (g.D + BitVec.ofNat 64 k)
  frame : Frame [⟨g.D, g.N⟩] g.M₀ s.mem

/-- What the loop keeps: the registers it does not use, the regions and the
stack pointer. -/
structure Kept (g : Glob) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s.gpr r = g.s₀.gpr r
  rd : s.rd = g.s₀.rd
  wr : s.wr = g.s₀.wr
  sp : s.sp = g.s₀.sp

/-- The bytes done after lane `n` of the group with base `B` that starts
after `p₀` bytes, skipping its first `sk` lanes. -/
def doneAt (g : Glob) (p₀ sk n : Nat) : Nat := min g.N (p₀ + (n - sk))

structure LaneInv (g : Glob) (B p₀ sk n : Nat) (s : State) : Prop where
  prga : PrgaRegs s B (stepN g.c₀ (doneAt g p₀ sk n))
  data : DataAt g (doneAt g p₀ sk n) s
  x5 : s.gpr .x5 = BitVec.ofNat 64 (sk - n)
  x8 : s.gpr .x8 = BitVec.ofNat 64 B
  next : doneAt g p₀ sk n < g.N →
    (stepN g.c₀ (doneAt g p₀ sk n)).i + 1 = BitVec.ofNat 8 (B + max n sk) ∧
      s.v si = bc (tbyte s.v (max n sk))
  kept : Kept g s
  vkept : ∀ r, r ∉ stepRegs → r ≠ negBase → s.v r = g.s₀.v r

theorem eval_nonzero' (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 m ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this; simp at this; omega
    change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]

theorem eval_zero' (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 m ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this; simp at this; omega
    change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]

theorem write_byte_apply (m : Mem) (p x : Addr) (v : BitVec 8) :
    m.write p 1 v x = if x = p then v else m x := VG.Proof.Rc4.write_byte m p x v

/-- The data region is writable, and fits in the address space. -/
structure DataOk (g : Glob) : Prop where
  wr : (⟨g.D, g.N⟩ : Region) ∈ g.s₀.wr
  fit : g.N < 2 ^ 64

theorem DataOk.byte {g : Glob} (h : DataOk g) {s : State} (hk : Kept g s) {p : Nat} (hp : p < g.N) :
    InRegions s.wr (g.D + BitVec.ofNat 64 p) 1 :=
  ⟨_, hk.wr ▸ h.wr, Offset.contains_base _ (by omega) (by have := h.fit; omega)⟩

theorem lane_ok (g : Glob) (hg : DataOk g) {B p₀ sk n : Nat} (hsk : sk ≤ 15) (hn : n < 16) {s : State}
    (h : LaneInv g B p₀ sk n s) : WP isa (lane n) s (LaneInv g B p₀ sk (n + 1)) := by
  have hfit := hg.fit
  unfold lane
  apply WP.ite _ (eval_nonzero' s .x5 h.x5 (by omega))
  · intro hz
    have hlt : n < sk := by simp at hz; omega
    let t := s.write .x .x5 (s.read .x .x5 - BitVec.ofNat _ 1)
    refine WP.of_runBlock ⟨t, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have hd : doneAt g p₀ sk (n + 1) = doneAt g p₀ sk n := by simp only [doneAt]; omega
    have hm : max (n + 1) sk = max n sk := by omega
    have g5 : ∀ r, r ≠ .x5 → t.gpr r = s.gpr r := fun r hr => by simp [t, State.write, hr]
    have x5 : t.gpr .x5 = BitVec.ofNat 64 (sk - (n + 1)) := by
      simp only [t, State.write, State.read, BitVec.setWidth_eq, ite_true, h.x5]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1
    exact {
      prga := by
        rw [hd]
        exact ⟨h.prga.table, h.prga.j, h.prga.nb,
          ⟨h.prga.consts.lns, h.prga.consts.c64, h.prga.consts.c128⟩⟩
      data := by
        rw [hd]
        exact ⟨h.data.le, by rw [g5 _ (by decide), h.data.x1], by rw [g5 _ (by decide), h.data.x2],
          h.data.bytes, h.data.frame⟩
      x5 := x5
      x8 := by rw [g5 _ (by decide), h.x8]
      next := by rw [hd, hm]; exact h.next
      kept := ⟨fun r a b c d e f => by rw [g5 r c, h.kept.gpr r a b c d e f], h.kept.rd, h.kept.wr,
        h.kept.sp⟩
      vkept := h.vkept }
  · intro hnz
    have hge : sk ≤ n := by simp at hnz; omega
    let p := doneAt g p₀ sk n
    have hp := h.data.le
    apply WP.ite _ (eval_zero' s .x2 h.data.x2 (by omega))
    · intro hz
      have hpN : p = g.N := by simp at hz; omega
      apply WP.block_nil
      have hd : doneAt g p₀ sk (n + 1) = p := by simp only [doneAt, p] at hpN ⊢; omega
      exact {
        prga := by rw [hd]; exact h.prga
        data := by rw [hd]; exact h.data
        x5 := by rw [h.x5]; congr 1; omega
        x8 := h.x8
        next := fun hlt => absurd hlt (by omega)
        kept := h.kept
        vkept := h.vkept }
    · intro hnz2
      have hpN : p < g.N := by simp at hnz2; omega
      obtain ⟨hi, hsi⟩ := h.next hpN
      rw [show max n sk = n by omega] at hi hsi
      have hd : InRegions s.wr (s.gpr .x1) 1 := by rw [h.data.x1]; exact hg.byte h.kept hpN
      refine WP.mono (byte_ok hn h.prga hi hsi hd) fun t ⟨pr, tsi, m, x1, x2, gg, vv, rd, wr, sp⟩ => ?_
      have hd1 : doneAt g p₀ sk (n + 1) = p + 1 := by simp only [doneAt, p] at hpN ⊢; omega
      have bytes : ∀ k < g.N, t.mem (g.D + BitVec.ofNat 64 k) =
          if k < p + 1 then g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k
          else g.M₀ (g.D + BitVec.ofNat 64 k) := by
        intro k hk
        rw [m, h.data.x1, write_byte_apply]
        have hne : (g.D + BitVec.ofNat 64 k = g.D + BitVec.ofNat 64 p) ↔ k = p := by
          constructor
          · intro e; have := congrArg (fun x => (x - g.D).toNat) e
            simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at this
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
          · intro e; rw [e]
        by_cases hkp : k = p
        · subst hkp
          rw [ite_eq_left rfl, h.data.bytes _ hk, ite_eq_right (by omega), ite_eq_left (by omega)]
          rfl
        · rw [ite_eq_right (fun e => hkp (hne.mp e)), h.data.bytes k hk]
          exact ite_iff ⟨fun h' => by omega, fun h' => by omega⟩ _ _
      have nexti : (stepN g.c₀ (p + 1)).i + 1 = BitVec.ofNat 8 (B + max (n + 1) sk) := by
        rw [show stepN g.c₀ (p + 1) = (step (stepN g.c₀ p)).1 from rfl, show max (n + 1) sk = n + 1 by omega]
        simp only [step]
        rw [hi]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 8).toNat = 1 from rfl]
        omega
      exact {
        prga := by rw [hd1]; exact pr
        data := by
          rw [hd1]
          refine ⟨by omega, ?_, ?_, bytes, ?_⟩
          · rw [x1, h.data.x1, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_add_ofNat]
          · rw [x2, h.data.x2, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
            congr 1
          · rw [m, h.data.x1]
            exact h.data.frame.write List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
        x5 := by
          rw [gg _ (by decide) (by decide) (by decide) (by decide), h.x5]; congr 1; omega
        x8 := by rw [gg _ (by decide) (by decide) (by decide) (by decide), h.x8]
        next := by
          rw [hd1]
          exact fun _ => ⟨nexti, by rw [tsi, show max (n + 1) sk = n + 1 by omega]⟩
        kept := ⟨fun r a b c d e f => by rw [gg r a b d e, h.kept.gpr r a b c d e f],
          rd.trans h.kept.rd, wr.trans h.kept.wr, sp.trans h.kept.sp⟩
        vkept := fun r hr hn => by rw [vv r hr, h.vkept r hr hn] }

end VG.Proof.Rc4.AArch64
