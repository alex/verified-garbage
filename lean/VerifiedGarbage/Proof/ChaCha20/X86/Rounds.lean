import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.X86

/-!
# ChaCha20 block function on x86 (32-bit): the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-- The address of word `k` of `buf`, relative to its 64-bit address `B`. -/
abbrev wordAddr (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

/-- The state `v` is in `buf[0..64)`. -/
def Holds (B : Addr) (v : CState) (m : Mem) : Prop :=
  ∀ k (hk : k < 16), m.readW (wordAddr B k) 32 = v[k]

theorem word_sep (B : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    Mem.Sep (wordAddr B j) 4 (wordAddr B k) 4 := by
  intro x hx hy
  simp only [wordAddr] at hx hy
  bv_omega

theorem readW_writeW_word (m : Mem) (B : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) : (m.writeW (wordAddr B k) v).readW (wordAddr B j) 32 = m.readW (wordAddr B j) 32 :=
  Mem.readW_writeW_sep (word_sep B hj hk h) (by decide)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The working state, `buf[0..64)`. -/
abbrev workR (B : Addr) : Region := ⟨B, 64⟩

theorem word_in_work (B : Addr) {k : Nat} (hk : k < 16) : (workR B).Contains (wordAddr B k) 4 := by
  simp only [Region.Contains, wordAddr]
  rw [show B + BitVec.ofNat 64 (4 * k) - B = BitVec.ofNat 64 (4 * k) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

/-- What the rounds need of the machine state: `esi` points to `buf`, whose
working state is readable and writable. -/
structure Ctx (B : Addr) (s : State) : Prop where
  ea : ∀ k < 16, addr (s.gpr .esi) (4 * k) = wordAddr B k
  inw : ∀ k < 16, InRegions (s.rd ++ s.wr) (wordAddr B k) 4
  outw : ∀ k < 16, InRegions s.wr (wordAddr B k) 4

/-! ## One quarter round -/

theorem qr_ok (s : State) (va vb vc vd : Word)
    (ha : s.gpr .eax = va) (hb : s.gpr .ebx = vb) (hc : s.gpr .ecx = vc) (hd : s.gpr .edx = vd) :
    WP isa (.block qr) s fun s' =>
      s'.gpr .eax = (quarterRound va vb vc vd).1 ∧ s'.gpr .ebx = (quarterRound va vb vc vd).2.1 ∧
      s'.gpr .ecx = (quarterRound va vb vc vd).2.2.1 ∧ s'.gpr .edx = (quarterRound va vb vc vd).2.2.2 ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [qr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    State.setReg, arithFlags, State.setFlags, ha, hb, hc, hd, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  and_intros
  all_goals simp only [quarterRound_eq]

theorem quarter_ok {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {B : Addr} {v : CState} {s : State} (hctx : Ctx B s)
    (h : Holds B v s.mem) :
    WP isa (quarter x y z w) s fun s' =>
      Holds B (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s'.mem ∧ Frame [workR B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.gpr .ebp = s.gpr .ebp := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ex := hctx.ea x hx; have ey := hctx.ea y hy; have ez := hctx.ea z hz; have ew := hctx.ea w hw
  have ix := hctx.inw x hx; have iy := hctx.inw y hy; have iz := hctx.inw z hz; have iw := hctx.inw w hw
  have ox := hctx.outw x hx; have oy := hctx.outw y hy; have oz := hctx.outw z hz
  have ow := hctx.outw w hw
  simp only [addr] at ex ey ez ew
  unfold quarter
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The loads.
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, State.ea,
    at_, State.load32, ex, ey, ez, ew, ix, iy, iz, iw, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine WP.mono (qr_ok _ v[x] v[y] v[z] v[w] (by simp [h x hx]) (by simp [h y hy])
    (by simp [h z hz]) (by simp [h w hw])) fun s₁ ⟨ha, hb, hc, hd,
    hesi, hedi, hesp, hebp, hm, hrd, hwr⟩ => ?_
  simp only [ite_false, reduceCtorEq] at hesi hedi hesp hebp
  -- The stores.
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea, State.store32, hesi,
    ex, ey, ez, ew, hrd, hwr, hm, ox, oy, oz, ow, ite_true, Option.some.injEq,
    exists_eq_left', ha, hb, hc, hd]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 2
  all_goals try first | trivial | exact hedi | exact hesp | exact hebp
  · rw [qround_get _ _ _ _ _ k hk]
    simp only
    have g : ∀ j (hj : j < 16), s.mem.readW (wordAddr B j) 32 = v[j] := h
    by_cases e4 : w = k
    · subst e4; simp only [ite_true]
      rw [Mem.readW_writeW_self32]; rfl
    by_cases e3 : z = k
    · subst e3; simp only [ite_true, e4, ite_false]
      rw [readW_writeW_word _ _ _ hz hw nzw, Mem.readW_writeW_self32]; rfl
    by_cases e2 : y = k
    · subst e2; simp only [ite_true, e4, e3, ite_false]
      rw [readW_writeW_word _ _ _ hy hw nyw, readW_writeW_word _ _ _ hy hz nyz,
        Mem.readW_writeW_self32]; rfl
    by_cases e1 : x = k
    · subst e1; simp only [ite_true, e4, e3, e2, ite_false]
      rw [readW_writeW_word _ _ _ hx hw nxw, readW_writeW_word _ _ _ hx hz nxz,
        readW_writeW_word _ _ _ hx hy nxy, Mem.readW_writeW_self32]; rfl
    simp only [e4, e3, e2, e1, ite_false]
    rw [readW_writeW_word _ _ _ hk hw (Ne.symm e4), readW_writeW_word _ _ _ hk hz (Ne.symm e3),
      readW_writeW_word _ _ _ hk hy (Ne.symm e2), readW_writeW_word _ _ _ hk hx (Ne.symm e1)]
    exact g k hk
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (word_in_work B hx)).writeW
      (List.mem_singleton_self _) _ (word_in_work B hy)).writeW (List.mem_singleton_self _) _
      (word_in_work B hz)).writeW (List.mem_singleton_self _) _ (word_in_work B hw)

/-! ## Double rounds -/

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : Addr) (v : CState) (s₀ s : State) : Prop where
  holds : Holds B v s.mem
  frame : Frame [workR B] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esi : s.gpr .esi = s₀.gpr .esi
  edi : s.gpr .edi = s₀.gpr .edi
  esp : s.gpr .esp = s₀.gpr .esp
  ebp : s.gpr .ebp = s₀.gpr .ebp

theorem RI.ctx {B : Addr} {v : CState} {s₀ s : State} (h : RI B v s₀ s) (hc : Ctx B s₀) :
    Ctx B s :=
  ⟨fun k hk => by rw [h.esi]; exact hc.ea k hk, fun k hk => by rw [h.rd, h.wr]; exact hc.inw k hk,
    fun k hk => by rw [h.wr]; exact hc.outw k hk⟩

theorem quarter_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {B : Addr} {v : CState} {s₀ s : State} (hctx : Ctx B s₀)
    (h : RI B v s₀ s) :
    WP isa (quarter x y z w) s (RI B (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (quarter_ok hx hy hz hw hd (h.ctx hctx) h.holds)
    fun _ ⟨hh, hf, hrd, hwr, hesi, hedi, hesp, hebp⟩ =>
      ⟨hh, h.frame.trans hf, hrd.trans h.rd, hwr.trans h.wr, hesi.trans h.esi, hedi.trans h.edi,
        hesp.trans h.esp, hebp.trans h.ebp⟩

theorem doubleRound_ok {B : Addr} {v : CState} {s₀ s : State} (hctx : Ctx B s₀)
    (h : RI B v s₀ s) : WP isa doubleRound s (RI B (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h1) fun _ h2 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h3) fun _ h4 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h5) fun _ h6 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h6) fun _ h7 => ?_)
  exact quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) hctx h7

theorem rounds_ok {B : Addr} {v : CState} {s₀ : State} (hctx : Ctx B s₀) (h : Holds B v s₀.mem) :
    ∀ n, WP isa (rounds n) s₀ (RI B (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok hctx h n) fun _ h' => doubleRound_ok hctx h')

end VG.Proof.ChaCha20.X86
