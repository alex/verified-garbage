import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.ChaCha20.X86_64
import VerifiedGarbage.Proof.ChaCha20.Spec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Basic

/-!
# ChaCha20 block function on x86-64: the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) (va vb vc vd : Word)
    (ha : s.gpr a = va.setWidth 64) (hb : s.gpr b = vb.setWidth 64)
    (hc : s.gpr c = vc.setWidth 64) (hd : s.gpr d = vd.setWidth 64) :
    WP isa (.block (qr a b c d)) s fun s' =>
      s'.gpr a = (quarterRound va vb vc vd).1.setWidth 64 ∧
      s'.gpr b = (quarterRound va vb vc vd).2.1.setWidth 64 ∧
      s'.gpr c = (quarterRound va vb vc vd).2.2.1.setWidth 64 ∧
      s'.gpr d = (quarterRound va vb vc vd).2.2.2.setWidth 64 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [qr, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execShift32, readSrc32,
    isa, State.setReg32, State.setReg, arithFlags, State.setFlags, ha, hb, hc, hd,
    hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm,
    ite_true, ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- Word `k` is in its register `wreg k` (rather than its slot): words 8 and 9
when `p = false`, words 10 and 11 when `p = true`, and always the others. -/
def inReg (p : Bool) (k : Nat) : Bool :=
  if k = 8 ∨ k = 9 then !p else if k = 10 ∨ k = 11 then p else true

/-- The home slot of word `k` (8–11). -/
abbrev slotAddr (buf : Addr) (k : Nat) : Addr := buf + BitVec.ofInt 64 ((slotOff k : Nat) : Int)

/-- The state `v` is in the registers and slots of layout `p`. -/
def Holds (buf : Addr) (p : Bool) (v : CState) (s : State) : Prop :=
  ∀ k (hk : k < 16), if inReg p k then s.gpr (wreg k) = v[k].setWidth 64
    else s.mem.readW (slotAddr buf k) 32 = v[k]

theorem wreg_ne_rsi (k : Nat) : wreg k ≠ .rsi := by
  unfold wreg; split <;> decide

theorem wreg_ne_rsp (k : Nat) : wreg k ≠ .rsp := by
  unfold wreg; split <;> decide

/-! ## One quarter round -/

/-- The side conditions of `quarter_ok`, decidable for concrete arguments:
the four words are in distinct registers, and no other word in a register
shares one of them. -/
def QSide (p : Bool) (x y z w : Nat) : Bool :=
  inReg p x && inReg p y && inReg p z && inReg p w && [x, y, z, w].Nodup &&
  [wreg x, wreg y, wreg z, wreg w].Nodup &&
  (List.range 16).all fun k => [x, y, z, w].contains k || !inReg p k ||
    !([wreg x, wreg y, wreg z, wreg w].contains (wreg k))

theorem quarter_ok {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : QSide p x y z w = true) {buf : Addr} {v : CState} {s : State}
    (h : Holds buf p v s) :
    WP isa (quarter x y z w) s fun s' =>
      Holds buf p (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rsp = s.gpr .rsp := by
  simp only [QSide, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hq
  obtain ⟨⟨⟨⟨⟨⟨ix, iy⟩, iz⟩, iw⟩, nd⟩, nr⟩, others⟩ := hq
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using nd
  have nr' : (wreg x ≠ wreg y ∧ wreg x ≠ wreg z ∧ wreg x ≠ wreg w) ∧
      (wreg y ≠ wreg z ∧ wreg y ≠ wreg w) ∧ wreg z ≠ wreg w := by simpa using nr
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  obtain ⟨⟨rxy, rxz, rxw⟩, ⟨ryz, ryw⟩, rzw⟩ := nr'
  have gx := h x hx; have gy := h y hy; have gz := h z hz; have gw := h w hw
  simp only [ix, iy, iz, iw, ite_true] at gx gy gz gw
  refine WP.mono (qr_ok rxy rxz rxw ryz ryw rzw s _ _ _ _ gx gy gz gw)
    fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ => ⟨fun k hk => ?_, hm, hrd, hwr,
      hr _ (wreg_ne_rsi x).symm (wreg_ne_rsi y).symm (wreg_ne_rsi z).symm (wreg_ne_rsi w).symm,
      hr _ (wreg_ne_rsp x).symm (wreg_ne_rsp y).symm (wreg_ne_rsp z).symm (wreg_ne_rsp w).symm⟩
  rw [qround_get _ _ _ _ _ k hk]
  simp only
  by_cases ew : w = k
  · subst ew; simp only [iw, ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [iz, ite_true, ew]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [iy, ite_true, ew, ez]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ix, ite_true, ew, ez, ey]; exact ha
  simp only [ew, ez, ey, ex, ite_false]
  have hk' := h k hk
  have ho := others k hk
  split
  · rename_i hin
    simp only [hin, ite_true] at hk'
    have ho' : wreg k ≠ wreg x ∧ wreg k ≠ wreg y ∧ wreg k ≠ wreg z ∧ wreg k ≠ wreg w := by
      simpa [Ne.symm ex, Ne.symm ey, Ne.symm ez, Ne.symm ew, hin] using ho
    rw [hr _ ho'.1 ho'.2.1 ho'.2.2.1 ho'.2.2.2]; exact hk'
  · rename_i hin
    simp only [hin] at hk'
    rw [hm]; exact hk'

/-! ## Addresses in `buf` -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) n (p + BitVec.ofInt 64 (e : Int)) k := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

/-- Reading a 32-bit word after writing a (32- or 64-bit) value elsewhere in `buf`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e : Nat}
    (hw' : w' = 32 ∨ w' = 64) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + w' / 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 32 =
      m.readW (p + BitVec.ofInt 64 (d : Int)) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  simp only [Region.Contains, ofInt_natCast]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

/-- The four home slots. -/
abbrev slotR (buf : Addr) : Region := ⟨buf + BitVec.ofInt 64 ((128 : Nat) : Int), 16⟩

/-! ## Swapping the pair of third-row words -/

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (buf : Addr) (p : Bool) (v : CState) (s₀ s : State) : Prop where
  holds : Holds buf p v s
  frame : Frame [slotR buf] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem quarter_step {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : QSide p x y z w = true) {buf : Addr} {v : CState} {s₀ s : State}
    (h : RI buf p v s₀ s) :
    WP isa (quarter x y z w) s (RI buf p (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (quarter_ok hx hy hz hw hq h.holds) fun _ ⟨hh, hm, hrd, hwr, hrsi, hrsp⟩ =>
    ⟨hh, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr, hrsi.trans h.rsi, hrsp.trans h.rsp⟩

abbrev bufR (buf : Addr) : Region := ⟨buf, 256⟩

/-- `readW_writeW_off` for the literal addresses `p + N#64` that `norm_num` produces. -/
theorem readW_writeW_lit (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e : Nat}
    (hw' : w' = 32 ∨ w' = 64) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + w' / 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 := by
  have := readW_writeW_off m p v hw' hd he h
  simpa only [ofInt_natCast] using this

theorem slotR_contains (buf : Addr) {d : Nat} (h1 : 128 ≤ d) (h2 : d + 4 ≤ 144) :
    (slotR buf).Contains (buf + BitVec.ofNat 64 d) 4 := by
  simp only [Region.Contains, ofInt_natCast]
  rw [show buf + BitVec.ofNat 64 d - (buf + BitVec.ofNat 64 128) = BitVec.ofNat 64 (d - 128) by
    bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem in_buf {rs ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 256) :
    InRegions (rs ++ ws) (buf + BitVec.ofInt 64 (d : Int)) n :=
  ⟨bufR buf, List.mem_append_right _ hw, contains_off h (by omega)⟩

theorem out_buf {ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 256) :
    InRegions ws (buf + BitVec.ofInt 64 (d : Int)) n :=
  ⟨bufR buf, hw, contains_off h (by omega)⟩

theorem swap_step {p : Bool} {buf : Addr} {v : CState} {s₀ s : State} (h : RI buf p v s₀ s)
    (hbuf : s₀.gpr .rsi = buf) (hw : bufR buf ∈ s₀.wr) :
    WP isa (swap (if p then 10 else 8) (if p then 8 else 10)) s (RI buf (!p) v s₀) := by
  have hrsi : s.gpr .rsi = buf := h.rsi.trans hbuf
  have hw' : bufR buf ∈ s.wr := h.wr ▸ hw
  have i128 := in_buf (rs := s.rd) hw' (d := 128) (n := 4) (by omega)
  have i132 := in_buf (rs := s.rd) hw' (d := 132) (n := 4) (by omega)
  have i136 := in_buf (rs := s.rd) hw' (d := 136) (n := 4) (by omega)
  have i140 := in_buf (rs := s.rd) hw' (d := 140) (n := 4) (by omega)
  have o128 := out_buf hw' (d := 128) (n := 4) (by omega)
  have o132 := out_buf hw' (d := 132) (n := 4) (by omega)
  have o136 := out_buf hw' (d := 136) (n := 4) (by omega)
  have o140 := out_buf hw' (d := 140) (n := 4) (by omega)
  have hh := h.holds
  have g8 := hh 8 (by omega); have g9 := hh 9 (by omega)
  have g10 := hh 10 (by omega); have g11 := hh 11 (by omega)
  norm_num at i128 i132 i136 i140 o128 o132 o136 o140
  have hf₁ := h.frame
  cases p
  · apply WP.of_runBlock
    simp only [slotOff, runBlock_cons, exec, isa, ea_at, State.store32, hrsi]
    norm_num [runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc32, isa, ea_at, State.load32, State.store32, State.setReg32, State.setReg,
      i128, i132, i136, i140, o128, o132, o136, o140, hrsi]
    refine ⟨fun k hk => ?_, ?_, h.rd, h.wr, by simp [h.rsi], by simp [h.rsp]⟩
    · have hk' := hh k hk
      simp only [slotAddr, slotOff] at hk'
      interval_cases k <;> norm_num [inReg, wreg, slotAddr, slotOff] at hk' ⊢ <;>
      simp (disch := norm_num) only [readW_writeW_lit, Mem.readW_writeW_self32, hk',
        BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    · exact (hf₁.writeW (List.mem_singleton_self _) _
        (slotR_contains buf (d := 128) (by omega) (by omega))).writeW
        (List.mem_singleton_self _) _ (slotR_contains buf (d := 132) (by omega) (by omega))
  · apply WP.of_runBlock
    simp only [slotOff, runBlock_cons, exec, isa, ea_at, State.store32, hrsi]
    norm_num [runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc32, isa, ea_at, State.load32, State.store32, State.setReg32, State.setReg,
      i128, i132, i136, i140, o128, o132, o136, o140, hrsi]
    refine ⟨fun k hk => ?_, ?_, h.rd, h.wr, by simp [h.rsi], by simp [h.rsp]⟩
    · have hk' := hh k hk
      simp only [slotAddr, slotOff] at hk'
      interval_cases k <;> norm_num [inReg, wreg, slotAddr, slotOff] at hk' ⊢ <;>
      simp (disch := norm_num) only [readW_writeW_lit, Mem.readW_writeW_self32, hk',
        BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    · exact (hf₁.writeW (List.mem_singleton_self _) _
        (slotR_contains buf (d := 136) (by omega) (by omega))).writeW
        (List.mem_singleton_self _) _ (slotR_contains buf (d := 140) (by omega) (by omega))

/-! ## Double rounds -/

theorem doubleRound_ok {buf : Addr} {v : CState} {s₀ s : State} (h : RI buf false v s₀ s)
    (hbuf : s₀.gpr .rsi = buf) (hw : bufR buf ∈ s₀.wr) :
    WP isa doubleRound s (RI buf false (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (swap_step h₂ hbuf hw) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (swap_step h₇ hbuf hw) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₈) fun s₉ h₉ => ?_)
  exact WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₉) fun _ h => h

theorem rounds_ok {buf : Addr} {v : CState} {s₀ : State} (h : Holds buf false v s₀)
    (hbuf : s₀.gpr .rsi = buf) (hw : bufR buf ∈ s₀.wr) :
    ∀ n, WP isa (rounds n) s₀ (RI buf false (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h hbuf hw n) fun _ h' => doubleRound_ok h' hbuf hw)

end VG.Proof.ChaCha20.X86_64
