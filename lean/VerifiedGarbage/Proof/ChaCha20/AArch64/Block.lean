import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Omega

section

section

/-!
# ChaCha20 block function on AArch64: the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

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
    runBlock_nil, exec_add, exec_logic,
    exec_ror_w (show 16 < 32 by decide), exec_ror_w (show 20 < 32 by decide),
    exec_ror_w (show 24 < 32 by decide), exec_ror_w (show 25 < 32 by decide), isa,
    State.read, State.write, Size.bits, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, hab.symm,
    hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq,
    exists_eq_left']
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- The state `v` is in the registers. -/
def Holds (v : CState) (s : State) : Prop := ∀ k (hk : k < 16), s.gpr (wreg k) = v[k].setWidth 64

/-- The registers that hold state words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : CState) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem quarter_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa (quarter x y z w) s (RI (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ne : ∀ {i j}, i < 16 → j < 16 → i ≠ j → wreg i ≠ wreg j := fun hi hj hij e =>
    hij (wreg_inj hi hj e)
  refine WP.mono (qr_ok (ne hx hy nxy) (ne hx hz nxz) (ne hx hw nxw) (ne hy hz nyz)
    (ne hy hw nyw) (ne hz hw nzw) s _ _ _ _ (h.holds x hx) (h.holds y hy) (h.holds z hz)
    (h.holds w hw)) fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ =>
    ⟨fun k hk => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hr' => ?_⟩
  · rw [qround_get _ _ _ _ _ k hk]
    simp only
    by_cases ew : w = k
    · subst ew; simp only [ite_true]; exact hd
    by_cases ez : z = k
    · subst ez; simp only [ite_true, ew, ite_false]; exact hc
    by_cases ey : y = k
    · subst ey; simp only [ite_true, ew, ez, ite_false]; exact hb
    by_cases ex : x = k
    · subst ex; simp only [ite_true, ew, ez, ey, ite_false]; exact ha
    simp only [ew, ez, ey, ex, ite_false]
    rw [hr _ (ne hk hx (Ne.symm ex)) (ne hk hy (Ne.symm ey)) (ne hk hz (Ne.symm ez))
      (ne hk hw (Ne.symm ew))]
    exact h.holds k hk
  · have nw : ∀ i < 16, r ≠ wreg i := fun i hi e => hr' ⟨i, hi, e⟩
    rw [hr r (nw x hx) (nw y hy) (nw z hz) (nw w hw)]
    exact h.keep r hr'

theorem doubleRound_ok {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₇) fun _ h => h

theorem rounds_ok {v : CState} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.ChaCha20.AArch64

end

/-!
# ChaCha20 block function on AArch64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.AArch64

/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is unspecified). `buf` may not
overlap `state`. The pointers are public; the state (key, counter and nonce)
is secret. -/
def blockAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let buf : Region := ⟨s.gpr .x1, 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state
  post s s' := stateAt s'.mem (s.gpr .x1) = block (stateAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .x0
abbrev buf : Addr := s₀.gpr .x1
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev bufR : Region := ⟨buf s₀, 256⟩
abbrev outR : Region := ⟨buf s₀, 64⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (st s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by lit_omega) (by lit_omega)⟩

theorem in_out {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (buf s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem out_out {k : Nat} (hk : k < 16) : InRegions s₀.wr (buf s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

/-- Reading the input state after writes to the output only. -/
theorem read_st {m : Mem} (hf : Frame [outR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  have hd : (stR s₀).Disjoint (outR s₀) :=
    Region.Disjoint.sub_right hp.buf_st.symm (Region.sub_prefix (by lit_omega))
  rw [hf.readW (r := stR s₀) (contains_off (by lit_omega) (by lit_omega)) (by simpa using hd) (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem out_sep (p : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := Offset.sep p (by lit_omega) (by lit_omega) (by lit_omega)

theorem readW_writeW_out (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (out_sep p hj hk h) (by decide)

theorem not_words_x0 : ¬ Words .x0 := by
  rintro ⟨k, hk, h⟩; exact (show ∀ k < 16, Reg.x0 ≠ wreg k by decide) k hk h
theorem not_words_x1 : ¬ Words .x1 := by
  rintro ⟨k, hk, h⟩; exact (show ∀ k < 16, Reg.x1 ≠ wreg k by decide) k hk h
theorem not_words_preserved {r : Reg} (hr : r ∈ preserved) : ¬ Words r := by
  rintro ⟨k, hk, rfl⟩
  exact (show ∀ k < 16, wreg k ∉ preserved by decide) k hk hr

/-! ## Loading the state -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → s.gpr (wreg j) = (V s₀)[j].setWidth 64
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.ldr .w (wreg n) .x0 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hx0 : s.gpr .x0 = st s₀ := h.keep _ not_words_x0
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [h.rd, h.wr, hx0]; exact hp.in_st hn _
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem]; exact hp.read_st (Frame.refl _ _) hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_ldr_w (show 4 * n % 4 = 0 ∧ 4 * n < 16384 by omega) hin, isa,
    Option.some.injEq, exists_eq_left', hx0, hv]
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e : wreg j ≠ wreg n := fun e => absurd (wreg_inj hj hn e) (by lit_omega)
      simp only [e, ite_false]; exact h.loaded j hj hjn
    · simp [Size.bits]
  · have e : r ≠ wreg n := fun e => hr ⟨n, hn, e⟩
    simp only [State.write, e, ite_false]; exact h.keep r hr

/-! ## Adding the input state -/

/-- After finishing words `1 … i`: word 0 of the rounds' result `R` is in the
output, words `1 … i` of the result are in the output, and words `i + 1 … 15`
are still in their registers. -/
structure FI (s₀ : State) (R : CState) (sB : State) (i : Nat) (s : State) : Prop where
  out0 : s.mem.readW (buf s₀ + BitVec.ofNat 64 (4 * 0)) 32 = R[0]
  done : ∀ j (hj : j < 16), 1 ≤ j → j ≤ i →
    s.mem.readW (buf s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j] + (V s₀)[j]
  rest : ∀ j (hj : j < 16), i < j → s.gpr (wreg j) = R[j].setWidth 64
  frame : Frame [outR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem add_step {s₀ : State} (hp : Pre s₀) {R : CState} {sB : State} {i : Nat} (hi : i < 15)
    {s : State} (h : FI s₀ R sB i s) :
    WP isa (.block (addWord (i + 1))) s (FI s₀ R sB (i + 1)) := by
  have hk : i + 1 < 16 := by omega
  have hx0 : s.gpr .x0 = st s₀ := h.keep _ not_words_x0
  have hx1 : s.gpr .x1 = buf s₀ := h.keep _ not_words_x1
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * (i + 1))) 4 := by
    rw [h.rd, h.wr, hx0]; exact hp.in_st hk _
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * (i + 1))) 4 := by
    rw [h.wr, hx1]; exact hp.out_out hk
  have hv := hp.read_st h.frame hk
  have hr := h.rest (i + 1) hk (by lit_omega)
  have hne : wreg (i + 1) ≠ .x2 := fun e => absurd (wreg_inj hk (show 0 < 16 by omega) e) (by lit_omega)
  have n1 : Reg.x1 ≠ wreg (i + 1) := fun e => not_words_x1 ⟨_, hk, e⟩
  apply WP.of_runBlock
  simp only [addWord, runBlock_cons, runStep_some,
    exec_ldr_w (show 4 * (i + 1) % 4 = 0 ∧ 4 * (i + 1) < 16384 by omega) hin, exec_add, isa, hx0, hv]
  simp (config := {decide := true}) only [State.write, State.read, Size.bits, hne, ite_false,
    hr, ite_true, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [exec_str_w (show 4 * (i + 1) % 4 = 0 ∧ 4 * (i + 1) < 16384 by omega)
    (by simpa [State.write, hne, n1] using hout)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left', ite_true, ite_false, hx1, n1, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have ho : (outR s₀).Contains (buf s₀ + BitVec.ofNat 64 (4 * (i + 1))) (32 / 8) :=
    contains_off (by lit_omega) (by lit_omega)
  refine ⟨?_, fun j hj h1 hji => ?_, fun j hj hij => ?_, h.frame.writeW (List.mem_singleton_self _) _ ho,
    h.rd, h.wr, fun r hr' => ?_⟩
  · rw [readW_writeW_out _ _ _ (by lit_omega) hk (by lit_omega)]; exact h.out0
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hji) with hji | rfl
    · rw [readW_writeW_out _ _ _ hj hk (by lit_omega)]; exact h.done j hj h1 (by lit_omega)
    · rw [Mem.readW_writeW_self32]
  · have e1 : wreg j ≠ wreg (i + 1) := fun e => absurd (wreg_inj hj hk e) (by lit_omega)
    have e2 : wreg j ≠ .x2 := fun e => absurd (wreg_inj hj (show 0 < 16 by omega) e) (by lit_omega)
    simp only [e1, e2, ite_false]; exact h.rest j hj (by lit_omega)
  · have e1 : r ≠ wreg (i + 1) := fun e => hr' ⟨i + 1, hk, e⟩
    have e2 : r ≠ .x2 := fun e => hr' ⟨0, by omega, e⟩
    simp only [e1, e2, ite_false]; exact h.keep r hr'

/-! ## Storing word 0, and finishing it -/

theorem first_ok {s₀ : State} (hp : Pre s₀) {R : CState} {s : State} (hh : Holds R s)
    (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r) :
    WP isa (.block [.str .w .x2 .x1 0]) s (FI s₀ R s 0) := by
  have hx1 : s.gpr .x1 = buf s₀ := hk _ not_words_x1
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 4 := by
    rw [hwr, hx1]; exact hp.out_out (k := 0) (by lit_omega)
  have h0 : s.gpr .x2 = R[0].setWidth 64 := hh 0 (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, isa,
    exec_str_w (show 0 % 4 = 0 ∧ 0 < 16384 by omega) hout, Option.some.injEq, exists_eq_left', hx1, h0,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  refine ⟨by simp only [Nat.mul_zero]; exact Mem.readW_writeW_self32 _ _ _, fun j _ h1 h2 => absurd h2 (by lit_omega),
    fun j hj _ => hh j hj, ?_, hrd, hwr, hk⟩
  rw [← hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by lit_omega) (by lit_omega))

theorem last_eq : [Instr.ldr .w .x2 .x0 0, .ldr .w .x3 .x1 0, .add .w .x2 .x3 .x2, .str .w .x2 .x1 0] =
    [.ldr .w .x2 .x0 (4 * 0), .ldr .w .x3 .x1 (4 * 0), .add .w .x2 .x3 .x2, .str .w .x2 .x1 (4 * 0)] :=
  rfl

theorem last_ok {s₀ : State} (hp : Pre s₀) {R : CState} {sB s : State} (h : FI s₀ R sB 15 s) :
    WP isa (.block [.ldr .w .x2 .x0 0, .ldr .w .x3 .x1 0, .add .w .x2 .x3 .x2, .str .w .x2 .x1 0]) s
      fun s' => (∀ j (hj : j < 16),
        s'.mem.readW (buf s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j] + (V s₀)[j]) ∧
        (∀ r, ¬ Words r → s'.gpr r = s₀.gpr r) := by
  have hx0 : s.gpr .x0 = st s₀ := h.keep _ not_words_x0
  have hx1 : s.gpr .x1 = buf s₀ := h.keep _ not_words_x1
  have hin : InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * 0)) 4 := by
    rw [h.rd, h.wr]; exact hp.in_st (by lit_omega) _
  have hin' : InRegions (s.rd ++ s.wr) (buf s₀ + BitVec.ofNat 64 (4 * 0)) 4 := by
    rw [h.rd, h.wr]; exact hp.in_out (by lit_omega) _
  have hout : InRegions s.wr (buf s₀ + BitVec.ofNat 64 (4 * 0)) 4 := by
    rw [h.wr]; exact hp.out_out (by lit_omega)
  have hv := hp.read_st h.frame (k := 0) (by lit_omega)
  apply WP.of_runBlock
  rw [last_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w
    (show 4 * 0 % 4 = 0 ∧ 4 * 0 < 16384 by omega), exec_add, exec_str_w
    (show 4 * 0 % 4 = 0 ∧ 4 * 0 < 16384 by omega), isa, State.read, State.write, Size.bits, hx0,
    hx1, hin, hin', hout, hv, h.out0, ite_true, ite_false, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun r hr => ?_⟩
  · by_cases hj0 : j = 0
    · subst hj0; exact Mem.readW_writeW_self32 _ _ _
    · rw [readW_writeW_out _ _ _ hj (show 0 < 16 by omega) hj0]
      exact h.done j hj (by lit_omega) (by lit_omega)
  · have e2 : r ≠ .x2 := fun e => hr ⟨0, by omega, e⟩
    have e3 : r ≠ .x3 := fun e => hr ⟨1, by omega, e⟩
    simp only [e2, e3, ite_false]; exact h.keep r hr

/-! ## The whole function -/

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

theorem finish_split : finish = (([.str .w .x2 .x1 0] : List Instr) ++ (List.range 15).flatMap (fun i => addWord (i + 1))) ++
    ([.ldr .w .x2 .x0 0, .ldr .w .x3 .x1 0, .add .w .x2 .x3 .x2, .str .w .x2 .x1 0] : List Instr) := by
  unfold finish; rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.blockAArch64.post s₀ s' := by
  have hl₀ : LI s₀ 0 s₀ := ⟨fun _ _ h => absurd h (by lit_omega), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₀ (LI s₀ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₀) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _) s₀ hl₀
  refine WP.seq (WP.mono hload fun s₁ h₁ => ?_)
  have hh₁ : Holds (V s₀) s₁ := fun k hk => h₁.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₁ 10) fun s₂ h₂ => ?_)
  have hk₂ : ∀ r, ¬ Words r → s₂.gpr r = s₀.gpr r := fun r hr => (h₂.keep r hr).trans (h₁.keep r hr)
  rw [finish_split, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (first_ok hp h₂.holds (h₂.mem.trans h₁.mem) (h₂.rd.trans h₁.rd)
    (h₂.wr.trans h₁.wr) hk₂) fun s₃ h₃ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (FI s₀ (Rs s₀) s₂) (fun i s hi h => add_step hp hi h) 15 (Nat.le_refl _)
    s₃ h₃) fun s₄ h₄ => ?_
  refine WP.mono (last_ok hp h₄) fun s' ⟨hout, hk'⟩ => ⟨fun r hr => hk' r (not_words_preserved hr), ?_⟩
  exact block_post hout

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockAArch64.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩

theorem block_verified :
    Verified AArch64.target Impl.ChaCha20.AArch64.block (Spec.ChaCha20.blockContract AArch64.abi) :=
      by
  refine Verified.of_correct block_correct ?_ (by
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, AArch64.abi, AArch64.argRegs,
      Proof.ChaCha20.blockAArch64]
      [satState] using satState)
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

end VG.Proof.ChaCha20.AArch64

end

