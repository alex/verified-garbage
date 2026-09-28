import VerifiedGarbage.Proof.ChaCha20.Arm.Rounds
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.ChaCha20.Arm.Contract

/-!
# ChaCha20 block function on 32-bit ARM: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.Arm

open VG VG.Arm VG.Impl.ChaCha20.Arm VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## Offsets -/

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) n (p + BitVec.ofNat 64 e) k := by
  intro x hx hy
  bv_omega

/-- Reading a 32-bit word after writing one elsewhere in `buf`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [show p + BitVec.ofNat 64 d - (p + BitVec.ofNat 64 a) = BitVec.ofNat 64 (d - a) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

/-- Two sub-ranges of `buf` that do not overlap. -/
theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, la⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 b, lb⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem sub_buf (p : Addr) {a len : Nat} (h : a + len ≤ 256) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p, 256⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-- The output area of `buf`. -/
abbrev outR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 0, 64⟩
/-- Everything in `buf` but the saved registers: output, input copy and slots. -/
abbrev workR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 0, 144⟩

theorem sub_work (p : Addr) {a len : Nat} (h : a + len ≤ 144) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ (workR p) := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - (p + BitVec.ofNat 64 0)).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - (p + BitVec.ofNat 64 0) = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by
      bv_omega, BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

theorem frame_work {p : Addr} {a len : Nat} (h : a + len ≤ 144) {m m' : Mem}
    (hf : Frame [⟨p + BitVec.ofNat 64 a, len⟩] m m') : Frame [workR p] m m' :=
  hf.sub fun r hr => ⟨workR p, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_work p h⟩

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : BitVec 32 := s₀.gpr .r0
abbrev buf : BitVec 32 := s₀.gpr .r1
/-- The 64-bit addresses of `state` and `buf`. -/
abbrev SA : Addr := State.addr (st s₀)
abbrev BA : Addr := State.addr (buf s₀)
abbrev stR : Region := ⟨SA s₀, 64⟩
abbrev bufR : Region := ⟨BA s₀, 256⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (buf s₀).toNat + 256 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem eaB {off : Nat} (h : off < 256) :
    State.addr (buf s₀ + BitVec.ofNat 32 off) = BA s₀ + BitVec.ofNat 64 off :=
  addr_add (by have := hp.buf_fits; omega)

theorem eaS {off : Nat} (h : off < 64) :
    State.addr (st s₀ + BitVec.ofNat 32 off) = SA s₀ + BitVec.ofNat 64 off :=
  addr_add (by have := hp.st_fits; omega)

theorem hw : bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by omega) (by omega)⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (contains_off (by omega) (by omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem in_lt {k : Nat} (hk : k < 16) : inOff k + 4 ≤ 256 := by simp only [inOff]; omega
theorem out_lt {k : Nat} (hk : k < 16) : outOff k + 4 ≤ 256 := by simp only [outOff]; omega

/-! ## Copying the state -/

set_option maxHeartbeats 400000 in
theorem copyWord_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16) {s : State}
    (hr0 : s.gpr .r0 = st s₀) (hr1 : s.gpr .r1 = buf s₀)
    (hin : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4)
    (hw : bufR s₀ ∈ s.wr) :
    WP isa (.block (copyWord k)) s fun s' =>
      s'.mem = (if 9 ≤ k ∧ k ≤ 11 then
          (s.mem.writeW (BA s₀ + BitVec.ofNat 64 (inOff k))
            (s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32)).writeW
            (BA s₀ + BitVec.ofNat 64 (slotOff k)) (s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32)
        else s.mem.writeW (BA s₀ + BitVec.ofNat 64 (inOff k))
          (s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32)) ∧
      (∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o₁ : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (inOff k)) 4 :=
    ⟨bufR s₀, hw, contains_off (in_lt hk) (by simp only [inOff]; omega)⟩
  have e0 := hp.eaS (show 4 * k < 64 by omega)
  have e1 := hp.eaB (show inOff k < 256 by simp only [inOff]; omega)
  have h4 : 4 * k < 4096 := by omega
  have h5 : inOff k < 4096 := by simp only [inOff]; omega
  apply WP.of_runBlock
  by_cases h : 9 ≤ k ∧ k ≤ 11
  · have o₂ : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (slotOff k)) 4 :=
      ⟨bufR s₀, hw, contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)⟩
    have e2 := hp.eaB (show slotOff k < 256 by simp only [slotOff]; omega)
    have h6 : slotOff k < 4096 := by simp only [slotOff]; omega
    simp (config := {decide := true}) only [copyWord, h, and_self, ite_true, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
          exec, isa, State.setReg, State.load32, State.store32, hr0, hr1,
      e0, e1, e2, h4, h5, h6, hin, o₁, o₂, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · simp (config := {decide := true}) only [copyWord, h, ite_false, List.append_nil,
      runBlock_cons, runStep_some, runBlock_nil,
      exec, isa, State.setReg, State.load32, State.store32, hr0, hr1, e0, e1, h4, h5, hin, o₁,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue's stores. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r2 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨BA s₀ + BitVec.ofNat 64 64, 80⟩] s₁.mem s.mem
  inw : ∀ j (hj : j < 16), j < n → s.mem.readW (BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = (V s₀)[j]
  slot : ∀ j (hj : j < 16), j < n → (9 ≤ j ∧ j ≤ 11) →
    s.mem.readW (BA s₀ + BitVec.ofNat 64 (slotOff j)) 32 = (V s₀)[j]

theorem copy_step {s₀ s₁ : State} (hp : Pre s₀) (h₁ : s₁.gpr = s₀.gpr)
    (hf₁ : Frame [bufR s₀] s₀.mem s₁.mem) {n : Nat} (hn : n < 16)
    {s : State} (hc : CI s₀ s₁ n s) : WP isa (.block (copyWord n)) s (CI s₀ s₁ (n + 1)) := by
  have hr0 : s.gpr .r0 = st s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hr1 : s.gpr .r1 = buf s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hfs : Frame [bufR s₀] s₀.mem s.mem :=
    hf₁.trans (hc.frame.sub fun r hr => ⟨bufR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_buf _ (by omega)⟩)
  refine WP.mono (copyWord_ok hp hn hr0 hr1 (by rw [hc.rd, hc.wr]; exact hp.in_st hn _)
    (by rw [hc.wr]; exact hp.hw)) fun s' ⟨hm, hg, hrd, hwr⟩ => ?_
  have hx : s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := hp.read_st hfs hn
  have cin : (⟨BA s₀ + BitVec.ofNat 64 64, 80⟩ : Region).Contains
      (BA s₀ + BitVec.ofNat 64 (inOff n)) (32 / 8) :=
    contains_sub _ (by simp [inOff]) (by simp [inOff]; omega) (by omega)
  refine ⟨fun r hr => (hg r hr).trans (hc.gpr r hr), hrd.trans hc.rd, hwr.trans hc.wr, ?_, ?_, ?_⟩
  · rw [hm]
    split
    · exact (hc.frame.writeW (List.mem_singleton_self _) _ cin).writeW (List.mem_singleton_self _) _
        (contains_sub _ (by simp [slotOff]; omega) (by simp [slotOff]; omega) (by omega))
    · exact hc.frame.writeW (List.mem_singleton_self _) _ cin
  · intro j hj hjn
    rw [hm]
    have e1 : ∀ m : Mem, (m.writeW (BA s₀ + BitVec.ofNat 64 (slotOff n)) ((V s₀)[n])).readW
        (BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = m.readW (BA s₀ + BitVec.ofNat 64 (inOff j)) 32 :=
      fun m => readW_writeW_off m _ _ (by simp [inOff]; omega) (by simp [slotOff]; omega)
        (by simp [inOff, slotOff]; omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : (s.mem.writeW (BA s₀ + BitVec.ofNat 64 (inOff n)) ((V s₀)[n])).readW
          (BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = s.mem.readW (BA s₀ + BitVec.ofNat 64 (inOff j)) 32 :=
        readW_writeW_off _ _ _ (by simp [inOff]; omega) (by simp [inOff]; omega)
          (by simp [inOff]; omega)
      rw [hx]; split <;> simp only [e1, e2, hc.inw j hj hjn]
    · rw [hx]; split <;> simp only [e1, Mem.readW_writeW_self32]
  · intro j hj hjn h911
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : ∀ m : Mem, ∀ d, d = inOff n ∨ d = slotOff n → (m.writeW (BA s₀ + BitVec.ofNat 64 d)
          ((V s₀)[n])).readW (BA s₀ + BitVec.ofNat 64 (slotOff j)) 32 =
          m.readW (BA s₀ + BitVec.ofNat 64 (slotOff j)) 32 := by
        rintro m d (rfl | rfl)
        · exact readW_writeW_off _ _ _ (by simp [slotOff]; omega) (by simp [inOff]; omega)
            (by simp [inOff, slotOff]; omega)
        · exact readW_writeW_off _ _ _ (by simp [slotOff]; omega) (by simp [slotOff]; omega)
            (by simp [slotOff]; omega)
      rw [hx]; split <;> simp only [e2 _ _ (.inl rfl), e2 _ _ (.inr rfl), hc.slot j hj hjn h911]
    · simp only [hx, h911, and_self, ite_true, Mem.readW_writeW_self32]

/-! ## Saving and restoring the callee-saved registers -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((((((s₀.mem.writeW (BA s₀ + BitVec.ofNat 64 144) (s₀.gpr .r4)).writeW (BA s₀ + BitVec.ofNat 64 148) (s₀.gpr .r5)).writeW (BA s₀ + BitVec.ofNat 64 152) (s₀.gpr .r6)).writeW (BA s₀ + BitVec.ofNat 64 156) (s₀.gpr .r7)).writeW (BA s₀ + BitVec.ofNat 64 160) (s₀.gpr .r8)).writeW (BA s₀ + BitVec.ofNat 64 164) (s₀.gpr .r9)).writeW (BA s₀ + BitVec.ofNat 64 168) (s₀.gpr .r10)).writeW (BA s₀ + BitVec.ofNat 64 172) (s₀.gpr .r11)).writeW (BA s₀ + BitVec.ofNat 64 176) (s₀.gpr .lr))

/-- The callee-saved registers are saved in `buf`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (BA s₀ + BitVec.ofNat 64 144) 32 = s₀.gpr .r4 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 148) 32 = s₀.gpr .r5 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 152) 32 = s₀.gpr .r6 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 156) 32 = s₀.gpr .r7 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 160) 32 = s₀.gpr .r8 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 164) 32 = s₀.gpr .r9 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 168) 32 = s₀.gpr .r10 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 172) 32 = s₀.gpr .r11 ∧
  m.readW (BA s₀ + BitVec.ofNat 64 176) 32 = s₀.gpr .lr

theorem save_eq : save = [
    .str .r4 .r1 144,
    .str .r5 .r1 148,
    .str .r6 .r1 152,
    .str .r7 .r1 156,
    .str .r8 .r1 160,
    .str .r9 .r1 164,
    .str .r10 .r1 168,
    .str .r11 .r1 172,
    .str .lr .r1 176] := rfl

theorem restore_eq : restore = [
    .ldr .r4 .r1 144,
    .ldr .r5 .r1 148,
    .ldr .r6 .r1 152,
    .ldr .r7 .r1 156,
    .ldr .r8 .r1 160,
    .ldr .r9 .r1 164,
    .ldr .r10 .r1 168,
    .ldr .r11 .r1 172,
    .ldr .lr .r1 176] := rfl

set_option maxHeartbeats 0 in
set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := hp.out_buf (d := 144) (n := 4) (by omega)
  have o1 := hp.out_buf (d := 148) (n := 4) (by omega)
  have o2 := hp.out_buf (d := 152) (n := 4) (by omega)
  have o3 := hp.out_buf (d := 156) (n := 4) (by omega)
  have o4 := hp.out_buf (d := 160) (n := 4) (by omega)
  have o5 := hp.out_buf (d := 164) (n := 4) (by omega)
  have o6 := hp.out_buf (d := 168) (n := 4) (by omega)
  have o7 := hp.out_buf (d := 172) (n := 4) (by omega)
  have o8 := hp.out_buf (d := 176) (n := 4) (by omega)
  have e0 := hp.eaB (show 144 < 256 by omega)
  have e1 := hp.eaB (show 148 < 256 by omega)
  have e2 := hp.eaB (show 152 < 256 by omega)
  have e3 := hp.eaB (show 156 < 256 by omega)
  have e4 := hp.eaB (show 160 < 256 by omega)
  have e5 := hp.eaB (show 164 < 256 by omega)
  have e6 := hp.eaB (show 168 < 256 by omega)
  have e7 := hp.eaB (show 172 < 256 by omega)
  have e8 := hp.eaB (show 176 < 256 by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.store32, o0, o1, o2, o3, o4, o5, o6, o7, o8, e0, e1,
    e2, e3, e4, e5, e6, e7, e8,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  and_intros <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [bufR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 256 → (bufR s₀).Contains (BA s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [saveMem]
  refine ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ ?_)).writeW
    (List.mem_singleton_self _) _ (c _ ?_)).writeW (List.mem_singleton_self _) _ (c _ ?_)).writeW
    (List.mem_singleton_self _) _ (c _ ?_)).writeW (List.mem_singleton_self _) _ (c _ ?_)).writeW
    (List.mem_singleton_self _) _ (c _ ?_)).writeW (List.mem_singleton_self _) _ (c _ ?_)).writeW
    (List.mem_singleton_self _) _ (c _ ?_) |>.writeW (List.mem_singleton_self _) _ (c _ ?_) <;> omega

theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) (hf : Frame [workR (BA s₀)] m m') :
    Saved s₀ m' := by
  have key : ∀ d : Nat, 144 ≤ d → d + 4 ≤ 180 →
      m'.readW (BA s₀ + BitVec.ofNat 64 d) 32 = m.readW (BA s₀ + BitVec.ofNat 64 d) 32 := by
    intro d h1 h2
    have hd := disjoint_sub (BA s₀) (a := d) (la := 4) (b := 0) (lb := 144) (by omega) (by omega)
      (by omega)
    exact hf.readW (r := ⟨BA s₀ + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton, forall_eq] using hd) (by decide)
  simp only [Saved] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨(key 144 (by omega) (by omega)).trans h0, (key 148 (by omega) (by omega)).trans h1,
    (key 152 (by omega) (by omega)).trans h2, (key 156 (by omega) (by omega)).trans h3,
    (key 160 (by omega) (by omega)).trans h4, (key 164 (by omega) (by omega)).trans h5,
    (key 168 (by omega) (by omega)).trans h6, (key 172 (by omega) (by omega)).trans h7,
    (key 176 (by omega) (by omega)).trans h8⟩

set_option maxHeartbeats 0 in
set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : Saved s₀ s.mem)
    (hr1 : s.gpr .r1 = buf s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hs
  have i0 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 144) 4 := by
    rw [hwr]; exact hp.in_buf (d := 144) (n := 4) (by omega) _
  have i1 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 148) 4 := by
    rw [hwr]; exact hp.in_buf (d := 148) (n := 4) (by omega) _
  have i2 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 152) 4 := by
    rw [hwr]; exact hp.in_buf (d := 152) (n := 4) (by omega) _
  have i3 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 156) 4 := by
    rw [hwr]; exact hp.in_buf (d := 156) (n := 4) (by omega) _
  have i4 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 160) 4 := by
    rw [hwr]; exact hp.in_buf (d := 160) (n := 4) (by omega) _
  have i5 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 164) 4 := by
    rw [hwr]; exact hp.in_buf (d := 164) (n := 4) (by omega) _
  have i6 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 168) 4 := by
    rw [hwr]; exact hp.in_buf (d := 168) (n := 4) (by omega) _
  have i7 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 172) 4 := by
    rw [hwr]; exact hp.in_buf (d := 172) (n := 4) (by omega) _
  have i8 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 176) 4 := by
    rw [hwr]; exact hp.in_buf (d := 176) (n := 4) (by omega) _
  have e0 := hp.eaB (show 144 < 256 by omega)
  have e1 := hp.eaB (show 148 < 256 by omega)
  have e2 := hp.eaB (show 152 < 256 by omega)
  have e3 := hp.eaB (show 156 < 256 by omega)
  have e4 := hp.eaB (show 160 < 256 by omega)
  have e5 := hp.eaB (show 164 < 256 by omega)
  have e6 := hp.eaB (show 168 < 256 by omega)
  have e7 := hp.eaB (show 172 < 256 by omega)
  have e8 := hp.eaB (show 176 < 256 by omega)
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.setReg, State.load32, hr1,
    i0, e0, g0, i1, e1, g1, i2, e2, g2, i3, e3, g3, i4, e4, g4, i5, e5, g5, i6, e6, g6, i7, e7, g7, i8, e8, g8, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true})

/-! ## Loading the registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (hj8 : inReg 8 j = true)
    (hk8 : inReg 8 k = true) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → inReg 8 j = true → inReg 8 k = true →
      wreg j = wreg k → j = k := by decide
  exact key j hj k hk hj8 hk8 h

/-- After loading words `< n`. -/
structure LI (s₀ : State) (sL : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → inReg 8 j = true → s.gpr (wreg j) = (V s₀)[j]
  mem : s.mem = sL.mem
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  r1 : s.gpr .r1 = buf s₀

theorem load_step {s₀ s₁ sL : State} (hp : Pre s₀) (hc : CI s₀ s₁ 16 sL) {n : Nat} (hn : n < 16)
    {s : State} (h : LI s₀ sL n s) : WP isa (.block (loadWord n)) s (LI s₀ sL (n + 1)) := by
  by_cases h911 : 9 ≤ n ∧ n ≤ 11
  · simp only [loadWord, h911, and_self, ite_true]
    refine WP.block_nil ⟨fun j hj hjn hin => ?_, h.mem, h.rd, h.wr, h.r1⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · exact h.loaded j hj hjn hin
    · simp [inReg] at hin; omega
  · have hin8 : inReg 8 n = true := by simp [inReg]; omega
    have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (inOff n))) 4 := by
      rw [h.r1, hp.eaB (by simp only [inOff]; omega), h.rd, h.wr, hc.wr]
      exact hp.in_buf (in_lt hn) _
    simp only [loadWord, h911, ite_false]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa,
      exec_ldr (show inOff n < 4096 by simp only [inOff]; omega) hin,
      Option.some.injEq, exists_eq_left']
    rw [h.r1, hp.eaB (by simp only [inOff]; omega), h.mem, hc.inw n hn hn]
    refine ⟨fun j hj hjn hj8 => ?_, h.mem, h.rd, h.wr, ?_⟩
    · simp only [State.setReg]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
      · have e : wreg j ≠ wreg n := fun e => absurd (wreg_inj hj hn hj8 hin8 e) (by omega)
        simp only [e, ite_false]; exact h.loaded j hj hjn hj8
      · simp
    · simp only [State.setReg, show Reg.r1 ≠ wreg n from (wreg_ne_r1 n).symm, ite_false]
      exact h.r1

theorem load_ok {s₀ s₁ : State} (hp : Pre s₀) (h₁ : s₁.gpr = s₀.gpr) {s : State}
    (hc : CI s₀ s₁ 16 s) :
    WP isa (.block load) s fun s' =>
      Holds (BA s₀) 8 (V s₀) s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .r1 = buf s₀ := by
  have h0 : LI s₀ s 0 s :=
    ⟨fun _ _ h => absurd h (by omega), rfl, rfl, rfl, by rw [hc.gpr _ (by decide), h₁]⟩
  have hl : WP isa (.block load) s (LI s₀ s 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₀ s) (fun k s' hk h => load_step hp hc hk h) 16 le_rfl
      s h0
  refine WP.mono hl fun s' h => ⟨fun k hk => ?_, h.mem, h.rd, h.wr, h.r1⟩
  split
  · rename_i hin; exact h.loaded k hk hk hin
  · rename_i hin
    have h911 : 9 ≤ k ∧ k ≤ 11 := by simp [inReg] at hin; omega
    rw [slotAddr, h.mem]; exact hc.slot k hk hk h911


/-! ## Storing the rounds' result -/

/-- The store invariant after `n` words. -/
structure SI (B : Addr) (R : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), j < n → s.mem.readW (B + BitVec.ofNat 64 (outOff j)) 32 = R[j]
  rest : ∀ j (hj : j < 16), n ≤ j → if inReg 8 j then s.gpr (wreg j) = R[j]
    else s.mem.readW (slotAddr B j) 32 = R[j]
  frame : Frame [outR B] sB.mem s.mem
  r1 : s.gpr .r1 = sB.gpr .r1
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem wreg_ne_r0 {j : Nat} (h : 10 ≤ j) (hj : j < 16) : wreg j ≠ .r0 := by
  interval_cases j <;> decide

set_option maxHeartbeats 400000 in
theorem store_step {s₀ : State} (hp : Pre s₀) {R : CState} {sB : State} (hwB : bufR s₀ ∈ sB.wr)
    (hr1B : sB.gpr .r1 = buf s₀) {n : Nat} (hn : n < 16) {s : State} (hs : SI (BA s₀) R sB n s) :
    WP isa (.block (storeWord n)) s (SI (BA s₀) R sB (n + 1)) := by
  have hw : bufR s₀ ∈ s.wr := hs.wr ▸ hwB
  have hr1 : s.gpr .r1 = buf s₀ := hs.r1.trans hr1B
  have eo := hp.eaB (show outOff n < 256 by simp only [outOff]; omega)
  have o : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (outOff n)) 4 :=
    ⟨bufR s₀, hw, contains_off (out_lt hn) (by simp only [outOff]; omega)⟩
  have h4 : outOff n < 4096 := by simp only [outOff]; omega
  have cout : (outR (BA s₀)).Contains (BA s₀ + BitVec.ofNat 64 (outOff n)) (32 / 8) :=
    contains_sub _ (by omega) (by simp [outOff]; omega) (by omega)
  have hr := hs.rest n hn le_rfl
  suffices key : ∀ s', s'.mem = s.mem.writeW (BA s₀ + BitVec.ofNat 64 (outOff n)) R[n] →
      (∀ j (hj : j < 16), n < j → inReg 8 j = true → s'.gpr (wreg j) = s.gpr (wreg j)) →
      s'.gpr .r1 = s.gpr .r1 → s'.rd = s.rd → s'.wr = s.wr → SI (BA s₀) R sB (n + 1) s' by
    apply WP.of_runBlock
    by_cases h : 9 ≤ n ∧ n ≤ 11
    · have hin : inReg 8 n = false := by simp [inReg]; omega
      simp only [hin, Bool.false_eq_true, ite_false, slotAddr] at hr
      have es := hp.eaB (show slotOff n < 256 by simp only [slotOff]; omega)
      have i : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 (slotOff n)) 4 :=
        ⟨bufR s₀, List.mem_append_right _ hw, contains_off (by simp only [slotOff]; omega)
          (by simp only [slotOff]; omega)⟩
      have h5 : slotOff n < 4096 := by simp only [slotOff]; omega
      simp (config := {decide := true}) only [storeWord, h, and_self, ite_true,
        runBlock_cons, runStep_some, runBlock_nil, exec, isa,
        State.setReg, State.load32, State.store32, hr1, es, eo, i, o, h4, h5, ite_false,
        Option.map_some, Option.some.injEq, exists_eq_left']
      refine key _ (by simp only [hr]) (fun j hj hnj _ => ?_) (by simp) rfl rfl
      simp [wreg_ne_r0 (show 10 ≤ j by omega) hj]
    · have hin : inReg 8 n = true := by simp [inReg]; omega
      simp only [hin, ite_true] at hr
      simp (config := {decide := true}) only [storeWord, h, ite_false, runBlock_cons,
        runStep_some, runBlock_nil, exec, isa,
        State.store32, hr1, eo, o, h4, ite_true, hr, Option.some.injEq,
        exists_eq_left']
      exact key _ rfl (fun _ _ _ _ => rfl) rfl rfl rfl
  intro s' hm hg hr1' hrd hwr
  refine ⟨fun j hj hjn => ?_, fun j hj hjn => ?_, ?_, hr1'.trans hs.r1, hrd.trans hs.rd,
    hwr.trans hs.wr⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [readW_writeW_off _ _ _ (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega)]
      exact hs.out j hj hjn
    · exact Mem.readW_writeW_self32 _ _ _
  · have hr' := hs.rest j hj (by omega)
    split
    · rename_i hin; simp only [hin, ite_true] at hr'; rw [hg j hj (by omega) hin]; exact hr'
    · rename_i hin; simp only [hin, Bool.false_eq_true, ite_false] at hr'
      rw [hm, slotAddr, readW_writeW_off _ _ _ (by simp [slotOff]; omega)
        (by simp [outOff]; omega) (by simp [outOff, slotOff]; omega)]
      exact hr'
  · rw [hm]; exact hs.frame.writeW (List.mem_singleton_self _) _ cout

/-! ## Adding the input state -/

/-- The add invariant after `n` words. -/
structure AI (B : Addr) (R v : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (B + BitVec.ofNat 64 (outOff j)) 32 =
    if j < n then R[j] + v[j] else R[j]
  inw : ∀ j (hj : j < 16), s.mem.readW (B + BitVec.ofNat 64 (inOff j)) 32 = v[j]
  frame : Frame [outR B] sB.mem s.mem
  r1 : s.gpr .r1 = sB.gpr .r1
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

set_option maxHeartbeats 400000 in
theorem add_step {s₀ : State} (hp : Pre s₀) {R v : CState} {sB : State} (hwB : bufR s₀ ∈ sB.wr)
    (hr1B : sB.gpr .r1 = buf s₀) {n : Nat} (hn : n < 16) {s : State}
    (hs : AI (BA s₀) R v sB n s) : WP isa (.block (addWord n)) s (AI (BA s₀) R v sB (n + 1)) := by
  have hw : bufR s₀ ∈ s.wr := hs.wr ▸ hwB
  have hr1 : s.gpr .r1 = buf s₀ := hs.r1.trans hr1B
  have eo := hp.eaB (show outOff n < 256 by simp only [outOff]; omega)
  have ei := hp.eaB (show inOff n < 256 by simp only [inOff]; omega)
  have o : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (outOff n)) 4 :=
    ⟨bufR s₀, hw, contains_off (out_lt hn) (by simp only [outOff]; omega)⟩
  have io : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 (outOff n)) 4 :=
    ⟨bufR s₀, List.mem_append_right _ hw, contains_off (out_lt hn) (by simp only [outOff]; omega)⟩
  have ii : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 (inOff n)) 4 :=
    ⟨bufR s₀, List.mem_append_right _ hw, contains_off (in_lt hn) (by simp only [inOff]; omega)⟩
  have h4 : outOff n < 4096 := by simp only [outOff]; omega
  have h5 : inOff n < 4096 := by simp only [inOff]; omega
  have cout : (outR (BA s₀)).Contains (BA s₀ + BitVec.ofNat 64 (outOff n)) (32 / 8) :=
    contains_sub _ (by omega) (by simp [outOff]; omega) (by omega)
  have ho := hs.out n hn
  simp only [lt_irrefl, ite_false] at ho
  have hi := hs.inw n hn
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addWord, runBlock_cons,
    runStep_some, runBlock_nil, exec, Op2.eval, isa, State.setReg,
    State.load32, State.store32, hr1, eo, ei, o, io, ii, h4, h5, ho, hi, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun j hj => ?_, hs.frame.writeW (List.mem_singleton_self _) _ cout,
    by simpa using hs.r1, hs.rd, hs.wr⟩
  · by_cases hjn : j = n
    · subst hjn; simp [Mem.readW_writeW_self32]
    · rw [readW_writeW_off _ _ _ (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega), hs.out j hj]
      split <;> split <;> first | rfl | omega
  · rw [readW_writeW_off _ _ _ (by simp [inOff]; omega) (by simp [outOff]; omega)
      (by simp [inOff, outOff]; omega)]
    exact hs.inw j hj

/-! ## The whole function -/

theorem finish_split : finish ++ restore =
    ((List.range 16).flatMap storeWord ++ (List.range 16).flatMap addWord) ++ restore := by
  unfold finish; rfl

theorem read_in {B : Addr} {m m' : Mem} {r : Region}
    (hf : Frame [r] m m') (hd : ∀ j < 16, (⟨B + BitVec.ofNat 64 (inOff j), 4⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < 16) :
    m'.readW (B + BitVec.ofNat 64 (inOff j)) 32 = m.readW (B + BitVec.ofNat 64 (inOff j)) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using hd j hj) (by decide)

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (outOff j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

set_option maxHeartbeats 400000 in
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.blockArm.post s₀ s' := by
  have hw₀ := hp.hw
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [bufR s₀] s₀.mem s₁.mem := hm₁ ▸ saveMem_frame s₀
  have hc₀ : CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, Frame.refl _ _, fun _ _ h => absurd h (by omega),
      fun _ _ h => absurd h (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (CI s₀ s₁)
    (fun k s hk hc => copy_step hp hg₁ hf₁ hk hc) 16 le_rfl s₁ hc₀) fun s hc => ?_
  refine WP.mono (load_ok hp hg₁ hc) fun s₂ ⟨hh₂, hm₂, hrd₂, hwr₂, hr1₂⟩ => ?_
  have hw₂ : bufR s₀ ∈ s₂.wr := by rw [hwr₂, hc.wr]; exact hw₀
  refine WP.seq (WP.mono (rounds_ok hh₂ (fun off ho => by rw [hr1₂]; exact hp.eaB ho) hw₂ 10)
    fun s₃ hR => ?_)
  have hw₃ : bufR s₀ ∈ s₃.wr := by rw [hR.wr]; exact hw₂
  have hr1₃ : s₃.gpr .r1 = buf s₀ := hR.r1.trans hr1₂
  rw [finish_split, WP.block_append_iff, WP.block_append_iff]
  have hs₀ : SI (BA s₀) (Rs s₀) s₃ 0 s₃ :=
    ⟨fun _ _ h => absurd h (by omega), fun j hj _ => hR.holds j hj, Frame.refl _ _, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (SI (BA s₀) (Rs s₀) s₃)
    (fun k s hk hs => store_step hp hw₃ hr1₃ hk hs) 16 le_rfl s₃ hs₀) fun s₄ hS => ?_
  have hw₄ : bufR s₀ ∈ s₄.wr := by rw [hS.wr]; exact hw₃
  have hr1₄ : s₄.gpr .r1 = buf s₀ := hS.r1.trans hr1₃
  have hinw : ∀ j (hj : j < 16),
      s₄.mem.readW (BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = (V s₀)[j] := by
    intro j hj
    rw [read_in hS.frame (fun j hj => disjoint_sub _ (by simp only [inOff]; omega)
        (by simp only [inOff]; omega) (by omega)) hj,
      read_in hR.frame (fun j hj => disjoint_sub _ (by simp only [inOff]; omega)
        (by simp only [inOff]; omega) (by omega)) hj, hm₂]
    exact hc.inw j hj hj
  have ha₀ : AI (BA s₀) (Rs s₀) (V s₀) s₄ 0 s₄ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hS.out j hj hj, hinw,
      Frame.refl _ _, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (AI (BA s₀) (Rs s₀) (V s₀) s₄)
    (fun k s hk ha => add_step hp hw₄ hr1₄ hk ha) 16 le_rfl s₄ ha₀) fun s₅ hA => ?_
  have hwork : Frame [workR (BA s₀)] s₁.mem s₅.mem := by
    refine (frame_work (a := 64) (len := 80) (by omega) hc.frame).trans ?_
    rw [← hm₂]
    refine (frame_work (a := 128) (len := 16) (by omega) hR.frame).trans ?_
    exact (frame_work (a := 0) (len := 64) (by omega) hS.frame).trans
      (frame_work (a := 0) (len := 64) (by omega) hA.frame)
  have hsaved : Saved s₀ s₅.mem := saved_frame (hm₁ ▸ saveMem_saved s₀) hwork
  refine WP.mono (restore_ok hp hsaved (hA.r1.trans hr1₄) (by rw [hA.wr, hS.wr, hR.wr, hwr₂, hc.wr]))
    fun s' ⟨hm', hg'⟩ => ⟨hg', ?_⟩
  show stateAt s'.mem (BA s₀) = Spec.ChaCha20.block (V s₀)
  rw [hm']
  exact block_post fun j hj => by simpa [hj] using hA.out j hj

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

set_option maxRecDepth 100000 in
theorem block_verified :
    Verified Arm.target Impl.ChaCha20.Arm.block Proof.ChaCha20.blockArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, by decide, by decide⟩
    intro a h₁ h₂
    simp only [Region.Contains, satState, State.addr] at h₁ h₂
    bv_omega

end VG.Proof.ChaCha20.Arm
