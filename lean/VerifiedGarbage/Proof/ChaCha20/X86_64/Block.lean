import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.ChaCha20.X86_64.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import Mathlib.Tactic.IntervalCases

/-!
# ChaCha20 block function on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The code may read `state` (64 bytes) and read and write `buf` (256 bytes; its
first 64 bytes hold the result on exit, and the rest is scratch space whose
contents on exit are unspecified). `buf` may not overlap `state` or the
return address on the stack. The pointers are public; the state (key,
counter and nonce) is secret. -/
def blockX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let buf : Region := ⟨s.gpr .rsi, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧ ret.Disjoint buf
  post s s' := stateAt s'.mem (s.gpr .rsi) = block (stateAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-- An address `buf + d` as the code computes it. -/
abbrev bufAt (buf : Addr) (d : Nat) : Addr := buf + BitVec.ofInt 64 (d : Int)

theorem in_lt {k : Nat} (hk : k < 16) : inOff k + 4 ≤ 256 := by simp only [inOff]; omega
theorem out_lt {k : Nat} (hk : k < 16) : outOff k + 4 ≤ 256 := by simp only [outOff]; omega

/-! ## Copying the state -/

theorem copyWord_ok {k : Nat} (hk : k < 16) {s : State} {st buf : Addr} (hrdi : s.gpr .rdi = st)
    (hrsi : s.gpr .rsi = buf) (hin : InRegions (s.rd ++ s.wr) (bufAt st (4 * k)) 4)
    (hw : bufR buf ∈ s.wr) :
    WP isa (.block (copyWord k)) s fun s' =>
      s'.mem = (if k = 10 ∨ k = 11 then
          (s.mem.writeW (bufAt buf (inOff k)) (s.mem.readW (bufAt st (4 * k)) 32)).writeW
            (bufAt buf (slotOff k)) (s.mem.readW (bufAt st (4 * k)) 32)
        else s.mem.writeW (bufAt buf (inOff k)) (s.mem.readW (bufAt st (4 * k)) 32)) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o₁ := out_buf hw (d := inOff k) (n := 4) (in_lt hk)
  apply WP.of_runBlock
  by_cases h : k = 10 ∨ k = 11
  · have o₂ := out_buf hw (d := slotOff k) (n := 4) (by simp only [slotOff]; omega)
    simp (config := {decide := true}) only [copyWord, h, ite_true, ite_false, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
          exec, readSrc32, isa, ea_at, State.load32, State.store32,
      State.setReg32, State.setReg, hrdi, hin, hrsi, o₁, o₂, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · simp (config := {decide := true}) only [copyWord, h, ite_true, ite_false, List.append_nil,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
          isa, ea_at, State.load32, State.store32, State.setReg32,
      State.setReg, hrdi, hin, hrsi, o₁, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-! ## Offsets -/

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨bufAt p a, len⟩ : Region).Contains (bufAt p d) n := by
  simp only [Region.Contains, bufAt, ofInt_natCast]
  rw [show p + BitVec.ofNat 64 d - (p + BitVec.ofNat 64 a) = BitVec.ofNat 64 (d - a) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

/-- Two sub-ranges of `buf` that do not overlap. -/
theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨bufAt p a, la⟩ : Region).Disjoint ⟨bufAt p b, lb⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains, bufAt, ofInt_natCast] at h₁ h₂
  bv_omega

/-- A sub-range of `buf` is inside `buf`. -/
theorem sub_buf (p : Addr) {a len : Nat} (h : a + len ≤ 256) :
    Region.Sub ⟨bufAt p a, len⟩ (bufR p) := by
  intro x hx
  simp only [Region.Contains, bufAt, ofInt_natCast] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-- The output area of `buf`. -/
abbrev outR (p : Addr) : Region := ⟨bufAt p 0, 64⟩
/-- Everything in `buf` but the saved registers: output, input copy and slots. -/
abbrev workR (p : Addr) : Region := ⟨bufAt p 0, 144⟩

theorem sub_work (p : Addr) {a len : Nat} (h : a + len ≤ 144) :
    Region.Sub ⟨bufAt p a, len⟩ (workR p) := by
  intro x hx
  simp only [Region.Contains, bufAt, ofInt_natCast] at *
  have : (x - (p + BitVec.ofNat 64 0)).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - (p + BitVec.ofNat 64 0) = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by
      bv_omega, BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

theorem frame_work {p : Addr} {a len : Nat} (h : a + len ≤ 144) {m m' : Mem}
    (hf : Frame [⟨bufAt p a, len⟩] m m') : Frame [workR p] m m' :=
  hf.sub fun r hr => ⟨workR p, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_work p h⟩

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev buf : Addr := s₀.gpr .rsi
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (st s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR (buf s₀)]
  buf_st : (bufR (buf s₀)).Disjoint (stR s₀)
  ret_buf : (retR s₀).Disjoint (bufR (buf s₀))

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem Pre.hw {s₀ : State} (hp : Pre s₀) : bufR (buf s₀) ∈ s₀.wr := by simp [hp.wr]

theorem Pre.in_st {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (bufAt (st s₀) (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by omega) (by omega)⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bufAt (st s₀) (4 * k)) 32 := by
  simp only [V, stateAt, Vector.getElem_ofFn, bufAt, ofInt_natCast]

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [bufR (buf s₀)] s₀.mem m)
    {k : Nat} (hk : k < 16) : m.readW (bufAt (st s₀) (4 * k)) 32 = (V s₀)[k] := by
  rw [V_get _ hk]
  exact hf.readW (r := stR s₀) (contains_off (by omega) (by omega))
    (by simpa using hp.buf_st.symm) (by decide)

/-! ## Phase 2: copying the state -/

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue's stores. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨bufAt (buf s₀) 64, 80⟩] s₁.mem s.mem
  inw : ∀ j (hj : j < 16), j < n → s.mem.readW (bufAt (buf s₀) (inOff j)) 32 = (V s₀)[j]
  slot : ∀ j (hj : j < 16), j < n → (j = 10 ∨ j = 11) →
    s.mem.readW (bufAt (buf s₀) (slotOff j)) 32 = (V s₀)[j]

theorem copy_step {s₀ s₁ : State} (hp : Pre s₀) (h₁ : s₁.gpr = s₀.gpr)
    (hf₁ : Frame [bufR (buf s₀)] s₀.mem s₁.mem) {n : Nat} (hn : n < 16)
    {s : State} (hc : CI s₀ s₁ n s) : WP isa (.block (copyWord n)) s (CI s₀ s₁ (n + 1)) := by
  have hrdi : s.gpr .rdi = st s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hrsi : s.gpr .rsi = buf s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hfs : Frame [bufR (buf s₀)] s₀.mem s.mem :=
    hf₁.trans (hc.frame.sub fun r hr => ⟨bufR (buf s₀), List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_buf _ (by omega)⟩)
  refine WP.mono (copyWord_ok hn hrdi hrsi (by rw [hc.rd, hc.wr]; exact hp.in_st hn _)
    (by rw [hc.wr]; exact hp.hw)) fun s' ⟨hm, hg, hrd, hwr⟩ => ?_
  have hx : s.mem.readW (bufAt (st s₀) (4 * n)) 32 = (V s₀)[n] := read_st hp hfs hn
  have cin : (⟨bufAt (buf s₀) 64, 80⟩ : Region).Contains (bufAt (buf s₀) (inOff n)) (32 / 8) :=
    contains_sub _ (by simp [inOff]) (by simp [inOff]; omega) (by omega)
  refine ⟨fun r hr => (hg r hr).trans (hc.gpr r hr), hrd.trans hc.rd, hwr.trans hc.wr, ?_, ?_, ?_⟩
  · rw [hm]
    split
    · exact (hc.frame.writeW (List.mem_singleton_self _) _ cin).writeW (List.mem_singleton_self _) _
        (contains_sub _ (by simp [slotOff]; omega) (by simp [slotOff]; omega) (by omega))
    · exact hc.frame.writeW (List.mem_singleton_self _) _ cin
  · intro j hj hjn
    rw [hm]
    have e1 : ∀ m : Mem, (m.writeW (bufAt (buf s₀) (slotOff n)) ((V s₀)[n])).readW
        (bufAt (buf s₀) (inOff j)) 32 = m.readW (bufAt (buf s₀) (inOff j)) 32 := fun m =>
      readW_writeW_off m _ _ (by omega) (by simp [inOff]; omega) (by simp [slotOff]; omega)
        (by simp [inOff, slotOff]; omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : (s.mem.writeW (bufAt (buf s₀) (inOff n)) ((V s₀)[n])).readW
          (bufAt (buf s₀) (inOff j)) 32 = s.mem.readW (bufAt (buf s₀) (inOff j)) 32 :=
        readW_writeW_off _ _ _ (by omega) (by simp [inOff]; omega) (by simp [inOff]; omega)
          (by simp [inOff]; omega)
      rw [hx]; split <;> simp only [e1, e2, hc.inw j hj hjn]
    · rw [hx]; split <;> simp only [e1, Mem.readW_writeW_self32]
  · intro j hj hjn h1011
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : ∀ m : Mem, ∀ d, d = inOff n ∨ d = slotOff n → (m.writeW (bufAt (buf s₀) d)
          ((V s₀)[n])).readW (bufAt (buf s₀) (slotOff j)) 32 = m.readW (bufAt (buf s₀) (slotOff j)) 32 := by
        rintro m d (rfl | rfl)
        · exact readW_writeW_off _ _ _ (by omega) (by simp [slotOff]; omega) (by simp [inOff]; omega)
            (by simp [inOff, slotOff]; omega)
        · exact readW_writeW_off _ _ _ (by omega) (by simp [slotOff]; omega) (by simp [slotOff]; omega)
            (by simp [slotOff]; omega)
      rw [hx]; split <;> simp only [e2 _ _ (.inl rfl), e2 _ _ (.inr rfl), hc.slot j hj hjn h1011]
    · simp only [hx, h1011, ite_true, Mem.readW_writeW_self32]

/-! ## Phase 5: storing the rounds' result -/

/-- The store invariant after `n` words: the result `R` is in the output for
words `< n`, and still in the registers and slots for the others. -/
structure SI (p : Addr) (R : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), j < n → s.mem.readW (bufAt p (outOff j)) 32 = R[j]
  rest : ∀ j (hj : j < 16), n ≤ j → if inReg false j then s.gpr (wreg j) = R[j].setWidth 64
    else s.mem.readW (slotAddr p j) 32 = R[j]
  frame : Frame [outR p] sB.mem s.mem
  rsi : s.gpr .rsi = p
  rsp : s.gpr .rsp = sB.gpr .rsp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem wreg_ne_rax {j : Nat} (h : 11 ≤ j) (hj : j < 16) : wreg j ≠ .rax := by
  interval_cases j <;> decide

theorem store_step {p : Addr} {R : CState} {sB : State} (hw : bufR p ∈ sB.wr) {n : Nat} (hn : n < 16)
    {s : State} (hs : SI p R sB n s) : WP isa (.block (storeWord n)) s (SI p R sB (n + 1)) := by
  have hw' : bufR p ∈ s.wr := hs.wr ▸ hw
  have o := out_buf hw' (d := outOff n) (n := 4) (out_lt hn)
  have cout : (outR p).Contains (bufAt p (outOff n)) (32 / 8) :=
    contains_sub _ (by omega) (by simp [outOff]; omega) (by omega)
  have hr := hs.rest n hn (Nat.le_refl _)
  have hrsi := hs.rsi
  /- The new memory is the old one with `R[n]` written to output word `n`. -/
  suffices key : ∀ s', s'.mem = s.mem.writeW (bufAt p (outOff n)) R[n] →
      (∀ j (hj : j < 16), n < j → inReg false j = true → s'.gpr (wreg j) = s.gpr (wreg j)) →
      s'.gpr .rsi = s.gpr .rsi → s'.gpr .rsp = s.gpr .rsp → s'.rd = s.rd → s'.wr = s.wr →
      SI p R sB (n + 1) s' by
    apply WP.of_runBlock
    by_cases h : n = 10 ∨ n = 11
    · have hin : inReg false n = false := by rcases h with rfl | rfl <;> rfl
      simp only [hin, Bool.false_eq_true, ite_false] at hr
      have i := in_buf (rs := s.rd) hw' (d := slotOff n) (n := 4) (by simp only [slotOff]; omega)
      simp (config := {decide := true}) only [storeWord, h, ite_true, runBlock_cons,
        runStep_some, runBlock_nil, exec, readSrc32,
        isa, ea_at, State.load32, State.store32, State.setReg32, State.setReg, hrsi, i, o,
        ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
        Option.map_some, Option.some.injEq, exists_eq_left']
      simp only [slotAddr] at hr
      refine key _ (by simp only [hr]) (fun j hj hnj _ => ?_) (by simp) (by simp) rfl rfl
      simp [wreg_ne_rax (show 11 ≤ j by omega) hj]
    · have hin : inReg false n = true := by
        simp only [inReg]; split <;> simp_all
      simp only [hin, ite_true] at hr
      simp (config := {decide := true}) only [storeWord, h, ite_false, runBlock_cons,
        runStep_some, runBlock_nil, exec, isa, ea_at,
        State.store32, hrsi, o, ite_true, hr, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
        Option.some.injEq, exists_eq_left']
      exact key _ rfl (fun _ _ _ _ => rfl) rfl rfl rfl rfl
  intro s' hm hg hrsi' hrsp' hrd hwr
  refine ⟨fun j hj hjn => ?_, fun j hj hjn => ?_, ?_, hrsi'.trans hs.rsi, hrsp'.trans hs.rsp,
    hrd.trans hs.rd, hwr.trans hs.wr⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [readW_writeW_off _ _ _ (by omega) (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega)]
      exact hs.out j hj hjn
    · exact Mem.readW_writeW_self32 _ _ _
  · have hr' := hs.rest j hj (by omega)
    split
    · rename_i hin; simp only [hin, ite_true] at hr'; rw [hg j hj (by omega) hin]; exact hr'
    · rename_i hin; simp only [hin] at hr'
      rw [hm, slotAddr, readW_writeW_off _ _ _ (by omega) (by simp [slotOff]; omega)
        (by simp [outOff]; omega) (by simp [outOff, slotOff]; omega)]
      exact hr'
  · rw [hm]; exact hs.frame.writeW (List.mem_singleton_self _) _ cout

/-! ## Phase 6: adding the input state -/

/-- The add invariant after `n` words. -/
structure AI (p : Addr) (R v : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bufAt p (outOff j)) 32 = if j < n then R[j] + v[j] else R[j]
  inw : ∀ j (hj : j < 16), s.mem.readW (bufAt p (inOff j)) 32 = v[j]
  frame : Frame [outR p] sB.mem s.mem
  rsi : s.gpr .rsi = p
  rsp : s.gpr .rsp = sB.gpr .rsp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem add_step {p : Addr} {R v : CState} {sB : State} (hw : bufR p ∈ sB.wr) {n : Nat} (hn : n < 16)
    {s : State} (hs : AI p R v sB n s) : WP isa (.block (addWord n)) s (AI p R v sB (n + 1)) := by
  have hw' : bufR p ∈ s.wr := hs.wr ▸ hw
  have o := out_buf hw' (d := outOff n) (n := 4) (out_lt hn)
  have io := in_buf (rs := s.rd) hw' (d := outOff n) (n := 4) (out_lt hn)
  have ii := in_buf (rs := s.rd) hw' (d := inOff n) (n := 4) (in_lt hn)
  have cout : (outR p).Contains (bufAt p (outOff n)) (32 / 8) :=
    contains_sub _ (by omega) (by simp [outOff]; omega) (by omega)
  have ho := hs.out n hn
  simp only [Nat.lt_irrefl, ite_false] at ho
  have hi := hs.inw n hn
  have hrsi := hs.rsi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addWord, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu32, readSrc32, isa, ea_at,
    State.load32, State.store32, State.setReg32, State.setReg, arithFlags, State.setFlags, hrsi, o,
    io, ii, ho, hi, ite_true, ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun j hj => ?_, hs.frame.writeW (List.mem_singleton_self _) _ cout,
    by simpa using hs.rsi, by simpa using hs.rsp, hs.rd, hs.wr⟩
  · by_cases hjn : j = n
    · subst hjn; simp [bufAt, Mem.readW_writeW_self32]
    · rw [readW_writeW_off _ _ _ (by omega) (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega), hs.out j hj]
      split <;> split <;> first | rfl | omega
  · rw [readW_writeW_off _ _ _ (by omega) (by simp [inOff]; omega) (by simp [outOff]; omega)
      (by simp [inOff, outOff]; omega)]
    exact hs.inw j hj

/-! ## Phase 1: saving the callee-saved registers -/

theorem readW64_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (bufAt p e) v).readW (bufAt p d) 64 = m.readW (bufAt p d) 64 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (bufAt (buf s₀) 144) (s₀.gpr .rbx)).writeW (bufAt (buf s₀) 152)
    (s₀.gpr .rbp)).writeW (bufAt (buf s₀) 160) (s₀.gpr .r12)).writeW (bufAt (buf s₀) 168)
    (s₀.gpr .r13)).writeW (bufAt (buf s₀) 176) (s₀.gpr .r14)).writeW (bufAt (buf s₀) 184)
    (s₀.gpr .r15)

/-- The callee-saved registers are saved in `buf`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (bufAt (buf s₀) 144) 64 = s₀.gpr .rbx ∧ m.readW (bufAt (buf s₀) 152) 64 = s₀.gpr .rbp ∧
  m.readW (bufAt (buf s₀) 160) 64 = s₀.gpr .r12 ∧ m.readW (bufAt (buf s₀) 168) 64 = s₀.gpr .r13 ∧
  m.readW (bufAt (buf s₀) 176) 64 = s₀.gpr .r14 ∧ m.readW (bufAt (buf s₀) 184) 64 = s₀.gpr .r15

theorem save_eq : save = [
    .store (at_ .rsi 144) .rbx, .store (at_ .rsi 152) .rbp, .store (at_ .rsi 160) .r12,
    .store (at_ .rsi 168) .r13, .store (at_ .rsi 176) .r14, .store (at_ .rsi 184) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rsi 144)), .mov .rbp (.mem (at_ .rsi 152)), .mov .r12 (.mem (at_ .rsi 160)),
    .mov .r13 (.mem (at_ .rsi 168)), .mov .r14 (.mem (at_ .rsi 176)), .mov .r15 (.mem (at_ .rsi 184))] :=
  rfl

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := out_buf hp.hw (d := 144) (n := 8) (by omega)
  have o1 := out_buf hp.hw (d := 152) (n := 8) (by omega)
  have o2 := out_buf hp.hw (d := 160) (n := 8) (by omega)
  have o3 := out_buf hp.hw (d := 168) (n := 8) (by omega)
  have o4 := out_buf hp.hw (d := 176) (n := 8) (by omega)
  have o5 := out_buf hp.hw (d := 184) (n := 8) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, ea_at, State.store64, o0, o1, o2,
    o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [bufR (buf s₀)] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 256 → (bufR (buf s₀)).Contains (bufAt (buf s₀) d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 144 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 152 (by omega))).writeW (List.mem_singleton_self _) _
    (c 160 (by omega))).writeW (List.mem_singleton_self _) _ (c 168 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 176 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 184 (by omega))

theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) (hf : Frame [workR (buf s₀)] m m') :
    Saved s₀ m' := by
  have key : ∀ d : Nat, 144 ≤ d → d + 8 ≤ 192 →
      m'.readW (bufAt (buf s₀) d) 64 = m.readW (bufAt (buf s₀) d) 64 := by
    intro d h1 h2
    have hd := disjoint_sub (buf s₀) (a := d) (la := 8) (b := 0) (lb := 144) (by omega) (by omega)
      (by omega)
    exact hf.readW (r := ⟨bufAt (buf s₀) d, 8⟩) (Region.contains_self _ _) (by simpa using hd)
      (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 144 (by omega) (by omega)).trans h1, (key 152 (by omega) (by omega)).trans h2,
    (key 160 (by omega) (by omega)).trans h3, (key 168 (by omega) (by omega)).trans h4,
    (key 176 (by omega) (by omega)).trans h5, (key 184 (by omega) (by omega)).trans h6⟩

/-! ## Phase 3: loading the registers -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rsi (inOff 0))), .mov32 .rbx (.mem (at_ .rsi (inOff 1))),
    .mov32 .rcx (.mem (at_ .rsi (inOff 2))), .mov32 .rdx (.mem (at_ .rsi (inOff 3))),
    .mov32 .rdi (.mem (at_ .rsi (inOff 4))), .mov32 .rbp (.mem (at_ .rsi (inOff 5))),
    .mov32 .r8 (.mem (at_ .rsi (inOff 6))), .mov32 .r9 (.mem (at_ .rsi (inOff 7))),
    .mov32 .r14 (.mem (at_ .rsi (inOff 8))), .mov32 .r15 (.mem (at_ .rsi (inOff 9))),
    .mov32 .r10 (.mem (at_ .rsi (inOff 12))), .mov32 .r11 (.mem (at_ .rsi (inOff 13))),
    .mov32 .r12 (.mem (at_ .rsi (inOff 14))), .mov32 .r13 (.mem (at_ .rsi (inOff 15)))] := rfl

set_option simprocs false in
theorem load_ok {s₀ s₁ : State} (hp : Pre s₀) (h₁ : s₁.gpr = s₀.gpr) {s : State}
    (hc : CI s₀ s₁ 16 s) :
    WP isa (.block load) s fun s' =>
      Holds (buf s₀) false (V s₀) s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rsi = buf s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp := by
  have hrsi : s.gpr .rsi = buf s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hrsp : s.gpr .rsp = s₀.gpr .rsp := by rw [hc.gpr _ (by decide), h₁]
  have hw : bufR (buf s₀) ∈ s.wr := by rw [hc.wr]; exact hp.hw
  have hin : ∀ k, k < 16 → InRegions (s.rd ++ s.wr) (buf s₀ + BitVec.ofInt 64 ((inOff k : Nat) : Int)) 4 :=
    fun k hk => in_buf hw (in_lt hk)
  have v : ∀ k (hk : k < 16), s.mem.readW (buf s₀ + BitVec.ofInt 64 ((inOff k : Nat) : Int)) 32 =
      (V s₀)[k] := fun k hk => hc.inw k hk hk
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at, State.load32,
    State.setReg32, State.setReg, hrsi, hin _ (show 0 < 16 by decide), hin _ (show 1 < 16 by decide),
    hin _ (show 2 < 16 by decide), hin _ (show 3 < 16 by decide), hin _ (show 4 < 16 by decide),
    hin _ (show 5 < 16 by decide), hin _ (show 6 < 16 by decide), hin _ (show 7 < 16 by decide),
    hin _ (show 8 < 16 by decide), hin _ (show 9 < 16 by decide), hin _ (show 12 < 16 by decide),
    hin _ (show 13 < 16 by decide), hin _ (show 14 < 16 by decide), hin _ (show 15 < 16 by decide),
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, trivial, trivial, trivial, by simp (config := {decide := true}),
    by simp (config := {decide := true}) [hrsp]⟩
  have v' : ∀ k (hk : k < 16), s.mem.readW (buf s₀ + BitVec.ofNat 64 (inOff k)) 32 = (V s₀)[k] :=
    fun k hk => by rw [← ofInt_natCast]; exact v k hk
  have sl : ∀ k (hk : k < 16), (k = 10 ∨ k = 11) →
      s.mem.readW (buf s₀ + BitVec.ofNat 64 (slotOff k)) 32 = (V s₀)[k] :=
    fun k hk h => by rw [← ofInt_natCast]; exact hc.slot k hk hk h
  interval_cases k <;>
  simp (config := {decide := true}) only [wreg, slotAddr, ite_true, ite_false, ofInt_natCast] <;>
  first
    | rw [v' _ (by decide)]
    | exact sl _ (by decide) (by decide)

/-! ## Phase 7: restoring the callee-saved registers -/

set_option simprocs false in
theorem restore_ok {s₀ : State} {s : State} (hs : Saved s₀ s.mem) (hrsi : s.gpr .rsi = buf s₀)
    (hw : bufR (buf s₀) ∈ s.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rsp = s.gpr .rsp ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r := by
  have i0 := in_buf (rs := s.rd) hw (d := 144) (n := 8) (by omega)
  have i1 := in_buf (rs := s.rd) hw (d := 152) (n := 8) (by omega)
  have i2 := in_buf (rs := s.rd) hw (d := 160) (n := 8) (by omega)
  have i3 := in_buf (rs := s.rd) hw (d := 168) (n := 8) (by omega)
  have i4 := in_buf (rs := s.rd) hw (d := 176) (n := 8) (by omega)
  have i5 := in_buf (rs := s.rd) hw (d := 184) (n := 8) (by omega)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hs
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hrsi, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true})

/-! ## The whole function -/

/-- The result of the rounds. -/
abbrev Rs (s₀ : State) : CState := Nat.repeat innerBlock 10 (V s₀)

theorem finish_split : finish ++ restore =
    ((List.range 16).flatMap storeWord ++ (List.range 16).flatMap addWord) ++ restore := by
  unfold finish; rfl

theorem read_in {p : Addr} {m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ j < 16, (⟨bufAt p (inOff j), 4⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < 16) :
    m'.readW (bufAt p (inOff j)) 32 = m.readW (bufAt p (inOff j)) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => hd r hr j hj) (by decide)

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (bufAt p (outOff j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  have := h j hj
  simp only [bufAt, outOff, ofInt_natCast] at this
  exact this

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' => gprPreserved s₀ s' ∧ Proof.ChaCha20.blockX86_64.post s₀ s' := by
  have hw₀ := hp.hw
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [bufR (buf s₀)] s₀.mem s₁.mem := hm₁ ▸ saveMem_frame s₀
  have hc₀ : CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, Frame.refl _ _, fun _ _ h => absurd h (by omega),
      fun _ _ h => absurd h (by omega)⟩
  refine WP.mono (wp_range_flatMap (CI s₀ s₁) (fun k s hk hc => copy_step hp hg₁ hf₁ hk hc)
    16 (Nat.le_refl _) s₁ hc₀) fun s hc => ?_
  refine WP.mono (load_ok hp hg₁ hc) fun s₂ ⟨hh₂, hm₂, hrd₂, hwr₂, hrsi₂, hrsp₂⟩ => ?_
  have hw₂ : bufR (buf s₀) ∈ s₂.wr := by rw [hwr₂, hc.wr]; exact hw₀
  refine WP.seq (WP.mono (rounds_ok hh₂ hrsi₂ hw₂ 10) fun s₃ hR => ?_)
  have hw₃ : bufR (buf s₀) ∈ s₃.wr := by rw [hR.wr]; exact hw₂
  rw [finish_split, WP.block_append_iff, WP.block_append_iff]
  have hs₀ : SI (buf s₀) (Rs s₀) s₃ 0 s₃ :=
    ⟨fun _ _ h => absurd h (by omega), fun j hj _ => hR.holds j hj, Frame.refl _ _,
      hR.rsi.trans hrsi₂, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (SI (buf s₀) (Rs s₀) s₃)
    (fun k s hk hs => store_step hw₃ hk hs) 16 (Nat.le_refl _) s₃ hs₀) fun s₄ hS => ?_
  have hw₄ : bufR (buf s₀) ∈ s₄.wr := by rw [hS.wr]; exact hw₃
  have hinw : ∀ j (hj : j < 16), s₄.mem.readW (bufAt (buf s₀) (inOff j)) 32 = (V s₀)[j] := by
    intro j hj
    rw [read_in hS.frame (by
        intro r hr j hj
        simp only [List.mem_singleton] at hr; subst hr
        exact disjoint_sub _ (by simp only [inOff]; omega) (by simp only [inOff]; omega) (by omega)) hj,
      read_in hR.frame (by
        intro r hr j hj
        simp only [List.mem_singleton] at hr; subst hr
        exact disjoint_sub _ (by simp only [inOff]; omega) (by simp only [inOff]; omega) (by omega)) hj,
      hm₂]
    exact hc.inw j hj hj
  have ha₀ : AI (buf s₀) (Rs s₀) (V s₀) s₄ 0 s₄ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hS.out j hj hj, hinw,
      Frame.refl _ _, hS.rsi, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (AI (buf s₀) (Rs s₀) (V s₀) s₄)
    (fun k s hk ha => add_step hw₄ hk ha) 16 (Nat.le_refl _) s₄ ha₀) fun s₅ hA => ?_
  have hw₅ : bufR (buf s₀) ∈ s₅.wr := by rw [hA.wr]; exact hw₄
  -- Everything since the prologue's stores wrote only `[buf, buf + 144)`.
  have hwork : Frame [workR (buf s₀)] s₁.mem s₅.mem := by
    refine (frame_work (a := 64) (len := 80) (by omega) hc.frame).trans ?_
    rw [← hm₂]
    refine (frame_work (a := 128) (len := 16) (by omega) hR.frame).trans ?_
    exact (frame_work (a := 0) (len := 64) (by omega) hS.frame).trans
      (frame_work (a := 0) (len := 64) (by omega) hA.frame)
  have hsaved : Saved s₀ s₅.mem := saved_frame (hm₁ ▸ saveMem_saved s₀) hwork
  have hbuf : Frame [bufR (buf s₀)] s₀.mem s₅.mem :=
    hf₁.trans (hwork.sub fun r hr => ⟨bufR (buf s₀), List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_buf _ (by omega)⟩)
  refine WP.mono (restore_ok hsaved hA.rsi hw₅) fun s' ⟨hm', hrsp', hg'⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · rw [hrsp', hA.rsp, hS.rsp, hR.rsp, hrsp₂]
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
  · rw [hm']
    exact hbuf.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_buf)
      (by decide)
  · show stateAt s'.mem (buf s₀) = Spec.ChaCha20.block (V s₀)
    rw [hm']
    exact block_post fun j hj => by simpa [hj] using hA.out j hj

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockX86_64.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem block_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.block (Spec.ChaCha20.blockContract X86_64.abi) := by
  refine Verified.of_correct block_correct ?_ (by
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, X86_64.abi, X86_64.argRegs,
      Proof.ChaCha20.blockX86_64]
      [satState] using satState)
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

end VG.Proof.ChaCha20.X86_64
