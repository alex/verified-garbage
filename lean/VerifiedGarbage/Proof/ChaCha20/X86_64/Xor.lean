import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20 keystream XOR on x86-64

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, the return address on the stack, or the 8
bytes below it, where the call of the block function stores its return
address; `data` does not wrap around the end of the address space. The
pointers and the length are public; the state and the data are secret. -/
def xorX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `xorX86_64` with `k` bytes of stack below the return address, for an
implementation whose calls use them, and that returns with `rsi` pointing at
`buf` (for a caller that recomputes pointers from it): what callers of any
implementation of `vg_chacha20_xor` rely on (see `Variant.lean`). -/
def xorStack (k : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := xorX86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx
  pub := xorX86_64.pub

theorem xorStack_pre8 : (xorStack 8).pre = xorX86_64.pre := rfl

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Xor

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Xor
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast readW_writeW_off
  block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev dp : Addr := s₀.gpr .rsi
abbrev L : Nat := (s₀.gpr .rdx).toNat
abbrev bp : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stackR : Region := below (s₀.gpr .rsp) 8
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  stk_st : (stackR s₀).Disjoint (stR s₀)
  stk_d : (stackR s₀).Disjoint (dR s₀)
  stk_b : (stackR s₀).Disjoint (bR s₀)
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorX86_64.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Our caller's `rbx, rbp, r12`, saved in `buf[256, 280)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (off (bp s₀) 256) 64 = s₀.gpr .rbx ∧ m.readW (off (bp s₀) 264) 64 = s₀.gpr .rbp ∧
  m.readW (off (bp s₀) 272) 64 = s₀.gpr .r12

/-- The regions the code writes: its buffers and the return address of its calls. -/
abbrev frameR (s₀ : State) : List Region := [stR s₀, dR s₀, bR s₀, stackR s₀]

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rsi : s.gpr .rsi = bp s₀
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem

/-! ## Memory -/

theorem XPre.w_st {s₀ : State} (hp : XPre s₀) : stR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem XPre.w_d {s₀ : State} (hp : XPre s₀) : dR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem XPre.w_b {s₀ : State} (hp : XPre s₀) : bR s₀ ∈ s₀.wr := by simp [hp.wr]

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (off p 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  have e : p + BitVec.ofNat 64 (4 * i) = off p (4 * i) := by rw [off, ofInt_natCast]
  rw [e]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (Or.inl rfl) (by lit_omega) (by lit_omega) (by lit_omega)

theorem contains_ofNat {b : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := by
  have := contains_off (base := b) h hd
  rwa [ofInt_natCast] at this

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_ofNat (by lit_omega) (by lit_omega)) hd (by decide)

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86_64.off_sep p hd he (by lit_omega) (by lit_omega) h) (by decide)

/-! ## The prologue -/

theorem save_eq : save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr) =
    [.store (at_ .rcx 256) .rbx, .store (at_ .rcx 264) .rbp, .store (at_ .rcx 272) .r12,
    .mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] := rfl

theorem bR_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 320) : (bR s₀).Contains (off (bp s₀) d) n :=
  contains_off h (by lit_omega)

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr))) s₀ fun s =>
      OInv s₀ 0 s ∧ s.zf = some (decide (L s₀ = 0)) := by
  have o : ∀ d, d + 8 ≤ 320 → InRegions s₀.wr (off (bp s₀) d) 8 :=
    fun d hd => ⟨_, hp.w_b, bR_contains s₀ hd⟩
  have o0 := o 256 (by lit_omega); have o1 := o 264 (by lit_omega); have o2 := o 272 (by lit_omega)
  simp only [off] at o0 o1 o2
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, State.store64, o0, o1, o2, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hf : Frame [bR s₀] s₀.mem (((s₀.mem.writeW (off (bp s₀) 256) (s₀.gpr .rbx)).writeW
      (off (bp s₀) 264) (s₀.gpr .rbp)).writeW (off (bp s₀) 272) (s₀.gpr .r12)) :=
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (bR_contains s₀ (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (bR_contains s₀ (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (bR_contains s₀ (by lit_omega))
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}) [P],
    by simp (config := {decide := true}) [P], by simp (config := {decide := true}), fun r hr => ?_, rfl,
    rfl, ?_, fun k hk => ?_, ?_, hf.mono (by simp)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true})
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (s₀.gpr .rdx).isLt) hk
  · refine ⟨?_, ?_, ?_⟩
    · rw [readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]
    · rw [readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]
  · simp only [BitVec.and_self, L]
    by_cases h : (s₀.gpr .rdx).toNat = 0
    · simp [BitVec.eq_of_toNat_eq (x := s₀.gpr .rdx) (y := 0) h]
    · have : s₀.gpr .rdx ≠ 0 := fun h' => h (by simp [h'])
      simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨off (bp s₀) 256, 24⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) := by
  simp only [savR, off, ofInt_natCast]
  exact Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := by
  simp only [savR, off, ofInt_natCast]
  exact Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 256 ≤ d → d + 8 ≤ 280 → (savR s₀).Contains (off (bp s₀) d) (64 / 8) := by
    intro d h₁ h₂
    simp only [savR, off, ofInt_natCast]
    exact Offset.contains _ h₁ (by lit_omega) (by lit_omega)
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hf.readW (c 256 (Nat.le_refl _) (by lit_omega)) hd (by decide), h1],
    by rw [hf.readW (c 264 (by lit_omega) (by lit_omega)) hd (by decide), h2],
    by rw [hf.readW (c 272 (by lit_omega) (by lit_omega)) hd (by decide), h3]⟩

/-! ## Calling the block function -/

/-- The registers the block function never writes. -/
def kept : List Reg := [.rsi, .rsp]

theorem block_keeps : ((instrs Impl.ChaCha20.X86_64.block).all fun i =>
    kept.all fun r => !Taint.clobbers i r) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs Impl.ChaCha20.X86_64.block, Taint.clobbers i r = false := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp block_keeps i hi) r hr
  simpa using this

theorem block_depth : Impl.ChaCha20.X86_64.block.depth = 0 := by lit_decide


theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by lit_omega)

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

set_option simprocs false in
theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.seq (.block [.mov .rdi (.reg .rbx)]) (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block))
      s (AInv s₀ j) := by
  have h₁ : WP isa (.block [.mov .rdi (.reg .rbx)]) s fun s₁ =>
      s₁.gpr .rdi = st s₀ ∧ (∀ r, r ≠ .rdi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨by simp [State.setReg, h.rbx], fun r hr => by simp [State.setReg, hr], rfl, rfl, rfl⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [e₂ _ (by decide)]; exact h.keep .rsp (by simp)
  have hrsi : s₁.gpr .rsi = bp s₀ := by rw [e₂ _ (by decide)]; exact h.rsi
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hwr : s₁.wr = [stR s₀, dR s₀, bR s₀] := by rw [e₄, h.wr, hp.wr]
  have hrd : s₁.rd = [] := by rw [e₃, h.rd, hp.rd]
  have hstk : below (s₁.gpr .rsp) 8 = stackR s₀ := by rw [hsp]
  refine WP.call (k := Proof.ChaCha20.blockX86_64) block_correct (block_keeps_reg (by simp [kept]))
    (by rw [block_depth]; decide) (rd := [stR s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), e₁, hrsi, hsp]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (b256_sub s₀)).symm,
      hp.stk_b.sub_right (b256_sub s₀)⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ hcs hf hkeep ⟨s₃, hm₃, _, hpost⟩
    rw [block_depth, hstk] at hf
    have g : ∀ r ∈ calleeSaved, r ≠ .rdi → s₂.gpr r = s.gpr r := fun r hr hne => by
      rw [hcs r hr, e₂ r hne]
    have hd : ∀ R : Region, R.Disjoint (b256 s₀) → R.Disjoint (stackR s₀) →
        ∀ r ∈ [b256 s₀] ++ [stackR s₀], R.Disjoint r := by
      intro R h₁ h₂ r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> assumption
    have hst : stateAt s₂.mem (st s₀) = stateAt s₁.mem (st s₀) :=
      stateAt_frame hf (hd _ (hp.st_b.sub_right (b256_sub s₀)) hp.stk_st.symm)
    refine ⟨⟨by rw [g .rbx (by simp [calleeSaved]) (by decide), h.rbx],
      by rw [g .rbp (by simp [calleeSaved]) (by decide), h.rbp],
      by rw [g .r12 (by simp [calleeSaved]) (by decide), h.r12],
      by rw [hkeep .rsi (block_keeps_reg (by simp [kept])), hrsi],
      fun r hr => ?_, by rw [hrd₂, e₃, h.rd], by rw [hwr₂, e₄, h.wr],
      by rw [hst, e₅, h.cnt], fun k hk => ?_, ?_, ?_⟩, fun t ht => ?_⟩
    · have hr' : r ∈ calleeSaved ∧ r ≠ .rdi := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true})
      rw [g r hr'.1 hr'.2]
      exact h.keep r hr
    · rw [hf.bytes (R := dR s₀) (hd _ (hp.d_b.sub_right (b256_sub s₀)) hp.stk_d.symm)
        (Nat.le_of_lt (s₀.gpr .rdx).isLt) hk, e₅]
      exact h.data k hk
    · rw [e₅] at hf
      exact h.saved.frame hf (hd _ (savR_b256 s₀) (hp.stk_b.symm.sub_left (savR_sub s₀)))
    · rw [e₅] at hf
      exact h.frame.trans (hf.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨bR s₀, by simp, b256_sub s₀⟩
        · exact ⟨stackR s₀, by simp, fun _ h => h⟩)
    · have hce : stateAt s₁.callEntry.mem (st s₀) = stateAt s₁.mem (st s₀) := by
        rw [State.callEntry_mem]
        exact stateAt_frame (rs := [stackR s₀])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
            rw [← hstk]; exact below_call _ (by lit_omega) (by lit_omega)))
          (by simpa using hp.stk_st.symm)
      simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
        hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), e₁, hrsi, hm₃, hce,
        e₅, h.cnt] at hpost
      rw [← serialize_stateAt s₂.mem (bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- How many bytes of block `j` are used. -/
abbrev C (s₀ : State) (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rsi : s.gpr .rsi = bp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (C s₀ j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j + i then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

set_option simprocs false in
theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
      (.seq (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)])) (.block [.mov32 .rcx (.imm 0)])))
      s (IInv s₀ j 0) := by
  have h₁ : WP isa (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)]) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .r12 ∧ (∀ r, r ≠ .rdx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.mem = s.mem ∧ eval .b s₁ = some (decide (L s₀ - P s₀ j < 64)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false]
    refine ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, ?_⟩
    have se : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
    have hr : (s.gpr .r12).toNat = L s₀ - P s₀ j := by
      rw [h.r12, toNat_ofNat_lt (by have := L_lt s₀; omega)]
    simp only [eval, se, hr]
    rfl
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅, hb⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s₂ : State => s₂.gpr .rdx = BitVec.ofNat 64 (C s₀ j) ∧
      (∀ r, r ≠ .rdx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.mem = s₁.mem) ?_
    fun s₂ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite _ hb (fun hlt => WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hge => ?_)
    · simp only [decide_eq_true_eq] at hlt
      rw [e₁, h.r12]; congr 1; omega
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, Option.map_some,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, fun r hr => by simp [State.setReg32, State.setReg, hr], rfl, rfl, rfl⟩
      simp only [State.setReg32, State.setReg, ite_true]
      rw [show C s₀ j = 64 by omega]; rfl
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .rdx → r ≠ .rcx → (s₂.setReg32 .rcx 0).gpr r = s.gpr r := fun r h₁ h₂ => by
      simp only [State.setReg32, State.setReg, h₂, ite_false]; rw [f₂ r h₁, e₂ r h₁]
    have gm : (s₂.setReg32 .rcx 0).mem = s.mem := by rw [State.setReg32, State.setReg]; exact f₅.trans e₅
    refine ⟨by rw [g _ (by decide) (by decide), h.rbx], by rw [g _ (by decide) (by decide), h.rbp],
      by rw [g _ (by decide) (by decide), h.r12], by rw [g _ (by decide) (by decide), h.rsi],
      by simp only [State.setReg32, State.setReg, (by decide : Reg.rdx ≠ .rcx), ite_false]; exact f₁,
      by simp [State.setReg32, State.setReg], fun r hr => ?_, by rw [← h.rd, ← e₃, ← f₃]; rfl,
      by rw [← h.wr, ← e₄, ← f₄]; rfl, by rw [gm]; exact h.cnt, fun k hk => ?_, by rw [gm]; exact h.saved,
      by rw [gm]; exact h.frame, fun t ht => by rw [gm]; exact h.ks t ht⟩
    · have hr' : r ≠ .rdx ∧ r ≠ .rcx := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [g r hr'.1 hr'.2]; exact h.keep r hr
    · rw [gm, h.data k hk, Nat.add_zero]

/-! ## One byte -/

def xorBody : List Instr :=
  [.movzx8 .rax dataByte, .movzx8 .r8 ksByte, .alu .xor .rax (.reg .r8), .store8 dataByte .rax,
    .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

theorem xorLoop_eq : xorLoop = .loop (.block xorBody) .ne := rfl

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

theorem xor_setWidth (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < L s₀) (hk' : k' < L s₀) (h : k' ≠ k) :
    dp s₀ + BitVec.ofNat 64 k' ≠ dp s₀ + BitVec.ofNat 64 k := by
  have hL := L_lt s₀
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - dp s₀) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
  exact h this

/-- Byte `k` of the data, before or after block `j`: `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

set_option simprocs false in
theorem xor_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) :
    WP isa (.block xorBody) s fun s' =>
      IInv s₀ j (i + 1) s' ∧ s'.zf = some (decide (i + 1 = C s₀ j)) := by
  have hL := L_lt s₀
  have hk : P s₀ j + i < L s₀ := by have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl; omega
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have ea₁ : dp s₀ + BitVec.ofNat 64 (P s₀ j) + BitVec.ofNat 64 i * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 0 = dp s₀ + BitVec.ofNat 64 (P s₀ j + i) := by
    rw [BitVec.mul_one, BitVec.ofNat_add]; simp [BitVec.add_assoc]
  have ea₂ : bp s₀ + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      bp s₀ + BitVec.ofNat 64 i := by simp
  have cd : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 := contains_ofNat (by lit_omega) (by lit_omega)
  have cb : (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 i) 1 := contains_ofNat (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.wr, hp.wr], cd⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, dataByte, ksByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8,
    State.setReg, State.setFlags, h.rbp, h.rcx, h.rsi, ea₁, ea₂, i₁, i₂, o₁, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', se1]
  have hd : s.mem (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) = D0 s₀ (P s₀ j + i) := by
    rw [h.data _ hk]; simp
  have hks : s.mem (bp s₀ + BitVec.ofNat 64 i) = (KS s₀).getD (P s₀ j + i) 0 := by
    rw [h.ks i (by lit_omega), ks_eq hj hi]
  rw [hd, hks, xor_setWidth]
  have hfd : Frame [dR s₀] s.mem (s.mem.writeW (dp s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  refine ⟨⟨by simp (config := {decide := true}) [h.rbx], by simp (config := {decide := true}) [h.rbp],
    by simp (config := {decide := true}) [h.r12], by simp (config := {decide := true}) [h.rsi],
    by simp (config := {decide := true}) [h.rdx], by simp [BitVec.ofNat_add],
    fun r hr => ?_, h.rd, h.wr, ?_, fun k hk' => ?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · have hr' : r ≠ .rcx ∧ r ≠ .rax ∧ r ≠ .r8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    simp only [hr'.1, hr'.2.1, hr'.2.2, ite_false]; exact h.keep r hr
  · dsimp only; rw [stateAt_frame hfd (by simpa using hp.st_d), h.cnt]
  · dsimp only; rw [writeW8_apply]
    by_cases he : k = P s₀ j + i
    · subst he; simp
    · simp only [data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < P s₀ j + (i + 1) by omega]
  · exact h.saved.frame hfd (by simpa using (hp.d_b.sub_right (savR_sub s₀)).symm)
  · exact h.frame.writeW (by simp) _ cd
  · dsimp only; rw [hfd.bytes (R := bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht
  · rw [h.rdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := C s₀ j) (by lit_omega) (by lit_omega),
      BitVec.ofNat_add]
    rfl

/-! ## The end of a block -/

def nextInstrs : List Instr :=
  [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1), .store32 (at_ .rbx 48) .rax,
    .alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)]

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) :
    WP isa (.block nextInstrs) s fun s' =>
      OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) := by
  have hL := L_lt s₀
  have hP := P_succ hj
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have hCL : C s₀ j ≤ L s₀ - P s₀ j := Nat.min_le_right _ _
  have c₁ : (stR s₀).Contains (off (st s₀) 48) 4 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (off (st s₀) 48) 4 := ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (off (st s₀) 48) 4 := ⟨stR s₀, by simp [h.wr, hp.wr], c₁⟩
  simp only [off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nextInstrs, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags, State.load32, State.store32,
    State.setReg, State.setReg32, State.setFlags, h.rbx, i₁, o₁, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  have hv : s.mem.readW (st s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (ctr (S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  simp only [hv]
  have hfs : Frame [stR s₀] s.mem (s.mem.writeW (off (st s₀) 48) ((ctr (S0 s₀) j)[12]'(by decide) + 1)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hr12 : (s.gpr .r12).toNat = L s₀ - P s₀ j := by rw [h.r12, toNat_ofNat_lt (by lit_omega)]
  have hrdx : (s.gpr .rdx).toNat = C s₀ j := by rw [h.rdx, toNat_ofNat_lt (by lit_omega)]
  refine ⟨⟨by simp (config := {decide := true}) [h.rbx], ?_, ?_, by simp (config := {decide := true}) [h.rsi],
    fun r hr => ?_, h.rd, h.wr, ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, h.rbp, h.rdx, hP, BitVec.ofNat_add,
      BitVec.add_assoc]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hr12, hrdx]; omega), hr12, hrdx,
      toNat_ofNat_lt (by lit_omega)]
    omega
  · have hr' : r ≠ .r12 ∧ r ≠ .rbp ∧ r ≠ .rax := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    simp only [hr'.1, hr'.2.1, hr'.2.2, ite_false]; exact h.keep r hr
  · dsimp only; rw [stateAt_writeW_counter, h.cnt, ctr_succ]
  · dsimp only
    rw [hfs.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (Nat.le_of_lt (L_lt s₀)) hk, h.data k hk, hP]
  · exact h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)
  · exact h.frame.writeW (by simp) _ c₁
  · have hz : (s.gpr .r12 - s.gpr .rdx == 0) = decide (L s₀ - P s₀ j - C s₀ j = 0) := by
      rw [h.r12, h.rdx, Offset.ofNat_sub_ofNat_beq (by lit_omega) (by lit_omega)]
      exact decide_eq_decide.mpr (by lit_omega)
    rw [hz, hP, Nat.sub_sub]

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  have hpos : 0 < C s₀ j := by simp only [C]; omega
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (eval .ne s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, hl], C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

theorem body_eq : body =
    .seq (.block [.mov .rdi (.reg .rbx)]) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
    (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
    (.seq (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)]))
    (.seq (.block [.mov32 .rcx (.imm 0)]) (.seq xorLoop (.block nextInstrs)))))) := rfl

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa body s fun s' => OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) := by
  have hc := call_ok hp h
  rw [WP.seq_iff] at hc
  rw [body_eq, WP.seq_iff]
  refine WP.mono hc fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₁ fun s₂ h₂ => ?_
  have hs := sel_ok hj h₂
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₃ h₃ => ?_
  rw [WP.seq_iff] at h₃
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₄ fun s₅ h₅ => ?_
  exact WP.seq (WP.mono (xorLoop_ok hp hj h₅) fun s₆ h₆ => next_ok hp hj h₆)

/-! ## The epilogue -/

theorem restore_eq : restore =
    [.mov .rbx (.mem (at_ .rsi 256)), .mov .rbp (.mem (at_ .rsi 264)), .mov .r12 (.mem (at_ .rsi 272))] :=
  rfl

theorem ret_stack (s₀ : State) : (retR s₀).Disjoint (stackR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa (.block restore) s fun s' =>
      (gprPreserved s₀ s' ∧ Proof.ChaCha20.xorX86_64.post s₀ s') ∧ s'.gpr .rsi = bp s₀ := by
  have i : ∀ d, d + 8 ≤ 320 → InRegions (s.rd ++ s.wr) (off (bp s₀) d) 8 :=
    fun d hd => ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], bR_contains s₀ hd⟩
  have i0 := i 256 (by lit_omega); have i1 := i 264 (by lit_omega); have i2 := i 272 (by lit_omega)
  simp only [off] at i0 i1 i2
  obtain ⟨sv1, sv2, sv3⟩ := h.saved
  simp only [off] at sv1 sv2 sv3
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.load64, State.setReg, h.rsi, i0, i1, i2, sv1, sv2, sv3, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, by simp (config := {decide := true})⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [ite_true, ite_false] <;>
      exact h.keep _ (by simp)
  · refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_d
    · exact hp.ret_b
    · exact ret_stack s₀
  · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    have hk' : k < L s₀ := hk
    rw [h.data k hk']
    simp only [show k < P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Xor.xor =
    .seq (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore)) := rfl

theorem correct {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.X86_64.Xor.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ Proof.ChaCha20.xorX86_64.post s₀ s') ∧ s'.gpr .rsi = bp s₀ := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => epilogue_ok hp hj h₂)
  refine WP.ite (decide (L s₀ = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by simp [P, h], h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s') ∨
        (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (body_ok hp hj hI) fun s' ⟨h', hz'⟩ => ?_
      have hP := P_succ hj
      have hC : 0 < C s₀ j := by simp only [C]; omega
      have hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by simp [eval, hz', hl], j + 1, by omega, h'⟩
      · exact .inr ⟨by simp [eval, hz', hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega, h₁⟩

/-- `vg_chacha20_xor` returns with `rsi` pointing at `buf`, for a caller that
recomputes pointers from it. -/
theorem xor_rsi (s : State) (hs : Proof.ChaCha20.xorX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := correct (XPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2, hr⟩

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the lengths
of `state` and `buf` (the data's varies) and the registers holding their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.rsi, 1, 0), (.rcx, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorX86_64.pre s₁)
    (h₂ : Proof.ChaCha20.xorX86_64.pre s₂) (hpub : Proof.ChaCha20.xorX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, Proof.ChaCha20.xorX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3], by simp [hw, Nat.le_of_lt (s.gpr .rdx).isLt]⟩,
      fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2, p3, p4]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86_64.post s s' :=
  (xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorX86_64.pre Proof.ChaCha20.xorX86_64.pub
    Impl.ChaCha20.X86_64.Xor.xor :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xor_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.Xor.xor (Spec.ChaCha20.xorContract X86_64.abi 8) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      Proof.ChaCha20.xorX86_64]
      [sat] using sat)

end VG.Proof.ChaCha20.X86_64.Xor
