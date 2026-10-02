import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20 keystream XOR on x86 (32-bit)

Correctness follows the x86-64 proof (`Proof/ChaCha20/X86_64/Xor.lean`): an
invariant before each block (`OInv`), one after the call of the block
function (`AInv`) and one before each byte (`IInv`). The call runs in a
frame holding its two arguments (`WP.frame`), and the block function's own
`Verified` proof gives its effect (`WP.call`); the frame and the return
address are in the 12 bytes of stack below `esp` that the contract reserves.

Constant time is the taint analysis's, which follows the frames and the
calls into the block function. `xor_eax` states that `eax` holds `buf` on
return.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86

/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`,
whose arguments are on the stack (cdecl): XORs the first `len` bytes of the
keystream of the state at `state` into the `len` bytes at `data`.

The code may read and write the arguments (16 bytes above the return
address), `state` (64 bytes; its contents on exit are unspecified), `data`
(`len` bytes) and `buf` (320 bytes of working space). These may not overlap
each other; the buffers may not overlap the return address or the 12 bytes
of stack below it, where the calls of the block function store their
arguments and return address; nothing may wrap around the end of the
(32-bit) address space. `esp` and the arguments (the pointers and the length)
are public; the state and the data are secret. -/
def xorX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let buf : Region := ⟨(arg s 3).setWidth 64, 320⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, data, buf, args] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 320 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (keystream (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86.Xor

open VG VG.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off contains_sub toNat_ofNat_lt readW_writeW_off block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev ST : BitVec 32 := arg s₀ 0
abbrev DP : BitVec 32 := arg s₀ 1
abbrev LN : BitVec 32 := arg s₀ 2
abbrev BP : BitVec 32 := arg s₀ 3
abbrev L : Nat := (LN s₀).toNat
abbrev st : Addr := (ST s₀).setWidth 64
abbrev dp : Addr := (DP s₀).setWidth 64
abbrev bp : Addr := (BP s₀).setWidth 64
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stackR : Region := ⟨(E s₀).setWidth 64 - 12, 12⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 32 := (LN s₀).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀, aR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  a_st : (aR s₀).Disjoint (stR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  a_b : (aR s₀).Disjoint (bR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  stk_st : (stackR s₀).Disjoint (stR s₀)
  stk_d : (stackR s₀).Disjoint (dR s₀)
  stk_b : (stackR s₀).Disjoint (bR s₀)
  st_fit : (ST s₀).toNat + 64 ≤ 2 ^ 32
  d_fit : (DP s₀).toNat + L s₀ ≤ 2 ^ 32
  b_fit : (BP s₀).toNat + 320 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_hi : (E s₀).toNat + 20 ≤ 2 ^ 32

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorX86.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-- Our caller's `ebx, esi, edi, ebp`, saved in `buf[256, 272)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (bp s₀ + BitVec.ofNat 64 256) 32 = s₀.gpr .ebx ∧
  m.readW (bp s₀ + BitVec.ofNat 64 260) 32 = s₀.gpr .esi ∧
  m.readW (bp s₀ + BitVec.ofNat 64 264) 32 = s₀.gpr .edi ∧
  m.readW (bp s₀ + BitVec.ofNat 64 268) 32 = s₀.gpr .ebp

/-- The regions the code writes: its buffers and the 12 bytes of stack of its calls. -/
abbrev frameR (s₀ : State) : List Region := [stR s₀, dR s₀, bR s₀, stackR s₀]

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (P s₀ j)
  edi : s.gpr .edi = BP s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (L s₀ - P s₀ j)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem

/-! ## Memory -/

namespace XPre
variable {s₀ : State} (hp : XPre s₀)
include hp

theorem w_b : bR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem eaS {d : Nat} (hd : d < 64) : addr (ST s₀) d = st s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fit; omega)

theorem eaB {d : Nat} (hd : d < 320) : addr (BP s₀) d = bp s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.b_fit; omega)

theorem eaE {d : Nat} (hd : d < 20) : addr (E s₀) d = (E s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.sp_hi; omega)

theorem out_b {d n : Nat} (h : d + n ≤ 320) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 d) n :=
  ⟨bR s₀, hp.w_b, contains_off h (by lit_omega)⟩

theorem arg_contains {i : Nat} (hi : i < 4) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [aR]
  rw [show argAddr s₀ i = addr (E s₀) (4 + 4 * i) from rfl, hp.eaE (by lit_omega),
    show argAddr s₀ 0 = addr (E s₀) 4 from rfl, hp.eaE (by lit_omega)]
  exact contains_sub _ (by lit_omega) (by lit_omega) (by lit_omega)

theorem in_arg {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨aR s₀, by simp [hp.wr], hp.arg_contains hi⟩

end XPre

theorem contains_ofNat {b : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := contains_off h hd

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_ofNat (by lit_omega) (by lit_omega)) hd (by decide)

/-- `buf[256, 272)`, where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨bp s₀ + BitVec.ofNat 64 256, 16⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) := Offset.sub_base _ (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 256 ≤ d → d + 4 ≤ 272 → (savR s₀).Contains (bp s₀ + BitVec.ofNat 64 d) (32 / 8) := by
    intro d h₁ h₂
    exact Offset.contains _ h₁ (by lit_omega) (by lit_omega)
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hf.readW (c 256 (Nat.le_refl _) (by lit_omega)) hd (by decide), h1],
    by rw [hf.readW (c 260 (by lit_omega) (by lit_omega)) hd (by decide), h2],
    by rw [hf.readW (c 264 (by lit_omega) (by lit_omega)) hd (by decide), h3],
    by rw [hf.readW (c 268 (by lit_omega) (by lit_omega)) hd (by decide), h4]⟩

/-! ## The prologue -/

theorem load_buf_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 16))]) s₀ fun s => s = s₀.setReg .eax (BP s₀) := by
  have i₃ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 4 :=
    hp.in_arg (i := 3) (by lit_omega)
  have v₃ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 32 = BP s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₃, v₃, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (bp s₀ + BitVec.ofNat 64 256) (s₀.gpr .ebx)).writeW (bp s₀ + BitVec.ofNat 64 260)
    (s₀.gpr .esi)).writeW (bp s₀ + BitVec.ofNat 64 264) (s₀.gpr .edi)).writeW
    (bp s₀ + BitVec.ofNat 64 268) (s₀.gpr .ebp)

theorem saveMem_frame {s₀ : State} (hp : XPre s₀) : Frame [bR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 320 → (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => contains_off hd (by lit_omega)
  have _ := hp
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 256 (by lit_omega))).writeW
    (List.mem_singleton_self _) _ (c 260 (by lit_omega))).writeW (List.mem_singleton_self _) _
    (c 264 (by lit_omega))).writeW (List.mem_singleton_self _) _ (c 268 (by lit_omega))

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
  · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
  · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem saveMem_arg {s₀ : State} (hp : XPre s₀) {i : Nat} (hi : i < 4) :
    (saveMem s₀).readW (argAddr s₀ i) 32 = arg s₀ i :=
  (saveMem_frame hp).readW (hp.arg_contains hi) (by simpa using hp.a_b) (by decide)

theorem save_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block save) (s₀.setReg .eax (BP s₀)) fun s₁ =>
      s₁.gpr = (s₀.setReg .eax (BP s₀)).gpr ∧ s₁.mem = saveMem s₀ ∧ s₁.rd = s₀.rd ∧
        s₁.wr = s₀.wr := by
  have e : ∀ d, d < 320 → (BP s₀ + BitVec.ofNat 32 d).setWidth 64 = bp s₀ + BitVec.ofNat 64 d :=
    fun d hd => hp.eaB hd
  have e0 := e 256 (by lit_omega); have e1 := e 260 (by lit_omega); have e2 := e 264 (by lit_omega)
  have e3 := e 268 (by lit_omega)
  have o0 := hp.out_b (d := 256) (n := 4) (by lit_omega)
  have o1 := hp.out_b (d := 260) (n := 4) (by lit_omega)
  have o2 := hp.out_b (d := 264) (n := 4) (by lit_omega)
  have o3 := hp.out_b (d := 268) (n := 4) (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [save, saved, List.map, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, at_, State.store32, State.setReg, e0, e1, e2, e3, o0, o1, o2, o3,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, trivial⟩

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : XPre s₀) {s₁ : State}
    (hg : s₁.gpr = (s₀.setReg .eax (BP s₀)).gpr) (hm : s₁.mem = saveMem s₀) (hr : s₁.rd = s₀.rd)
    (hw : s₁.wr = s₀.wr) :
    WP isa (.block [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
      .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)), .alu .test .ebp (.reg .ebp)]) s₁
      fun s => OInv s₀ 0 s ∧ s.zf = some (decide (L s₀ = 0)) := by
  have i₀ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 0) (by lit_omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 1) (by lit_omega)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 2) (by lit_omega)
  have v₀ : (saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = ST s₀ :=
    saveMem_arg hp (i := 0) (by lit_omega)
  have v₁ : (saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = DP s₀ :=
    saveMem_arg hp (i := 1) (by lit_omega)
  have v₂ : (saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 32 = LN s₀ :=
    saveMem_arg hp (i := 2) (by lit_omega)
  have gesp : s₁.gpr .esp = s₀.gpr .esp := by rw [hg]; rfl
  have geax : s₁.gpr .eax = BP s₀ := by rw [hg]; rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, execAlu, arithFlags, State.setReg, State.setFlags, gesp, geax, hm,
    i₀, i₁, i₂, v₀, v₁, v₂, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have hf := saveMem_frame hp
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}) [P],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [P],
    by simp (config := {decide := true}) [hg, State.setReg], hr, hw, ?_, fun k hk => ?_,
    saveMem_saved s₀, hf.mono (by simp)⟩, ?_⟩
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk
  · simp only [BitVec.and_self]
    by_cases h : L s₀ = 0
    · simp [h, BitVec.eq_of_toNat_eq (x := LN s₀) (y := 0) h]
    · have : LN s₀ ≠ 0 := fun h' => h (by simp [L, h'])
      simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block prologue) (s₀.setReg .eax (BP s₀)) fun s =>
      OInv s₀ 0 s ∧ s.zf = some (decide (L s₀ = 0)) := by
  rw [show prologue = save ++ [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
      .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)), .alu .test .ebp (.reg .ebp)]
    from rfl, WP.block_append_iff]
  exact WP.mono (save_ok hp) fun s₁ ⟨hg, hm, hr, hw⟩ => load_ok hp hg hm hr hw

/-! ## Calling the block function -/

/-- `esp` as a 64-bit address. -/
abbrev Es (s₀ : State) : Addr := (E s₀).setWidth 64

theorem toNat_ofNat_lt32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem setWidth_sub {x : BitVec 32} {d : Nat} (h : d ≤ x.toNat) :
    (x - BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 - BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by lit_omega), Nat.mod_eq_of_lt (a := x.toNat) (by lit_omega),
    Nat.mod_eq_of_lt (a := d) (by lit_omega)]
  omega

/-- The 8 bytes of the frame holding the block function's arguments. -/
abbrev fR (s₀ : State) : Region := ⟨Es s₀ - 8, 8⟩
/-- The block function's return address. -/
abbrev cR (s₀ : State) : Region := ⟨Es s₀ - 12, 4⟩
/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

theorem fR_sub (s₀ : State) : Region.Sub (fR s₀) (stackR s₀) := Offset.sub_below _ (by decide) (by decide)

theorem cR_sub (s₀ : State) : Region.Sub (cR s₀) (stackR s₀) := Offset.sub_below _ (by decide) (by decide)

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by lit_omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The permissions the block function is called with. -/
abbrev rdC (s₀ : State) : List Region := [stR s₀, fR s₀]
abbrev wrC (s₀ : State) : List Region := [b256 s₀]

/-- The state the block function is entered in, from `s`. -/
abbrev entry (s : State) : State := (pushed [.edi, .ebx] s).callEntry

theorem entry_esp (s : State) :
    (entry s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 8 - 4 := by
  simp only [entry, State.callEntry_esp, pushed_esp]; rfl

theorem entry_mem (s : State) :
    (entry s).mem = ((s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr .edi)).writeW
      ((s.gpr .esp - 4 - 4).setWidth 64) (s.gpr .ebx)).writeW
      ((s.gpr .esp - BitVec.ofNat 32 8 - 4).setWidth 64) (s.unknowns 0) := by
  simp only [entry, State.callEntry_mem, pushed_esp]
  simp [pushed, pushRegs, State.setReg]

/-- The words at `esp - 4`, `esp - 8` and `esp - 12` lie in the 12 bytes below `esp`. -/
theorem stack_contains (e : Addr) :
    (⟨e - 12, 12⟩ : Region).Contains (e - 4) (32 / 8) ∧ (⟨e - 12, 12⟩ : Region).Contains (e - 8) (32 / 8) ∧
      (⟨e - 12, 12⟩ : Region).Contains (e - 12) (32 / 8) :=
  ⟨Offset.contains_below e (by decide) (by decide) (by decide),
    Offset.contains_below e (by decide) (by decide) (by decide),
    Offset.contains_below e (by decide) (by decide) (by decide)⟩

/-- The words at `esp - 4`, `esp - 8` and `esp - 12` do not overlap. -/
theorem stack_seps (e : Addr) :
    Mem.Sep (e - 8) (32 / 8) (e - 12) (32 / 8) ∧ Mem.Sep (e - 4) (32 / 8) (e - 12) (32 / 8) ∧
      Mem.Sep (e - 4) (32 / 8) (e - 8) (32 / 8) :=
  ⟨Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide)⟩

section
variable {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀)
include hp hE

theorem entry_addrs :
    ((s.gpr .esp - 4).setWidth 64 = Es s₀ - 4) ∧ ((s.gpr .esp - 4 - 4).setWidth 64 = Es s₀ - 8) ∧
    ((s.gpr .esp - BitVec.ofNat 32 8 - 4).setWidth 64 = Es s₀ - 12) := by
  have hlo := hp.sp_lo
  rw [hE]
  refine ⟨setWidth_sub (d := 4) (by lit_omega), ?_, ?_⟩
  · rw [show E s₀ - 4 - 4 = E s₀ - BitVec.ofNat 32 8 by rw [BitVec.sub_sub]; rfl, setWidth_sub (by lit_omega)]; rfl
  · rw [show E s₀ - BitVec.ofNat 32 8 - 4 = E s₀ - BitVec.ofNat 32 12 by rw [BitVec.sub_sub]; rfl,
      setWidth_sub (by lit_omega)]; rfl

theorem entry_frame : Frame [stackR s₀] s.mem (entry s).mem := by
  obtain ⟨a₁, a₂, a₃⟩ := entry_addrs hp hE
  obtain ⟨c4, c8, c12⟩ := stack_contains (Es s₀)
  rw [entry_mem, a₁, a₂, a₃]
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c4).writeW
    (List.mem_singleton_self _) _ c8).writeW (List.mem_singleton_self _) _ c12

theorem entry_argAddr0 : argAddr (entry s) 0 = Es s₀ - 8 := by
  have hlo := hp.sp_lo
  simp only [argAddr, entry_esp, hE]
  rw [show E s₀ - BitVec.ofNat 32 8 - 4 + BitVec.ofNat 32 (4 + 4 * 0) = E s₀ - BitVec.ofNat 32 8 by
    rw [BitVec.sub_sub, Offset.sub_ofNat_eq (E s₀) (show 8 ≤ 12 by decide)]; rfl, setWidth_sub (by lit_omega)]; rfl

theorem entry_argAddr1 : argAddr (entry s) 1 = Es s₀ - 4 := by
  have hlo := hp.sp_lo
  simp only [argAddr, entry_esp, hE]
  rw [show E s₀ - BitVec.ofNat 32 8 - 4 + BitVec.ofNat 32 (4 + 4 * 1) = E s₀ - BitVec.ofNat 32 4 by
    rw [BitVec.sub_sub, Offset.sub_ofNat_eq (E s₀) (show 4 ≤ 12 by decide)]; rfl, setWidth_sub (by lit_omega)]; rfl

theorem entry_arg0 (hb : s.gpr .ebx = ST s₀) : arg (entry s) 0 = ST s₀ := by
  obtain ⟨a₁, a₂, a₃⟩ := entry_addrs hp hE
  show (entry s).mem.readW (argAddr (entry s) 0) 32 = ST s₀
  rw [entry_argAddr0 hp hE, entry_mem, a₁, a₂, a₃,
    Mem.readW_writeW_sep (stack_seps _).1 (by decide), Mem.readW_writeW_self32, hb]

theorem entry_arg1 (hd : s.gpr .edi = BP s₀) : arg (entry s) 1 = BP s₀ := by
  obtain ⟨a₁, a₂, a₃⟩ := entry_addrs hp hE
  show (entry s).mem.readW (argAddr (entry s) 1) 32 = BP s₀
  rw [entry_argAddr1 hp hE, entry_mem, a₁, a₂, a₃,
    Mem.readW_writeW_sep (stack_seps _).2.1 (by decide),
    Mem.readW_writeW_sep (stack_seps _).2.2 (by decide), Mem.readW_writeW_self32, hd]

theorem entry_esp64 : ((entry s).gpr .esp).setWidth 64 = Es s₀ - 12 := by
  rw [entry_esp]; exact (entry_addrs hp hE).2.2

theorem entry_esp_fit : ((entry s).gpr .esp).toNat + 12 ≤ 2 ^ 32 := by
  have hlo := hp.sp_lo
  rw [entry_esp, hE, show E s₀ - BitVec.ofNat 32 8 - 4 = E s₀ - BitVec.ofNat 32 12 by
    rw [BitVec.sub_sub]; rfl,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by lit_omega)]; omega),
    toNat_ofNat_lt32 (by lit_omega)]
  have := (E s₀).isLt
  omega

end

/-- The block function's precondition, from the facts about its entry state. -/
theorem pre_block_of {s₀ s' : State} (hp : XPre s₀) (h₀ : arg s' 0 = ST s₀) (h₁ : arg s' 1 = BP s₀)
    (ha : argAddr s' 0 = Es s₀ - 8) (hr : (s'.gpr .esp).setWidth 64 = Es s₀ - 12)
    (ht : (s'.gpr .esp).toNat + 12 ≤ 2 ^ 32) (hrd : s'.rd = rdC s₀) (hwr : s'.wr = wrC s₀) :
    Proof.ChaCha20.blockX86.pre s' := by
  show s'.rd = [⟨(arg s' 0).setWidth 64, 64⟩, ⟨argAddr s' 0, 8⟩] ∧
    s'.wr = [⟨(arg s' 1).setWidth 64, 256⟩] ∧
    Region.Disjoint ⟨(arg s' 1).setWidth 64, 256⟩ ⟨(arg s' 0).setWidth 64, 64⟩ ∧
    Region.Disjoint ⟨argAddr s' 0, 8⟩ ⟨(arg s' 1).setWidth 64, 256⟩ ∧
    Region.Disjoint ⟨(s'.gpr .esp).setWidth 64, 4⟩ ⟨(arg s' 1).setWidth 64, 256⟩ ∧
    (arg s' 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s' 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s'.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rw [h₀, h₁, ha, hr]
  exact ⟨hrd, hwr, (hp.st_b.sub_right (b256_sub s₀)).symm,
    (hp.stk_b.sub_left (fR_sub s₀)).sub_right (b256_sub s₀),
    (hp.stk_b.sub_left (cR_sub s₀)).sub_right (b256_sub s₀), hp.st_fit,
    by have := hp.b_fit; omega, ht⟩

/-- The block function's precondition holds when it is called. -/
theorem entry_pre {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀)
    (hb : s.gpr .ebx = ST s₀) (hd : s.gpr .edi = BP s₀) :
    Proof.ChaCha20.blockX86.pre ((entry s).withRegions (rdC s₀) (wrC s₀)) :=
  pre_block_of (s' := (entry s).withRegions (rdC s₀) (wrC s₀)) hp (entry_arg0 (s := s) hp hE hb)
    (entry_arg1 (s := s) hp hE hd) (entry_argAddr0 (s := s) hp hE) (entry_esp64 (s := s) hp hE)
    (entry_esp_fit (s := s) hp hE) rfl rfl

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem pushed_wr_eq {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀) :
    (pushed [.edi, .ebx] s).wr = fR s₀ :: s.wr := by
  have hlo := hp.sp_lo
  rw [pushed_wr, hE]
  show below (E s₀) 8 :: s.wr = _
  simp only [below]
  rw [setWidth_sub (by lit_omega)]; rfl

theorem call_covers {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers (rdC s₀ ++ wrC s₀) ((pushed [.edi, .ebx] s).rd ++ (pushed [.edi, .ebx] s).wr) ∧
      Covers (wrC s₀) (pushed [.edi, .ebx] s).wr := by
  rw [pushed_rd, pushed_wr_eq hp hE, hrd, hwr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨fR s₀, by simp, 0, by simp, show 0 + 8 ≤ 8 by omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩

/-! ### The frame's pop -/

theorem popped_esp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) := (popReg_eq s r k).2.2.1

theorem popped_gpr (r : Reg) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .esp) (h₂ : q ≠ r) :
    (popped r k s).gpr q = s.gpr q := (popReg_eq s r k).2.2.2 q h₁ h₂

theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd := (popReg_eq s r k).1

theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl

theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  (popReg_rest s r k).1

/-! ### The call -/

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := by
  have : ((instrs Impl.ChaCha20.X86.block).all fun i => !Taint.clobbers i .esp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem block_stackUse : stackUse Impl.ChaCha20.X86.block = 0 := by lit_decide

theorem stackR_eq {s₀ : State} (hp : XPre s₀) : stackR s₀ = below (E s₀) 12 := by
  simp only [stackR, below]
  rw [setWidth_sub hp.sp_lo]
  rfl

theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa callBlock s (AInv s₀ j) := by
  have hlo := hp.sp_lo
  obtain ⟨hc, hw⟩ := call_covers hp h.esp h.rd h.wr
  have hn : 4 * [Reg.edi, .ebx].length ≤ (s.gpr .esp).toNat := by
    rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
  have hd : stackUse Impl.ChaCha20.X86.block + 4 ≤ ((pushed [.edi, .ebx] s).gpr .esp).toNat := by
    rw [block_stackUse, pushed_esp, sub_toNat hn, h.esp]
    simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (rs := [.edi, .ebx]) (r := .eax) (by simp) (by decide) (by decide) hn block_nosp ?_
  refine WP.call (k := Proof.ChaCha20.blockX86) block_correct block_nosp hd (rd := rdC s₀)
    (wr := wrC s₀) (entry_pre hp h.esp h.ebx h.edi) hc hw
    fun s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hsp : s'.gpr .esp = (pushed [.edi, .ebx] s).gpr .esp := hcs .esp (by simp [calleeSaved])
  -- The frame, the return address and the block function's writes.
  have hF : Frame [b256 s₀, stackR s₀] s.mem s'.mem := by
    rw [stackR_eq hp]
    refine (Frame.sub (pushed_frame (by decide) hn) fun r hr => ?_).trans (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (E s₀) 12, by simp, by rw [h.esp]; exact below_sub (by decide) hlo⟩
    · simp only [wrC, block_stackUse, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨b256 s₀, by simp, fun _ h => h⟩
      · refine ⟨below (E s₀) 12, by simp, ?_⟩
        rw [pushed_esp, h.esp]
        exact below_inner (by decide) hlo
  have hd : ∀ R : Region, R.Disjoint (b256 s₀) → R.Disjoint (stackR s₀) →
      ∀ r ∈ [b256 s₀, stackR s₀], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  have hst : stateAt s'.mem (st s₀) = stateAt s.mem (st s₀) :=
    stateAt_frame hF (hd _ (hp.st_b.sub_right (b256_sub s₀)) hp.stk_st.symm)
  have g : ∀ r ∈ calleeSaved, r ≠ .esp → r ≠ .eax → (popped .eax [Reg.edi, .ebx].length s').gpr r = s.gpr r := by
    intro r hr h₁ h₂
    rw [popped_gpr _ _ _ h₁ h₂, hcs r hr, pushed_gpr _ _ h₁]
  have e0 : arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 0 = ST s₀ := entry_arg0 (s := s) hp h.esp h.ebx
  have e1 : arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 1 = BP s₀ := entry_arg1 (s := s) hp h.esp h.edi
  have hpost' : stateAt s'.mem (bp s₀) = Spec.ChaCha20.block (ctr (S0 s₀) j) := by
    have := (show stateAt s₂.mem ((arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 1).setWidth 64) =
      Spec.ChaCha20.block (stateAt ((entry s).withRegions (rdC s₀) (wrC s₀)).mem
        ((arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 0).setWidth 64)) from hpost)
    rw [e0, e1, hm₂, State.withRegions_mem,
      stateAt_frame (entry_frame hp h.esp) (by simpa using hp.stk_st.symm), h.cnt] at this
    exact this
  refine ⟨⟨by rw [g .ebx (by simp [calleeSaved]) (by decide) (by decide), h.ebx],
    by rw [g .esi (by simp [calleeSaved]) (by decide) (by decide), h.esi],
    by rw [g .edi (by simp [calleeSaved]) (by decide) (by decide), h.edi],
    by rw [g .ebp (by simp [calleeSaved]) (by decide) (by decide), h.ebp],
    ?_, by rw [popped_rd, hrd, pushed_rd, h.rd],
    by rw [popped_wr, hwr, pushed_wr_eq hp h.esp, List.tail_cons, h.wr],
    by rw [popped_mem, hst, h.cnt], fun k hk => ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · rw [popped_esp, hsp, pushed_esp, h.esp]
    simp only [List.length_cons, List.length_nil]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, hF.bytes (R := dR s₀) (hd _ (hp.d_b.sub_right (b256_sub s₀)) hp.stk_d.symm)
      (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
    exact h.data k hk
  · rw [popped_mem]
    exact h.saved.frame hF (hd _ (savR_b256 s₀) (hp.stk_b.symm.sub_left (savR_sub s₀)))
  · rw [popped_mem]
    exact h.frame.trans (hF.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨bR s₀, by simp, b256_sub s₀⟩
      · exact ⟨stackR s₀, by simp, fun _ h => h⟩)
  · rw [popped_mem, ← serialize_stateAt s'.mem (bp s₀) ht, hpost']

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (P s₀ j + i)
  edi : s.gpr .edi = BP s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (L s₀ - P s₀ j)
  esp : s.gpr .esp = E s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (C s₀ j - i)
  edx : s.gpr .edx = BP s₀ + BitVec.ofNat 32 i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j + i then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem P_le (s₀ : State) (j : Nat) : P s₀ j ≤ L s₀ := Nat.min_le_right _ _

set_option simprocs false in
theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa select s (IInv s₀ j 0) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  have hr : (s.gpr .ebp).toNat = L s₀ - P s₀ j := by
    rw [h.ebp, toNat_ofNat_lt32 (by lit_omega)]
  have h₁ : WP isa (.block [.mov .ecx (.reg .ebp), .alu .cmp .ebp (.imm 64)]) s fun s₁ =>
      s₁.gpr .ecx = s.gpr .ebp ∧ (∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧
        s₁.wr = s.wr ∧ s₁.mem = s.mem ∧ eval .b s₁ = some (decide (L s₀ - P s₀ j < 64)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false]
    refine ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, ?_⟩
    simp only [eval, hr]
    rfl
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅, hb⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s₂ : State => s₂.gpr .ecx = BitVec.ofNat 32 (C s₀ j) ∧
      (∀ r, r ≠ .ecx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.mem = s₁.mem) ?_
    fun s₂ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite _ hb (fun hlt => WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hge => ?_)
    · simp only [decide_eq_true_eq] at hlt
      rw [e₁, h.ebp]; congr 1; omega
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, fun r hr => by simp [State.setReg, hr], rfl, rfl, rfl⟩
      simp only [State.setReg, ite_true]
      rw [show C s₀ j = 64 by omega]; rfl
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .ecx → r ≠ .edx → (s₂.setReg .edx (s₂.gpr .edi)).gpr r = s.gpr r :=
      fun r h₁ h₂ => by simp only [State.setReg, h₂, ite_false]; rw [f₂ r h₁, e₂ r h₁]
    have gm : (s₂.setReg .edx (s₂.gpr .edi)).mem = s.mem := by
      rw [State.setReg]; exact f₅.trans e₅
    have gd : s₂.gpr .edi = BP s₀ := by rw [f₂ _ (by decide), e₂ _ (by decide), h.edi]
    refine ⟨by rw [g _ (by decide) (by decide), h.ebx],
      by rw [g _ (by decide) (by decide), h.esi, Nat.add_zero],
      by rw [g _ (by decide) (by decide), h.edi], by rw [g _ (by decide) (by decide), h.ebp],
      by rw [g _ (by decide) (by decide), h.esp],
      by simp only [State.setReg, (by decide : Reg.ecx ≠ .edx), ite_false, Nat.sub_zero]; exact f₁,
      by simp only [State.setReg, ite_true, gd]; simp,
      by rw [← h.rd, ← e₃, ← f₃]; rfl, by rw [← h.wr, ← e₄, ← f₄]; rfl, by rw [gm]; exact h.cnt,
      fun k hk => by rw [gm, h.data k hk, Nat.add_zero], by rw [gm]; exact h.saved,
      by rw [gm]; exact h.frame, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

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

/-- The low byte of a word in memory is its first byte. -/
theorem low_byte (m : Mem) (a : Addr) : (m.readW a 32).setWidth 8 = m a := by
  have := Mem.readW_byte m a (i := 0) (by lit_omega)
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  rw [this]
  ext i hi
  simp

theorem xor_low (b : Byte) (w : BitVec 32) : (b.setWidth 32 ^^^ w).setWidth 8 = b ^^^ w.setWidth 8 := by
  ext i hi; simp

/-- `p + k`, as the code computes it, without wrapping around. -/
theorem ptr_add (x : BitVec 32) {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 0).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

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

theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem add_ofNat_one (x : BitVec 32) (n : Nat) :
    x + BitVec.ofNat 32 n + 1 = x + BitVec.ofNat 32 (n + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

set_option simprocs false in
theorem xor_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) :
    WP isa (.block xorBody) s fun s' =>
      IInv s₀ j (i + 1) s' ∧ s'.zf = some (decide (i + 1 = C s₀ j)) := by
  have hL := L_lt s₀
  have hk : P s₀ j + i < L s₀ := by have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl; omega
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have ea₁ : (DP s₀ + BitVec.ofNat 32 (P s₀ j + i) + BitVec.ofNat 32 0).setWidth 64 =
      dp s₀ + BitVec.ofNat 64 (P s₀ j + i) := ptr_add _ (by have := hp.d_fit; omega)
  have ea₂ : (BP s₀ + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = bp s₀ + BitVec.ofNat 64 i :=
    ptr_add _ (by have := hp.b_fit; omega)
  have cd : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    contains_ofNat (by lit_omega) (by lit_omega)
  have cb : (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 i) 4 := contains_ofNat (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 i) 4 :=
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.wr, hp.wr], cd⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.load32,
    State.store8, State.setReg, State.setFlags, Reg8.reg, h.esi, h.edx, ea₁, ea₂, i₁, i₂, o₁,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hd : s.mem (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) = D0 s₀ (P s₀ j + i) := by
    rw [h.data _ hk]; simp
  have hks : (s.mem.readW (bp s₀ + BitVec.ofNat 64 i) 32).setWidth 8 = (KS s₀).getD (P s₀ j + i) 0 := by
    rw [low_byte, h.ks i (by lit_omega), ks_eq hj hi]
  rw [xor_low, hd, hks]
  have hfd : Frame [dR s₀] s.mem (s.mem.writeW (dp s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  refine ⟨⟨by simp (config := {decide := true}) [h.ebx], ?_, by simp (config := {decide := true}) [h.edi],
    by simp (config := {decide := true}) [h.ebp], by simp (config := {decide := true}) [h.esp],
    ?_, ?_, h.rd, h.wr, ?_, fun k hk' => ?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    exact add_ofNat_one _ _
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ecx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by lit_omega)]; simp; omega),
      toNat_ofNat_lt32 (by lit_omega), toNat_ofNat_lt32 (by lit_omega)]
    simp; omega
  · simp (config := {decide := true}) only [ite_true, ite_false]
    exact add_ofNat_one _ _
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
  · rw [h.ecx]
    by_cases he : i + 1 = C s₀ j
    · rw [show C s₀ j - i = 1 by omega]; simp [he]
    · have : BitVec.ofNat 32 (C s₀ j - i) - 1 ≠ 0 := by
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by lit_omega)]; simp; omega),
          toNat_ofNat_lt32 (by lit_omega)] at this
        simp at this; omega
      simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

/-! ## The end of a block -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (by lit_omega) (by lit_omega) (by lit_omega)

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) :
    WP isa (.block next) s fun s' =>
      OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) := by
  have hL := L_lt s₀
  have hP := P_succ hj
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have hCL : C s₀ j ≤ L s₀ - P s₀ j := Nat.min_le_right _ _
  have c₁ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 := contains_ofNat (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 48) 4 :=
    ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (st s₀ + BitVec.ofNat 64 48) 4 := ⟨stR s₀, by simp [h.wr, hp.wr], c₁⟩
  have ea : (ST s₀ + BitVec.ofNat 32 48).setWidth 64 = st s₀ + BitVec.ofNat 64 48 := hp.eaS (by lit_omega)
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, readSrc, execAlu, arithFlags, State.load32, State.store32, State.setReg,
    State.setFlags, h.ebx, ea, i₁, o₁, hv, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have hfs : Frame [stR s₀] s.mem (s.mem.writeW (st s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12]'(by decide) + 1)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hedx : s.gpr .edx - s.gpr .edi = BitVec.ofNat 32 (C s₀ j) := by rw [h.edx, h.edi, BitVec.add_comm, BitVec.add_sub_cancel]
  have hebp : (s.gpr .ebp).toNat = L s₀ - P s₀ j := by rw [h.ebp, toNat_ofNat_lt32 (by lit_omega)]
  have hsub : s.gpr .ebp - BitVec.ofNat 32 (C s₀ j) = BitVec.ofNat 32 (L s₀ - P s₀ (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hebp, toNat_ofNat_lt32 (by lit_omega)]; omega), hebp,
      toNat_ofNat_lt32 (by lit_omega), toNat_ofNat_lt32 (by lit_omega)]
    omega
  refine ⟨⟨by simp (config := {decide := true}) [h.ebx], ?_, by simp (config := {decide := true}) [h.edi],
    ?_, by simp (config := {decide := true}) [h.esp], h.rd, h.wr, ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_false, h.esi, hP]
  · simp (config := {decide := true}) only [ite_true, hedx, hsub]
  · dsimp only; rw [stateAt_writeW_counter, h.cnt, ctr_succ]
  · dsimp only
    rw [hfs.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (show L s₀ ≤ 2 ^ 64 by omega) hk,
      h.data k hk, hP]
  · exact h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)
  · exact h.frame.writeW (by simp) _ c₁
  · simp (config := {decide := true}) only [hedx, hsub]
    by_cases he : L s₀ - P s₀ (j + 1) = 0
    · simp [he]
    · have : BitVec.ofNat 32 (L s₀ - P s₀ (j + 1)) ≠ 0 := by
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_lt32 (by lit_omega)] at this
        simp at this; omega
      simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  have hpos : 0 < C s₀ j := by simp only [C]; omega
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (eval .ne s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
        (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, hl], C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

/-- The code after the call. -/
abbrev rest : Prog isa := .seq select (.seq xorLoop (.block next))

theorem rest_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : AInv s₀ j s) :
    WP isa rest s fun s' => OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) :=
  WP.seq (WP.mono (sel_ok hj h) fun _ h₁ =>
    WP.seq (WP.mono (xorLoop_ok hp hj h₁) fun _ h₂ => next_ok hp hj h₂))

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa body s fun s' => OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) :=
  WP.seq (WP.mono (call_ok hp h) fun _ h₁ => rest_ok hp hj h₁)

/-! ## The epilogue -/

theorem restore_eq : restore =
    [.mov .ebx (.mem (at_ .eax 256)), .mov .esi (.mem (at_ .eax 260)), .mov .edi (.mem (at_ .eax 264)),
     .mov .ebp (.mem (at_ .eax 268))] := rfl

theorem ret_stack (s₀ : State) : (retR s₀).Disjoint (stackR s₀) := by
  have := Offset.disjoint_base (Es s₀ - BitVec.ofNat 64 12) (d := 12) (n := 4) (k := 12) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa (.block (.mov .eax (.reg .edi) :: restore)) s fun s' =>
      (abiPreserved s₀ s' ∧ Proof.ChaCha20.xorX86.post s₀ s') ∧ s'.gpr .eax = BP s₀ := by
  have e : ∀ d, d < 320 → (BP s₀ + BitVec.ofNat 32 d).setWidth 64 = bp s₀ + BitVec.ofNat 64 d :=
    fun d hd => hp.eaB hd
  have e0 := e 256 (by lit_omega); have e1 := e 260 (by lit_omega); have e2 := e 264 (by lit_omega)
  have e3 := e 268 (by lit_omega)
  have i : ∀ d, d + 4 ≤ 320 → InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 d) 4 :=
    fun d hd => ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], contains_off hd (by lit_omega)⟩
  have i0 := i 256 (by lit_omega); have i1 := i 260 (by lit_omega); have i2 := i 264 (by lit_omega)
  have i3 := i 268 (by lit_omega)
  obtain ⟨sv1, sv2, sv3, sv4⟩ := h.saved
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, at_,
    State.ea, readSrc, State.load32, State.setReg, h.edi, e0, e1, e2, e3, i0, i1, i2, i3, sv1, sv2,
    sv3, sv4, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, by simp⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) only [ite_true, ite_false]
    exact h.esp
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

theorem xor_eq : Impl.ChaCha20.X86.Xor.xor =
    .seq (.block [.mov .eax (.mem (at_ .esp 16))]) (.seq (.block prologue)
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block (.mov .eax (.reg .edi) :: restore)))) := rfl

theorem loop_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : OInv s₀ 0 s) (hL : L s₀ ≠ 0) :
    WP isa (.loop body .ne) s fun s' => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s' := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s
  have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
      (eval .ne s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (body_ok hp hj hI) fun s' ⟨h', hz'⟩ => ?_
    have hP := P_succ hj
    have hC : 0 < C s₀ j := by simp only [C]; omega
    have hle : P s₀ (j + 1) ≤ L s₀ := P_le s₀ (j + 1)
    by_cases hl : L s₀ - P s₀ (j + 1) = 0
    · exact .inl ⟨by simp [eval, hz', hl], j + 1, by omega, h'⟩
    · exact .inr ⟨by simp [eval, hz', hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s ⟨0, rfl, by simp [P]; omega, h⟩

theorem correct {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.X86.Xor.xor s₀ fun s' =>
      (abiPreserved s₀ s' ∧ Proof.ChaCha20.xorX86.post s₀ s') ∧ s'.gpr .eax = BP s₀ := by
  rw [xor_eq]
  refine WP.seq (WP.mono (load_buf_ok hp) fun s e => ?_)
  subst e
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => epilogue_ok hp hj h₂)
  refine WP.ite (decide (L s₀ = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by simp [P, h], h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    exact loop_ok hp h₁ h

/-- `vg_chacha20_xor` returns with `eax` holding `buf`, for a caller that
recomputes pointers from it. -/
theorem xor_eax (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86.post s s' ∧ s'.gpr .eax = arg s 3) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := correct (XPre.of s hs)
  exact ⟨t, s', he, h.1, h.2, hr⟩

/-! ## Constant time

The taint analysis follows the frames and the calls into the block function.
On entry it knows `esp` and where the writable regions are: `state`, the data
(whose length varies), `buf` and the arguments, which are public and at
`esp + 4`, and whose words 0 and 3 are the base addresses of `state` and
`buf`; and that the 12 bytes below `esp` are free for the frames and the
return addresses of the calls. -/

def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 0, 320, 16], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 16)], wbases := [(3, 0, 0), (3, 12, 2)], room := 12 }

theorem setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by lit_omega), addr_eq (by lit_omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (hp : XPre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fit; have hd := hp.d_fit; have hb := hp.b_fit
  have hs : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.sp_hi
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_d, hp.st_b, hp.a_st.symm⟩, ⟨hp.d_b, hp.a_d.symm⟩, hp.a_b.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [st, setWidth_toNat]; omega
    · simp only [dp, setWidth_toNat]; omega
    · simp only [bp, setWidth_toNat]; omega
    · show (addr (s.gpr .esp) 4).toNat + 16 ≤ 2 ^ 32
      rw [addr_eq (by lit_omega), BitVec.toNat_add, setWidth_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 3).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = st s
      simp [addr, st, ST, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 12) 32) 0 = bp s
      rw [argWord_eq hs (k := 12) (by lit_omega)]
      simp [addr, bp, BP, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_d
    · exact hp.stk_b
    · intro x h₁ h₂
      simp only [Region.Contains, τ₀] at h₁ h₂
      rw [show argAddr s 0 = addr (s.gpr .esp) 4 from rfl, addr_eq (by lit_omega)] at h₂
      have := (s.gpr .esp).isLt
      have hE := setWidth_toNat (s.gpr .esp)
      generalize (s.gpr .esp).setWidth 64 = E at *
      bv_omega

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorX86.pre s₁) (h₂ : Proof.ChaCha20.xorX86.pre s₂)
    (hpub : Proof.ChaCha20.xorX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := XPre.of _ h₁; have hp₂ := XPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, dR, bR, aR, st, dp, bp, L, ST, DP, LN, BP, argAddr, ha 0 (by lit_omega),
      ha 1 (by lit_omega), ha 2 (by lit_omega), ha 3 (by lit_omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq hp₁.sp_hi hk, argWord_eq hp₂.sp_hi hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    exact congrArg _ (ha _ (by lit_omega))

/-- Memory whose four argument slots (at `0x5004`) hold `0x1000`, `0x2000`,
`0` and `0x3000`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x20 else if a = 0x5011 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩, ⟨0x5004, 16⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86.post s s' :=
  (correct (XPre.of s hs)).imp fun _ ⟨s', he, h, _⟩ => ⟨s', he, h⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub
    Impl.ChaCha20.X86.Xor.xor :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xor_verified :
    Verified X86.target Impl.ChaCha20.X86.Xor.xor (Spec.ChaCha20.xorContract X86.abi 12) :=
  Verified.of_correct xor_correct xor_ct
    (by
      have a0 : arg sat 0 = 0x1000 := by decide
      have a1 : arg sat 1 = 0x2000 := by decide
      have a2 : arg sat 2 = 0 := by decide
      have a3 : arg sat 3 = 0x3000 := by decide
      have e : argAddr sat 0 = 0x5004 := by decide
      have esp : sat.gpr .esp = 0x5000 := rfl
      sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.ChaCha20.xorX86] [a0, a1, a2, a3, e, esp] using sat)

end VG.Proof.ChaCha20.X86.Xor
