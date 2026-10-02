import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.X86
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# ChaCha20 block function on x86 (32-bit): the rounds
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
    Mem.Sep (wordAddr B j) 4 (wordAddr B k) 4 := Offset.sep B (by lit_omega) (by lit_omega) (by lit_omega)

theorem readW_writeW_word (m : Mem) (B : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) : (m.writeW (wordAddr B k) v).readW (wordAddr B j) 32 = m.readW (wordAddr B j) 32 :=
  Mem.readW_writeW_sep (word_sep B hj hk h) (by decide)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The working state, `buf[0..64)`. -/
abbrev workR (B : Addr) : Region := ⟨B, 64⟩

theorem word_in_work (B : Addr) {k : Nat} (hk : k < 16) : (workR B).Contains (wordAddr B k) 4 := Offset.contains_base B (by lit_omega) (by lit_omega)

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
  refine WP.mono (qr_ok _ (v[x]'hx) (v[y]'hy) (v[z]'hz) (v[w]'hw) (by simp [h x hx]) (by simp [h y hy])
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

end

/-!
# ChaCha20 block function on x86 (32-bit): the whole function
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`,
whose arguments are on the stack (cdecl): writes `block` of the state at
`state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read the two arguments (8 bytes above the return address) and `state` (64
bytes), and read and write `buf` (256 bytes; its first 64 bytes hold the
result on exit, and the rest is scratch space whose contents on exit are
unspecified). `buf` may not overlap `state`, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers) are public; the state (key, counter
and nonce) is secret. -/
def blockX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let buf : Region := ⟨(arg s 1).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [state, args] ∧ s.wr = [buf] ∧
    buf.Disjoint state ∧ args.Disjoint buf ∧ ret.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 1).setWidth 64) = block (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
/-- The two pointers. -/
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
/-- Their 64-bit addresses. -/
abbrev SA : Addr := (st s₀).setWidth 64
abbrev BA : Addr := (bp s₀).setWidth 64
abbrev stR : Region := ⟨SA s₀, 64⟩
abbrev bufR : Region := ⟨BA s₀, 256⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀, argR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  arg_buf : (argR s₀).Disjoint (bufR s₀)
  ret_buf : (retR s₀).Disjoint (bufR s₀)
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (bp s₀).toNat + 256 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains p h1 h2 (by lit_omega)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem eaB {d : Nat} (hd : d < 256) : addr (bp s₀) d = BA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.buf_fits; omega)

theorem eaS {d : Nat} (hd : d < 64) : addr (st s₀) d = SA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem eaA {d : Nat} (hd : d < 12) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem hw : bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by lit_omega) (by lit_omega)⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 2) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  simp only [argR, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    hp.eaA (by lit_omega),
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, hp.eaA (by lit_omega)]
  exact Offset.sub _ (by lit_omega) (by lit_omega)

theorem arg_contains {i : Nat} (hi : i < 2) : (argR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [argR]
  rw [show argAddr s₀ i = addr (esp₀ s₀) (4 + 4 * i) from rfl, hp.eaA (by lit_omega),
    show argAddr s₀ 0 = addr (esp₀ s₀) 4 from rfl, hp.eaA (by lit_omega)]
  exact contains_sub _ (by lit_omega) (by lit_omega) (by lit_omega)

theorem in_arg {i : Nat} (hi : i < 2) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨argR s₀, by simp [hp.rd], hp.arg_contains hi⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (contains_off (by lit_omega) (by lit_omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem workR_sub (B : Addr) : Region.Sub (workR B) ⟨B, 256⟩ := Region.sub_prefix (by lit_omega)

theorem frame_buf {s₀ : State} {m m' : Mem} (hf : Frame [workR (BA s₀)] m m') :
    Frame [bufR s₀] m m' :=
  hf.sub fun r hr => ⟨bufR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact workR_sub _⟩

/-! ## Saving the callee-saved registers, and loading the pointers -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  ((s₀.mem.writeW (BA s₀ + BitVec.ofNat 64 64) (s₀.gpr .ebx)).writeW (BA s₀ + BitVec.ofNat 64 68)
    (s₀.gpr .esi)).writeW (BA s₀ + BitVec.ofNat 64 72) (s₀.gpr .edi)

/-- The callee-saved registers `ebx, esi, edi` are saved in `buf`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (BA s₀ + BitVec.ofNat 64 64) 32 = s₀.gpr .ebx ∧
  m.readW (BA s₀ + BitVec.ofNat 64 68) 32 = s₀.gpr .esi ∧
  m.readW (BA s₀ + BitVec.ofNat 64 72) 32 = s₀.gpr .edi

theorem off_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) 4 (p + BitVec.ofNat 64 e) 4 := Offset.sep p h (by lit_omega) (by lit_omega)

theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he h) (by decide)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_⟩
  · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
  · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem saveMem_frame (s₀ : State) : Frame [bufR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 256 → (bufR s₀).Contains (BA s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => contains_off hd (by lit_omega)
  simp only [saveMem]
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 64 (by lit_omega))).writeW
    (List.mem_singleton_self _) _ (c 68 (by lit_omega))).writeW (List.mem_singleton_self _) _
    (c 72 (by lit_omega))

/-- The saved registers survive writes to the working state. -/
theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) (hf : Frame [workR (BA s₀)] m m') :
    Saved s₀ m' := by
  have key : ∀ d : Nat, 64 ≤ d → d + 4 ≤ 76 →
      m'.readW (BA s₀ + BitVec.ofNat 64 d) 32 = m.readW (BA s₀ + BitVec.ofNat 64 d) 32 := by
    intro d h1 h2
    refine hf.readW (r := ⟨BA s₀ + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint_base _ h1 (by lit_omega)
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨(key 64 (by lit_omega) (by lit_omega)).trans h1, (key 68 (by lit_omega) (by lit_omega)).trans h2,
    (key 72 (by lit_omega) (by lit_omega)).trans h3⟩

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .esi = bp s₀ ∧ s₁.gpr .edi = st s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = saveMem s₀ := by
  have i8 : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    hp.in_arg (i := 1) (by lit_omega)
  have i4 : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hp.in_arg (i := 0) (by lit_omega)
  have v8 : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = bp s₀ := rfl
  have v4 : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = st s₀ := rfl
  have e64 : (bp s₀ + BitVec.ofNat 32 64).setWidth 64 = BA s₀ + BitVec.ofNat 64 64 := hp.eaB (by lit_omega)
  have e68 : (bp s₀ + BitVec.ofNat 32 68).setWidth 64 = BA s₀ + BitVec.ofNat 64 68 := hp.eaB (by lit_omega)
  have e72 : (bp s₀ + BitVec.ofNat 32 72).setWidth 64 = BA s₀ + BitVec.ofNat 64 72 := hp.eaB (by lit_omega)
  have o64 := hp.out_buf (d := 64) (n := 4) (by lit_omega)
  have o68 := hp.out_buf (d := 68) (n := 4) (by lit_omega)
  have o72 := hp.out_buf (d := 72) (n := 4) (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [save, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, State.store32, i8, i4, v8, v4, e64, e68, e72, o64, o68, o72,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], by simp, by simp, trivial, trivial, rfl⟩

/-! ## Copying the state -/

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .eax → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [bufR s₀] s₀.mem s.mem
  fw : Frame [workR (BA s₀)] s₁.mem s.mem
  copied : ∀ j (hj : j < 16), j < n → s.mem.readW (wordAddr (BA s₀) j) 32 = (V s₀)[j]

theorem copy_step {s₀ s₁ : State} (hp : Pre s₀) (hesi : s₁.gpr .esi = bp s₀)
    (hedi : s₁.gpr .edi = st s₀) {n : Nat} (hn : n < 16) {s : State} (hc : CI s₀ s₁ n s) :
    WP isa (.block (copyWord n)) s (CI s₀ s₁ (n + 1)) := by
  have hsi : s.gpr .esi = bp s₀ := (hc.keep _ (by decide)).trans hesi
  have hdi : s.gpr .edi = st s₀ := (hc.keep _ (by decide)).trans hedi
  have eS : (st s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = SA s₀ + BitVec.ofNat 64 (4 * n) :=
    hp.eaS (by lit_omega)
  have eB : (bp s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = wordAddr (BA s₀) n := hp.eaB (by lit_omega)
  have iS : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [hc.rd, hc.wr]; exact hp.in_st hn _
  have oB : InRegions s.wr (wordAddr (BA s₀) n) 4 := by rw [hc.wr]; exact hp.out_buf (by lit_omega)
  have hv := hp.read_st hc.fb hn
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, State.store32, hsi, hdi, eS, eB, iS, oB, hv, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr, hc.keep r hr], hc.rd, hc.wr,
    hc.fb.writeW (List.mem_singleton_self _) _ (contains_off (by lit_omega) (by lit_omega)),
    hc.fw.writeW (List.mem_singleton_self _) _ (word_in_work _ hn), fun j hj hjn => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
  · rw [readW_writeW_word _ _ _ hj hn (by lit_omega)]; exact hc.copied j hj hjn
  · exact Mem.readW_writeW_self32 _ _ _

/-! ## Adding the input state -/

/-- The add invariant after `n` words, relative to the state `sB` after the rounds. -/
structure AI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (wordAddr (BA s₀) j) 32 =
    if j < n then (Rs s₀)[j] + (V s₀)[j] else (Rs s₀)[j]
  keep : ∀ r, r ≠ .eax → s.gpr r = sB.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [bufR s₀] s₀.mem s.mem
  fw : Frame [workR (BA s₀)] sB.mem s.mem

theorem add_step {s₀ sB : State} (hp : Pre s₀) (hesi : sB.gpr .esi = bp s₀)
    (hedi : sB.gpr .edi = st s₀) {n : Nat} (hn : n < 16) {s : State} (ha : AI s₀ sB n s) :
    WP isa (.block (addWord n)) s (AI s₀ sB (n + 1)) := by
  have hsi : s.gpr .esi = bp s₀ := (ha.keep _ (by decide)).trans hesi
  have hdi : s.gpr .edi = st s₀ := (ha.keep _ (by decide)).trans hedi
  have eS : (st s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = SA s₀ + BitVec.ofNat 64 (4 * n) :=
    hp.eaS (by lit_omega)
  have eB : (bp s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = wordAddr (BA s₀) n := hp.eaB (by lit_omega)
  have iS : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [ha.rd, ha.wr]; exact hp.in_st hn _
  have iB : InRegions (s.rd ++ s.wr) (wordAddr (BA s₀) n) 4 := by
    rw [ha.wr]; exact hp.in_buf (by lit_omega) _
  have oB : InRegions s.wr (wordAddr (BA s₀) n) 4 := by rw [ha.wr]; exact hp.out_buf (by lit_omega)
  have hv := hp.read_st ha.fb hn
  have hr := ha.out n hn
  simp only [Nat.lt_irrefl, ite_false] at hr
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addWord, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, State.ea, at_, State.load32, State.store32, hsi, hdi,
    eS, eB, iS, iB, oB, hv, hr, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun r hr => by simp [hr, ha.keep r hr], ha.rd, ha.wr,
    ha.fb.writeW (List.mem_singleton_self _) _ (contains_off (by lit_omega) (by lit_omega)),
    ha.fw.writeW (List.mem_singleton_self _) _ (word_in_work _ hn)⟩
  by_cases hjn : j = n
  · subst hjn; simp [Mem.readW_writeW_self32]
  · rw [readW_writeW_word _ _ _ hj hn hjn, ha.out j hj]
    split <;> split <;> first | omega | rfl

/-! ## Restoring the callee-saved registers -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : Saved s₀ s.mem)
    (hesi : s.gpr .esi = bp s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .ebx = s₀.gpr .ebx ∧ s'.gpr .esi = s₀.gpr .esi ∧
      s'.gpr .edi = s₀.gpr .edi ∧ ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r := by
  have e64 : (bp s₀ + BitVec.ofNat 32 64).setWidth 64 = BA s₀ + BitVec.ofNat 64 64 := hp.eaB (by lit_omega)
  have e68 : (bp s₀ + BitVec.ofNat 32 68).setWidth 64 = BA s₀ + BitVec.ofNat 64 68 := hp.eaB (by lit_omega)
  have e72 : (bp s₀ + BitVec.ofNat 32 72).setWidth 64 = BA s₀ + BitVec.ofNat 64 72 := hp.eaB (by lit_omega)
  have i64 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 64) 4 := by
    rw [hwr]; exact hp.in_buf (by lit_omega) _
  have i68 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 68) 4 := by
    rw [hwr]; exact hp.in_buf (by lit_omega) _
  have i72 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 72) 4 := by
    rw [hwr]; exact hp.in_buf (by lit_omega) _
  obtain ⟨g1, g2, g3⟩ := hs
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, hesi, e64, e68, e72, i64, i68, i72, g1, g2, g3, ite_true,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩

/-! ## The whole function -/

theorem finish_split : finish ++ restore = (List.range 16).flatMap addWord ++ restore := rfl

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (wordAddr p j) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' => abiPreserved s₀ s' ∧ Proof.ChaCha20.blockX86.post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hk₁, hesi₁, hedi₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hc₀ : CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, hm₁ ▸ saveMem_frame s₀, Frame.refl _ _,
      fun _ _ h => absurd h (by lit_omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (CI s₀ s₁)
    (fun k s hk hc => copy_step hp hesi₁ hedi₁ hk hc) 16 (Nat.le_refl _) s₁ hc₀) fun s₂ hc => ?_
  have hsi₂ : s₂.gpr .esi = bp s₀ := (hc.keep _ (by decide)).trans hesi₁
  have hdi₂ : s₂.gpr .edi = st s₀ := (hc.keep _ (by decide)).trans hedi₁
  have hctx : Ctx (BA s₀) s₂ :=
    ⟨fun k hk => by rw [hsi₂]; exact hp.eaB (by lit_omega),
      fun k hk => by rw [hc.wr]; exact hp.in_buf (by lit_omega) _,
      fun k hk => by rw [hc.wr]; exact hp.out_buf (by lit_omega)⟩
  refine WP.seq (WP.mono (rounds_ok hctx (fun k hk => hc.copied k hk hk) 10) fun s₃ hR => ?_)
  rw [finish_split, WP.block_append_iff]
  have ha₀ : AI s₀ s₃ 0 s₃ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hR.holds j hj, fun _ _ => rfl,
      hR.rd.trans hc.rd, hR.wr.trans hc.wr, hc.fb.trans (frame_buf hR.frame), Frame.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (AI s₀ s₃)
    (fun k s hk ha => add_step hp (hR.esi.trans hsi₂) (hR.edi.trans hdi₂) hk ha) 16 (Nat.le_refl _) s₃ ha₀)
    fun s₄ hA => ?_
  have hwork : Frame [workR (BA s₀)] s₁.mem s₄.mem := (hc.fw.trans hR.frame).trans hA.fw
  have hsaved : Saved s₀ s₄.mem := saved_frame (hm₁ ▸ saveMem_saved s₀) hwork
  have hsi₄ : s₄.gpr .esi = bp s₀ := (hA.keep _ (by decide)).trans (hR.esi.trans hsi₂)
  refine WP.mono (restore_ok hp hsaved hsi₄ hA.wr) fun s' ⟨hm', hbx, hsi, hdi, hk'⟩ => ?_
  have hesp : s'.gpr .esp = s₀.gpr .esp := by
    rw [hk' _ (by decide) (by decide) (by decide) (by decide), hA.keep _ (by decide), hR.esp,
      hc.keep _ (by decide), hk₁ _ (by decide) (by decide) (by decide) (by decide)]
  have hebp : s'.gpr .ebp = s₀.gpr .ebp := by
    rw [hk' _ (by decide) (by decide) (by decide) (by decide), hA.keep _ (by decide), hR.ebp,
      hc.keep _ (by decide), hk₁ _ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hbx
    · exact hsi
    · exact hdi
    · exact hebp
    · exact hesp
  · rw [hm']
    refine hA.fb.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simpa using hp.ret_buf
  · show stateAt s'.mem (BA s₀) = Spec.ChaCha20.block (V s₀)
    rw [hm']
    exact block_post fun j hj => by simpa [hj] using hA.out j hj

/-- Memory whose two argument slots (at `0x4004`) hold `0x1000` and `0x2000`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 64⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x2000, 256⟩]

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and so are the 12 bytes above it (the
return address and the two pointer arguments), which no store changes. -/
def τ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 8) (by lit_omega) (by simpa using hp.ret_buf)
    (by simpa [argR, argAddr, addr] using hp.arg_buf)

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.blockX86.pre s₁)
    (h₂ : Proof.ChaCha20.blockX86.pre s₂) (hpub : Proof.ChaCha20.blockX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  have f₁ : (s₁.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₁.esp_fits
  have f₂ : (s₂.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₂.esp_fits
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockX86.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockX86.post s s' :=
  correct (pre_of s hs)

theorem block_ct : ConstantTime isa Proof.ChaCha20.blockX86.pre Proof.ChaCha20.blockX86.pub block :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide)

theorem block_verified :
    Verified X86.target Impl.ChaCha20.X86.block (Spec.ChaCha20.blockContract X86.abi) :=
  Verified.of_correct block_correct block_ct (by
    have a0 : arg satState 0 = 0x1000 := by decide
    have a1 : arg satState 1 = 0x2000 := by decide
    have e : argAddr satState 0 = 0x4004 := by decide
    have esp : satState.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.blockX86] [a0, a1, e, esp] using satState)

end VG.Proof.ChaCha20.X86
