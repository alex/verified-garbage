import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Impl.ChaCha20.X86.Stream
import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# Streaming ChaCha20 on x86 (32-bit): `init` and `set_nonce`

Untrusted: everything here is checked by Lean. Both load everything first
(`loads_ok`, `nonceLoads_ok`: the number of bytes left by doubling, `dbl_ok`)
and then store it (`nonceStores_ok`, `keyStores_ok`); `nonceMem` and
`keyMem` are the memory they leave.
-/

namespace VG.Proof.ChaCha20

open VG.X86
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt)

/-- x86 (32-bit) contract for `vg_chacha20_set_nonce(state, nonce)`, whose
arguments are on the stack (cdecl). -/
def setNonceX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 768⟩
    let nonce : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [nonce, args] ∧ s.wr = [state] ∧ state.Disjoint nonce ∧ args.Disjoint state ∧
      ret.Disjoint state ∧ (arg s 0).toNat + 768 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem ((arg s 0).setWidth 64) = keyAt s.mem ((arg s 0).setWidth 64) ∧
      restAt s'.mem ((arg s 0).setWidth 64) =
        keystreamOf (keyAt s.mem ((arg s 0).setWidth 64)) (bytesAt s.mem ((arg s 1).setWidth 64) 16)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

/-- x86 (32-bit) contract for `vg_chacha20_init(state, key, nonce)`. -/
def initX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 768⟩
    let key : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let nonce : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, nonce, args] ∧ s.wr = [state] ∧ state.Disjoint key ∧ state.Disjoint nonce ∧
      args.Disjoint state ∧ ret.Disjoint state ∧ (arg s 0).toNat + 768 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem ((arg s 0).setWidth 64) = bytesAt s.mem ((arg s 1).setWidth 64) 32 ∧
      restAt s'.mem ((arg s 0).setWidth 64) =
        keystreamOf (bytesAt s.mem ((arg s 1).setWidth 64) 32) (bytesAt s.mem ((arg s 2).setWidth 64) 16)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off)
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt wordLE)

/-- The number of bytes left for the initial block counter `c`. -/
abbrev V (c : BitVec 32) : Nat := 64 * (2 ^ 32 - c.toNat)

theorem V_lt (c : BitVec 32) : V c < 2 ^ 39 := by have := c.isLt; simp only [V]; omega

/-- `x` in `edx:ecx`. -/
abbrev Pair (s : State) (x : Nat) : Prop := (s.gpr .ecx).toNat + 2 ^ 32 * (s.gpr .edx).toNat = x

/-- `s'` is `s` with `ecx` and `edx` changed. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  xmm : s'.xmm = s.xmm
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {s₁ s₂ s₃ : State} (h₁ : Keep s₁ s₂) (h₂ : Keep s₂ s₃) : Keep s₁ s₃ :=
  ⟨fun r a b => by rw [h₂.gpr r a b, h₁.gpr r a b], by rw [h₂.xmm, h₁.xmm], by rw [h₂.mem, h₁.mem],
    by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr]⟩

def dbl : List Instr := [.alu .add .ecx (.reg .ecx), .alu .adc .edx (.reg .edx)]

set_option simprocs false in
/-- `edx:ecx` doubled. -/
theorem dbl_ok {s : State} {x : Nat} (h : Pair s x) (hx : 2 * x < 2 ^ 64) :
    WP isa (.block dbl) s fun s' => Pair s' (2 * x) ∧ Keep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, Pair]
  refine ⟨?_, fun r h₁ h₂ => by simp [h₁, h₂], rfl, rfl, rfl, rfl⟩
  simp only [Pair] at h
  have ha := (s.gpr .ecx).isLt
  have hb := (s.gpr .edx).isLt
  generalize s.gpr .ecx = a at *
  generalize s.gpr .edx = b at *
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  by_cases hc : 2 ^ 32 ≤ a.toNat + a.toNat
  · simp only [hc, decide_true, Bool.toNat_true]; omega
  · simp only [hc, decide_false, Bool.toNat_false]; omega

def nonceLoad1 : List Instr :=
  [.movdquLoad .xmm0 (at_ .edx 0), .mov .ecx (.imm 0), .alu .sub .ecx (.mem (at_ .edx 0)),
   .mov .edx (.imm 1), .alu .sbb .edx (.imm 0)]

set_option simprocs false in
/-- The nonce into `xmm0`, and `2³² − c` into `edx:ecx`. -/
theorem nonceLoad1_ok {s : State} {np : Addr} (hen : (s.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = np)
    (h16 : InRegions (s.rd ++ s.wr) np 16) (h4 : InRegions (s.rd ++ s.wr) np 4) :
    WP isa (.block nonceLoad1) s fun s' => Pair s' (2 ^ 32 - (s.mem.readW np 32).toNat) ∧
      s'.xmm .xmm0 = s.mem.readW np 128 ∧ (∀ x, x ≠ .xmm0 → s'.xmm x = s.xmm x) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nonceLoad1, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.ea, at_, State.load32, State.load128, State.setReg, State.setXmm,
    State.setFlags, hen, h16, h4, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', ite_true, ite_false, Pair]
  refine ⟨?_, trivial, fun x hx => by simp [hx], fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩
  have hc := (s.mem.readW np 32).isLt
  generalize s.mem.readW np 32 = c at *
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  by_cases h0 : (0 : BitVec 32).toNat < c.toNat
  · simp only [h0, decide_true, Bool.toNat_true]; simp at h0 ⊢; omega
  · simp only [h0, decide_false, Bool.toNat_false]; simp at h0 ⊢; omega

theorem nonceLoads_eq : nonceLoads = nonceLoad1 ++ (dbl ++ (dbl ++ (dbl ++ (dbl ++ (dbl ++ dbl))))) := rfl

theorem dbl_then {l : List Instr} {s : State} {x : Nat} (h : Pair s x) (hx : 2 * x < 2 ^ 64) {Q : State → Prop}
    (k : ∀ s', Pair s' (2 * x) → Keep s s' → WP isa (.block l) s' Q) : WP isa (.block (dbl ++ l)) s Q :=
  WP.block_append_iff.mpr (WP.mono (dbl_ok h hx) fun s' ⟨h₁, h₂⟩ => k s' h₁ h₂)

/-- `edx:ecx` = `v`, word by word. -/
theorem pair_eq {s : State} {v : Nat} (h : Pair s v) (hv : v < 2 ^ 64) :
    s.gpr .ecx = BitVec.ofNat 32 v ∧ s.gpr .edx = BitVec.ofNat 32 (v / 2 ^ 32) := by
  have ha := (s.gpr .ecx).isLt
  have hb := (s.gpr .edx).isLt
  simp only [Pair] at h
  constructor <;> apply BitVec.eq_of_toNat_eq <;> rw [BitVec.toNat_ofNat] <;> omega

/-- What the loads of `set_nonce` leave: the nonce in `xmm0`, and the number
of bytes left in `edx:ecx`. -/
structure Loaded (s : State) (np : Addr) (s' : State) : Prop where
  xmm0 : s'.xmm .xmm0 = s.mem.readW np 128
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (V (s.mem.readW np 32))
  edx : s'.gpr .edx = BitVec.ofNat 32 (V (s.mem.readW np 32) / 2 ^ 32)
  xmm : ∀ x, x ≠ .xmm0 → s'.xmm x = s.xmm x
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonceLoads_ok {s : State} {np : Addr} (hen : (s.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = np)
    (h16 : InRegions (s.rd ++ s.wr) np 16) (h4 : InRegions (s.rd ++ s.wr) np 4) :
    WP isa (.block nonceLoads) s (Loaded s np) := by
  have hc := (s.mem.readW np 32).isLt
  rw [nonceLoads_eq]
  refine WP.block_append_iff.mpr (WP.mono (nonceLoad1_ok hen h16 h4) fun s₁ ⟨p₁, x₁, xs₁, g₁, m₁, r₁, w₁⟩ => ?_)
  refine dbl_then p₁ (by omega) fun s₂ p₂ k₂ => dbl_then p₂ (by omega) fun s₃ p₃ k₃ =>
    dbl_then p₃ (by omega) fun s₄ p₄ k₄ => dbl_then p₄ (by omega) fun s₅ p₅ k₅ =>
    dbl_then p₅ (by omega) fun s₆ p₆ k₆ => ?_
  refine WP.mono (dbl_ok p₆ (by omega)) fun s₇ ⟨p₇, k₇⟩ => ?_
  have k := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇
  have e : 2 * (2 * (2 * (2 * (2 * (2 * (2 ^ 32 - (s.mem.readW np 32).toNat)))))) = V (s.mem.readW np 32) := by
    simp only [V]; omega
  rw [e] at p₇
  have ⟨hecx, hedx⟩ := pair_eq p₇ (by have := V_lt (s.mem.readW np 32); omega)
  exact ⟨by rw [k.xmm, x₁], hecx, hedx, fun x hx => by rw [k.xmm, xs₁ x hx],
    fun r a b => by rw [k.gpr r a b, g₁ r a b], by rw [k.mem, m₁], by rw [k.rd, r₁], by rw [k.wr, w₁]⟩

/-! ## The stores -/

/-- The constants (RFC 8439 §2.3), as little-endian words. -/
def k0 : BitVec 32 := 0x61707865
def k1 : BitVec 32 := 0x3320646e
def k2 : BitVec 32 := 0x79622d32
def k3 : BitVec 32 := 0x6b206574

/-- The memory `set_nonce` leaves, from `m`, for the state at `st`, the
nonce `n` and the number of bytes left `lo`, `hi`. -/
def nonceMem (m : Mem) (st : Addr) (n : BitVec 128) (lo hi : BitVec 32) : Mem :=
  ((((((m.writeW (st + BitVec.ofNat 64 48) n).writeW (st + BitVec.ofNat 64 128) lo).writeW
    (st + BitVec.ofNat 64 132) hi).writeW (st + BitVec.ofNat 64 0) k0).writeW (st + BitVec.ofNat 64 4) k1).writeW
    (st + BitVec.ofNat 64 8) k2).writeW (st + BitVec.ofNat 64 12) k3

/-- What the stores need: the state at `ST` in `eax`, writable. -/
structure SPre (s : State) (ST : BitVec 32) : Prop where
  eax : s.gpr .eax = ST
  fit : ST.toNat + 768 ≤ 2 ^ 32
  w : ∀ d n, d + n ≤ 768 → InRegions s.wr (ST.setWidth 64 + BitVec.ofNat 64 d) n

theorem SPre.ea {s : State} {ST : BitVec 32} (h : SPre s ST) {d : Nat} (hd : d < 768) :
    (ST + BitVec.ofNat 32 d).setWidth 64 = ST.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.fit; omega)

set_option simprocs false in
theorem nonceStores_ok {s : State} {ST : BitVec 32} (hp : SPre s ST) :
    WP isa (.block nonceStores) s fun s' =>
      s'.mem = nonceMem s.mem (ST.setWidth 64) (s.xmm .xmm0) (s.gpr .ecx) (s.gpr .edx) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 := hp.ea (d := 0) (by decide); have e4 := hp.ea (d := 4) (by decide)
  have e8 := hp.ea (d := 8) (by decide); have e12 := hp.ea (d := 12) (by decide)
  have e48 := hp.ea (d := 48) (by decide); have e128 := hp.ea (d := 128) (by decide)
  have e132 := hp.ea (d := 132) (by decide)
  have o0 := hp.w 0 4 (by decide); have o4 := hp.w 4 4 (by decide)
  have o8 := hp.w 8 4 (by decide); have o12 := hp.w 12 4 (by decide)
  have o48 := hp.w 48 16 (by decide); have o128 := hp.w 128 4 (by decide)
  have o132 := hp.w 132 4 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nonceStores, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.ea, at_, State.store32, State.store128, State.setReg, hp.eax, e0, e4, e8, e12, e48, e128,
    e132, o0, o4, o8, o12, o48, o128, o132, Option.map_some, Option.some.injEq,
    exists_eq_left', ite_true, ite_false]
  exact ⟨rfl, fun r h => by simp [h], trivial⟩

/-! ## What the stores leave -/

/-- Reading a 32- or 64-bit word after writing a 32-bit word elsewhere, at
offsets from `p`. -/
theorem readW_ofNat32 (m : Mem) (p : Addr) {w : Nat} (v : BitVec 32) {d e : Nat}
    (h : d + w / 8 ≤ e ∨ e + 4 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hw : w ≤ 64) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) w = m.readW (p + BitVec.ofNat 64 d) w :=
  readW_writeW_ofNat m p v h (by omega) (by omega) (by omega)

theorem k_bytes : ∀ j < 16, ([k0, k1, k2, k3].getD (j / 4) 0).extractLsb' (8 * (j % 4)) 8 = sigma.getD j 0 := by
  decide

set_option simprocs false in
/-- The constants' words. -/
theorem nonceMem_k (m : Mem) (st : Addr) (n : BitVec 128) (lo hi : BitVec 32) {k : Nat} (hk : k < 4) :
    (nonceMem m st n lo hi).readW (st + BitVec.ofNat 64 (4 * k)) 32 = [k0, k1, k2, k3].getD k 0 := by
  simp only [nonceMem]
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_ofNat32,
    List.getD_cons_zero, List.getD_cons_succ]

/-- What `set_nonce` leaves, for the nonce `N` (the bytes of `n`) and the
number of bytes left for it. -/
theorem nonceMem_post (m : Mem) (st : Addr) {N : List Byte} {n : BitVec 128}
    (hN : ∀ i < 16, n.extractLsb' (8 * i) 8 = N.getD i 0) :
    keyAt (nonceMem m st n (BitVec.ofNat 32 (V (wordLE N 0))) (BitVec.ofNat 32 (V (wordLE N 0) / 2 ^ 32))) st =
        keyAt m st ∧
      restAt (nonceMem m st n (BitVec.ofNat 32 (V (wordLE N 0))) (BitVec.ofNat 32 (V (wordLE N 0) / 2 ^ 32))) st =
        keystreamOf (keyAt m st) N := by
  have hv := V_lt (wordLE N 0)
  refine stream_of_parts (by simp [keyAt, length_bytesAt]) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) ?_
  · rw [byte_of_words32 (a := 0) (b := 4) (W := fun k => [k0, k1, k2, k3].getD k 0)
      (fun k _ hk => nonceMem_k m st n _ _ hk) (Nat.zero_le _) (by omega)]
    exact k_bytes i hi
  · simp only [nonceMem]
    rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), keyAt,
      show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl, bytesAt_getD _ _ hi, Offset.add_add]
  · simp only [nonceMem]
    rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      ← Offset.add_add st 48 i, byte_writeW_self _ _ _ (by omega) (by omega), hN i hi]
  · simp only [leftAt, nonceMem]
    rw [show (st + 128 : Addr) = st + BitVec.ofNat 64 128 from rfl,
      readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
      readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
      readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
      readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
      show (132 : Nat) = 128 + 4 from rfl, readW64_halves _ _ _ (by decide), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]

/-- The stores of `set_nonce` write only the state. -/
theorem nonceMem_frame (m : Mem) (st : Addr) (n : BitVec 128) (lo hi : BitVec 32) :
    Frame [⟨st, 768⟩] m (nonceMem m st n lo hi) := by
  have c : ∀ d w, d + w / 8 ≤ 768 → (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) (w / 8) :=
    fun d w hd => contains_off hd (by omega)
  simp only [nonceMem]
  exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 48 128 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 128 32 (by decide))).writeW (List.mem_singleton_self _) _
    (c 132 32 (by decide))).writeW (List.mem_singleton_self _) _ (c 0 32 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 4 32 (by decide))).writeW (List.mem_singleton_self _) _
    (c 8 32 (by decide))).writeW (List.mem_singleton_self _) _ (c 12 32 (by decide)))

/-! ## The arguments -/

/-- The words of the arguments are in their region. -/
theorem arg_in (s : State) {n : Nat} (hfit : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {i : Nat} (hi : i < n) :
    (⟨argAddr s 0, 4 * n⟩ : Region).Contains (argAddr s i) 4 := by
  have e : ∀ d, d < 4 + 4 * n → addr (s.gpr .esp) d = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 d :=
    fun d hd => addr_eq (by omega)
  rw [show argAddr s i = addr (s.gpr .esp) (4 + 4 * i) from rfl, e _ (by omega),
    show argAddr s 0 = addr (s.gpr .esp) 4 from rfl, e _ (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

/-! ## `set_nonce` -/

section
variable (s₀ : State)
abbrev ST : BitVec 32 := arg s₀ 0
abbrev st : Addr := (ST s₀).setWidth 64
end

structure NPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨(arg s₀ 1).setWidth 64, 16⟩, ⟨argAddr s₀ 0, 8⟩]
  wr : s₀.wr = [⟨st s₀, 768⟩]
  st_n : (⟨st s₀, 768⟩ : Region).Disjoint ⟨(arg s₀ 1).setWidth 64, 16⟩
  a_st : (⟨argAddr s₀ 0, 8⟩ : Region).Disjoint ⟨st s₀, 768⟩
  ret_st : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨st s₀, 768⟩
  st_fit : (ST s₀).toNat + 768 ≤ 2 ^ 32
  n_fit : (arg s₀ 1).toNat + 16 ≤ 2 ^ 32
  sp_hi : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem NPre.of (s₀ : State) (h : Proof.ChaCha20.setNonceX86.pre s₀) : NPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The memory `set_nonce` leaves, from `m`, for the state at `st` and the
nonce at `np`. -/
abbrev setNonceMem (m : Mem) (st np : Addr) : Mem :=
  nonceMem m st (m.readW np 128) (BitVec.ofNat 32 (V (m.readW np 32)))
    (BitVec.ofNat 32 (V (m.readW np 32) / 2 ^ 32))

set_option simprocs false in
theorem setNonceArgs_ok {s : State} (hp : NPre s) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4)), .mov .edx (.mem (at_ .esp 8))]) s fun s' =>
      s'.gpr .eax = ST s ∧ s'.gpr .edx = arg s 1 ∧ (∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.xmm = s.xmm ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i₀ : InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    ⟨_, by rw [hp.rd]; simp, arg_in s (n := 2) (by have := hp.sp_hi; omega) (i := 0) (by decide)⟩
  have i₁ : InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    ⟨_, by rw [hp.rd]; simp, arg_in s (n := 2) (by have := hp.sp_hi; omega) (i := 1) (by decide)⟩
  have v₀ : s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = arg s 0 := rfl
  have v₁ : s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = arg s 1 := rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
    at_, State.load32, State.setReg, i₀, i₁, v₀, v₁, Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, ite_false]
  exact ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩

theorem setNonce_eq : setNonce = .block (([.mov .eax (.mem (at_ .esp 4)), .mov .edx (.mem (at_ .esp 8))] ++
    nonceLoads) ++ nonceStores) := rfl

theorem setNonce_exec {s : State} (hp : NPre s) :
    WP isa setNonce s fun s' => s'.mem = setNonceMem s.mem (st s) ((arg s 1).setWidth 64) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hn : ∀ n, n ≤ 16 → InRegions (s.rd ++ s.wr) ((arg s 1).setWidth 64) n := fun n hn =>
    ⟨⟨(arg s 1).setWidth 64, 16⟩, by rw [hp.rd]; simp, by simp [Region.Contains]; omega⟩
  rw [setNonce_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setNonceArgs_ok hp) fun s₁ ⟨a₁, d₁, g₁, x₁, m₁, r₁, w₁⟩ => ?_
  refine WP.mono (nonceLoads_ok (np := (arg s 1).setWidth 64) (by rw [d₁]; simp)
    (by rw [r₁, w₁]; exact hn 16 (by decide)) (by rw [r₁, w₁]; exact hn 4 (by decide))) fun s₂ h₂ => ?_
  have hS : SPre s₂ (ST s) := ⟨by rw [h₂.gpr _ (by decide) (by decide), a₁], hp.st_fit, fun d n hd => by
    rw [h₂.wr, w₁, hp.wr]; exact ⟨_, List.mem_singleton_self _, contains_off hd (by omega)⟩⟩
  refine WP.mono (nonceStores_ok hS) fun s₃ ⟨m₃, g₃, _, _, _⟩ => ⟨?_, fun r a c d => ?_⟩
  · rw [m₃, h₂.mem, h₂.xmm0, h₂.ecx, h₂.edx, m₁]
  · rw [g₃ r c, h₂.gpr r c d, g₁ r a d]

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The nonce `set_nonce` reads, byte by byte. -/
theorem nonce_bytes (m : Mem) (np : Addr) :
    ∀ i < 16, (m.readW np 128).extractLsb' (8 * i) 8 = (bytesAt m np 16).getD i 0 :=
  fun i hi => by rw [readW128_byte _ _ hi, bytesAt_getD _ _ hi]

theorem setNonceMem_post (m : Mem) (st np : Addr) :
    keyAt (setNonceMem m st np) st = keyAt m st ∧
      restAt (setNonceMem m st np) st = keystreamOf (keyAt m st) (bytesAt m np 16) := by
  have := nonceMem_post m st (nonce_bytes m np)
  rwa [wordLE_bytesAt _ _ (by decide)] at this

theorem setNonce_ok (s : State) (hs : Proof.ChaCha20.setNonceX86.pre s) :
    ∃ t s', Exec isa setNonce s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.setNonceX86.post s s' := by
  have hp := NPre.of s hs
  obtain ⟨t, s', he, hm, hg⟩ := setNonce_exec hp
  refine ⟨t, s', he, ⟨fun r hr => hg r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.1 (calleeSaved_ne hr).2.2, ?_⟩,
    ?_⟩
  · rw [hm]
    exact (nonceMem_frame _ _ _ _ _).readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · simp only [Proof.ChaCha20.setNonceX86]; rw [hm]; exact setNonceMem_post _ _ _

/-- The initial taint of `set_nonce`: `esp` is public, and so are the 12
bytes above it (the return address and the two pointer arguments), which
no store changes. -/
def τN : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 12 }

theorem wfN {s : State} (hp : NPre s) : VG.X86.Taint.Wf τN s := by
  have hs := hp.sp_hi
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) (by simpa using hp.ret_st)
    (by simpa [argAddr, addr] using hp.a_st)

theorem agreeN {s₁ s₂ : State} (h₁ : Proof.ChaCha20.setNonceX86.pre s₁)
    (h₂ : Proof.ChaCha20.setNonceX86.pre s₂) (hpub : Proof.ChaCha20.setNonceX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τN s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := NPre.of _ h₁; have hp₂ := NPre.of _ h₂
  have f₁ : (s₁.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₁.sp_hi
  have f₂ : (s₂.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₂.sp_hi
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wfN hp₁, wfN hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τN, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [τN] at hk
    rw [show VG.X86.Taint.depth τN.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem setNonce_ct : ConstantTime isa Proof.ChaCha20.setNonceX86.pre Proof.ChaCha20.setNonceX86.pub setNonce :=
  VG.Taint.constantTime (A := sseTaint) τN (fun _ _ h₁ h₂ hpub => agreeN h₁ h₂ hpub)
    (by taint_decide)

/-- Memory whose argument slots (at `0x4004`) hold `0x1000`, `0x2000` and
`0x3000`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0

/-- A state satisfying the precondition of `set_nonce`. -/
def setNonceSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 16⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x1000, 768⟩]

theorem setNonce_verified : Verified X86.target setNonce (Spec.ChaCha20.setNonceContract X86.abi) :=
  Verified.of_correct setNonce_ok setNonce_ct (by
    have a0 : arg setNonceSat 0 = 0x1000 := by decide
    have a1 : arg setNonceSat 1 = 0x2000 := by decide
    have e : argAddr setNonceSat 0 = 0x4004 := by decide
    have esp : setNonceSat.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.setNonceContract, Spec.ChaCha20.setNonceSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.setNonceX86] [a0, a1, e, esp] using setNonceSat)

/-! ## `init` -/

structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨(arg s₀ 1).setWidth 64, 32⟩, ⟨(arg s₀ 2).setWidth 64, 16⟩, ⟨argAddr s₀ 0, 12⟩]
  wr : s₀.wr = [⟨st s₀, 768⟩]
  st_k : (⟨st s₀, 768⟩ : Region).Disjoint ⟨(arg s₀ 1).setWidth 64, 32⟩
  st_n : (⟨st s₀, 768⟩ : Region).Disjoint ⟨(arg s₀ 2).setWidth 64, 16⟩
  a_st : (⟨argAddr s₀ 0, 12⟩ : Region).Disjoint ⟨st s₀, 768⟩
  ret_st : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨st s₀, 768⟩
  st_fit : (ST s₀).toNat + 768 ≤ 2 ^ 32
  k_fit : (arg s₀ 1).toNat + 32 ≤ 2 ^ 32
  n_fit : (arg s₀ 2).toNat + 16 ≤ 2 ^ 32
  sp_hi : (s₀.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem IPre.of (s₀ : State) (h : Proof.ChaCha20.initX86.pre s₀) : IPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

def initLoads : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8)), .movdquLoad .xmm1 (at_ .ecx 0),
    .movdquLoad .xmm2 (at_ .ecx 16), .mov .edx (.mem (at_ .esp 12))]

def keyStores : List Instr := [.movdquStore (at_ .eax 16) .xmm1, .movdquStore (at_ .eax 32) .xmm2]

theorem init_eq : init = .block (((initLoads ++ nonceLoads) ++ keyStores) ++ nonceStores) := rfl

set_option simprocs false in
theorem initLoads_ok {s : State} (hp : IPre s) :
    WP isa (.block initLoads) s fun s' =>
      s'.gpr .eax = ST s ∧ s'.gpr .edx = arg s 2 ∧
      s'.xmm .xmm1 = s.mem.readW ((arg s 1).setWidth 64) 128 ∧
      s'.xmm .xmm2 = s.mem.readW ((arg s 1).setWidth 64 + BitVec.ofNat 64 16) 128 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hf : (s.gpr .esp).toNat + 4 + 4 * 3 ≤ 2 ^ 32 := by have := hp.sp_hi; omega
  have i₀ : InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    ⟨_, by rw [hp.rd]; simp, arg_in s (n := 3) hf (i := 0) (by decide)⟩
  have i₁ : InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    ⟨_, by rw [hp.rd]; simp, arg_in s (n := 3) hf (i := 1) (by decide)⟩
  have i₂ : InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 4 :=
    ⟨_, by rw [hp.rd]; simp, arg_in s (n := 3) hf (i := 2) (by decide)⟩
  have v₀ : s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = arg s 0 := rfl
  have v₁ : s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = arg s 1 := rfl
  have v₂ : s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 32 = arg s 2 := rfl
  have k₀ : (arg s 1 + BitVec.ofNat 32 0).setWidth 64 = (arg s 1).setWidth 64 := by simp
  have k₁₆ : (arg s 1 + BitVec.ofNat 32 16).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 16 :=
    addr_eq (by have := hp.k_fit; omega)
  have j₀ : InRegions (s.rd ++ s.wr) ((arg s 1).setWidth 64) 16 :=
    ⟨⟨(arg s 1).setWidth 64, 32⟩, by rw [hp.rd]; simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
  have j₁₆ : InRegions (s.rd ++ s.wr) ((arg s 1).setWidth 64 + BitVec.ofNat 64 16) 16 :=
    ⟨⟨(arg s 1).setWidth 64, 32⟩, by rw [hp.rd]; simp, contains_off (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [initLoads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, State.load128, State.setReg, State.setXmm, i₀, i₁, i₂, v₀, v₁, v₂, k₀, k₁₆,
    j₀, j₁₆, Option.map_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  exact ⟨trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

/-- The memory after the key is stored. -/
def keyMem (m : Mem) (st : Addr) (a b : BitVec 128) : Mem :=
  (m.writeW (st + BitVec.ofNat 64 16) a).writeW (st + BitVec.ofNat 64 32) b

set_option simprocs false in
theorem keyStores_ok {s : State} {ST : BitVec 32} (hp : SPre s ST) :
    WP isa (.block keyStores) s fun s' =>
      s'.mem = keyMem s.mem (ST.setWidth 64) (s.xmm .xmm1) (s.xmm .xmm2) ∧ s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 := hp.ea (d := 16) (by decide); have e32 := hp.ea (d := 32) (by decide)
  have o16 := hp.w 16 16 (by decide); have o32 := hp.w 32 16 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [keyStores, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, at_, State.store128, hp.eax, e16, e32, o16, o32, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨rfl, trivial⟩

theorem keyMem_frame (m : Mem) (st : Addr) (a b : BitVec 128) : Frame [⟨st, 768⟩] m (keyMem m st a b) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))

/-- The key `init` stores. -/
theorem keyMem_key (m : Mem) (st kp : Addr) :
    keyAt (keyMem m st (m.readW kp 128) (m.readW (kp + BitVec.ofNat 64 16) 128)) st = bytesAt m kp 32 := by
  apply List.ext_getElem
  · simp [keyAt, length_bytesAt]
  · intro i h₁ h₂
    simp only [keyAt, length_bytesAt] at h₁
    rw [getElem_eq_getD, getElem_eq_getD, keyAt, show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl,
      bytesAt_getD _ _ h₁, bytesAt_getD _ _ h₁, keyMem]
    rw [Offset.add_add]
    by_cases h : i < 16
    · rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), ← Offset.add_add st 16 i,
        byte_writeW_self _ _ _ (by omega) (by omega), readW128_byte _ _ h]
    · rw [show 16 + i = 32 + (i - 16) by omega, ← Offset.add_add st 32 (i - 16),
        byte_writeW_self _ _ _ (by omega) (by omega), readW128_byte _ _ (by omega), Offset.add_add,
        show 16 + (i - 16) = i by omega]

/-- The memory `init` leaves, from `m`, for the state at `st`, the key at
`kp` and the nonce at `np`. -/
abbrev initMem (m : Mem) (st kp np : Addr) : Mem :=
  nonceMem (keyMem m st (m.readW kp 128) (m.readW (kp + BitVec.ofNat 64 16) 128)) st (m.readW np 128)
    (BitVec.ofNat 32 (V (m.readW np 32))) (BitVec.ofNat 32 (V (m.readW np 32) / 2 ^ 32))

theorem init_exec {s : State} (hp : IPre s) :
    WP isa init s fun s' => s'.mem = initMem s.mem (st s) ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hn : ∀ n, n ≤ 16 → InRegions (s.rd ++ s.wr) ((arg s 2).setWidth 64) n := fun n hn =>
    ⟨⟨(arg s 2).setWidth 64, 16⟩, by rw [hp.rd]; simp, by simp [Region.Contains]; omega⟩
  have hw : ∀ d n, d + n ≤ 768 → InRegions s.wr ((ST s).setWidth 64 + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [hp.wr]; exact ⟨_, List.mem_singleton_self _, contains_off hd (by omega)⟩
  rw [init_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (initLoads_ok hp) fun s₁ ⟨a₁, d₁, x₁, y₁, g₁, m₁, r₁, w₁⟩ => ?_
  refine WP.mono (nonceLoads_ok (np := (arg s 2).setWidth 64) (by rw [d₁]; simp)
    (by rw [r₁, w₁]; exact hn 16 (by decide)) (by rw [r₁, w₁]; exact hn 4 (by decide))) fun s₂ h₂ => ?_
  have hS : SPre s₂ (ST s) := ⟨by rw [h₂.gpr _ (by decide) (by decide), a₁], hp.st_fit, fun d n hd => by
    rw [h₂.wr, w₁]; exact hw d n hd⟩
  refine WP.mono (keyStores_ok hS) fun s₃ ⟨m₃, g₃, x₃, r₃, w₃⟩ => ?_
  have hS' : SPre s₃ (ST s) := ⟨by rw [g₃]; exact hS.eax, hp.st_fit, fun d n hd => by rw [w₃]; exact hS.w d n hd⟩
  refine WP.mono (nonceStores_ok hS') fun s₄ ⟨m₄, g₄, _, _, _⟩ => ⟨?_, fun r a c d => ?_⟩
  · rw [m₄, m₃, x₃, g₃, h₂.mem, h₂.xmm0, h₂.ecx, h₂.edx, h₂.xmm _ (by decide), h₂.xmm _ (by decide), x₁, y₁, m₁]
  · rw [g₄ r c, g₃, h₂.gpr r c d, g₁ r a c d]

theorem init_ok (s : State) (hs : Proof.ChaCha20.initX86.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.initX86.post s s' := by
  have hp := IPre.of s hs
  obtain ⟨t, s', he, hm, hg⟩ := init_exec hp
  refine ⟨t, s', he, ⟨fun r hr => hg r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.1 (calleeSaved_ne hr).2.2, ?_⟩,
    ?_⟩
  · rw [hm]
    exact ((keyMem_frame _ _ _ _).trans (nonceMem_frame _ _ _ _ _)).readW (Region.contains_self _ _)
      (by simpa using hp.ret_st) (by decide)
  · have hN := nonceMem_post (keyMem s.mem (st s) (s.mem.readW ((arg s 1).setWidth 64) 128)
      (s.mem.readW ((arg s 1).setWidth 64 + BitVec.ofNat 64 16) 128)) (st s)
      (nonce_bytes s.mem ((arg s 2).setWidth 64))
    rw [wordLE_bytesAt _ _ (by decide), keyMem_key] at hN
    simp only [Proof.ChaCha20.initX86]; rw [hm]; exact hN

/-- The initial taint of `init`: `esp` is public, and so are the 16 bytes
above it (the return address and the three pointer arguments). -/
def τI : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16 }

theorem wfI {s : State} (hp : IPre s) : VG.X86.Taint.Wf τI s := by
  have hs := hp.sp_hi
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) (by simpa using hp.ret_st)
    (by simpa [argAddr, addr] using hp.a_st)

theorem agreeI {s₁ s₂ : State} (h₁ : Proof.ChaCha20.initX86.pre s₁)
    (h₂ : Proof.ChaCha20.initX86.pre s₂) (hpub : Proof.ChaCha20.initX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τI s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2⟩ := hpub
  have hp₁ := IPre.of _ h₁; have hp₂ := IPre.of _ h₂
  have f₁ : (s₁.gpr .esp).toNat + 16 ≤ 2 ^ 32 := hp₁.sp_hi
  have f₂ : (s₂.gpr .esp).toNat + 16 ≤ 2 ^ 32 := hp₂.sp_hi
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wfI hp₁, wfI hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τI, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [τI] at hk
    rw [show VG.X86.Taint.depth τI.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

theorem init_ct : ConstantTime isa Proof.ChaCha20.initX86.pre Proof.ChaCha20.initX86.pub init :=
  VG.Taint.constantTime (A := sseTaint) τI (fun _ _ h₁ h₂ hpub => agreeI h₁ h₂ hpub) (by taint_decide)

/-- A state satisfying the precondition of `init`. -/
def initSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 16⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x1000, 768⟩]

theorem init_verified : Verified X86.target init (Spec.ChaCha20.initContract X86.abi) :=
  Verified.of_correct init_ok init_ct (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 0x2000 := by decide
    have a2 : arg initSat 2 = 0x3000 := by decide
    have e : argAddr initSat 0 = 0x4004 := by decide
    have esp : initSat.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.initContract, Spec.ChaCha20.initSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.initX86] [a0, a1, a2, e, esp] using initSat)

end VG.Proof.ChaCha20.X86.Stream
