import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The Salsa20/8 Core on x86-64: the rounds
-/

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Addresses -/

/-- An address `p + d` as the code computes it. -/
abbrev bufAt (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (bufAt base off) n := by
  simp only [bufAt, ofInt_natCast]; exact Offset.contains_base base h ho

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (bufAt p d) n (bufAt p e) k := by
  simp only [bufAt, ofInt_natCast]; exact Offset.sep p h (by omega) (by omega)

/-- Reading a 32-bit word after writing a (32- or 64-bit) value elsewhere near `p`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e : Nat}
    (hw' : w' = 32 ∨ w' = 64) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + w' / 8 ≤ d) :
    (m.writeW (bufAt p e) v).readW (bufAt p d) 32 = m.readW (bufAt p d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

/-- `scratch`. -/
abbrev scR (p : Addr) : Region := ⟨p, 64⟩
/-- The home slots of words 12–15, at the start of `scratch`. -/
abbrev slotR (p : Addr) : Region := ⟨p, 16⟩

theorem in_sc {rs ws : List Region} {p : Addr} (hw : scR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (bufAt p d) n :=
  ⟨scR p, List.mem_append_right _ hw, contains_off h (by omega)⟩

theorem out_sc {ws : List Region} {p : Addr} (hw : scR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (bufAt p d) n :=
  ⟨scR p, hw, contains_off h (by omega)⟩

/-! ## Registers -/

theorem wreg_ne : ∀ k < 12, wreg k ≠ .rax ∧ wreg k ≠ .rsi ∧ wreg k ≠ .rdi ∧ wreg k ≠ .rsp := by
  decide

theorem wreg_inj : ∀ a < 12, ∀ b < 12, wreg a = wreg b → a = b := by decide

/-! ## One instruction -/

/-- `s'` is `s` with register `d` set to `x` (and possibly the flags changed). -/
structure Upd (d : Reg) (x : BitVec 64) (s s' : State) : Prop where
  gpr : s'.gpr d = x
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem mov32_upd {s : State} {d : Reg} {src : Src} {x : Word} (hr : readSrc32 s src = some x) :
    ∃ s', exec (.mov32 d src) s = some s' ∧ Upd d (x.setWidth 64) s s' := by
  simp only [exec, hr, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [State.setReg32, State.setReg], fun r hr => by simp [State.setReg32, State.setReg, hr],
    rfl, rfl, rfl⟩

theorem add32_upd {s : State} {d : Reg} {src : Src} {x : Word} (hr : readSrc32 s src = some x) :
    ∃ s', exec (.alu32 .add d src) s = some s' ∧
      Upd d (((s.gpr d).setWidth 32 + x).setWidth 64) s s' := by
  simp only [exec, execAlu32, hr, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [State.setReg32, State.setReg],
    fun r hr => by simp [State.setReg32, State.setReg, arithFlags, State.setFlags, hr], rfl, rfl, rfl⟩

theorem xor32_upd {s : State} {d : Reg} {src : Src} {x : Word} (hr : readSrc32 s src = some x) :
    ∃ s', exec (.alu32 .xor d src) s = some s' ∧
      Upd d (((s.gpr d).setWidth 32 ^^^ x).setWidth 64) s s' := by
  simp only [exec, execAlu32, hr, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp only [State.setReg32, State.setReg, ite_true],
    fun r hr => by simp [State.setReg32, State.setReg, arithFlags, State.setFlags, hr], rfl, rfl, rfl⟩

theorem ror32_upd {s : State} {d : Reg} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    ∃ s', exec (.shift32 .ror d n) s = some s' ∧
      Upd d ((((s.gpr d).setWidth 32).rotateRight n).setWidth 64) s s' := by
  simp only [exec, execShift32, h1, h2, and_self, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨by simp only [State.setReg32, State.setReg, ite_true],
    fun r hr => by simp [State.setReg32, State.setReg, State.setFlags, hr], rfl, rfl, rfl⟩

theorem store32_exec {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 4) :
    exec (.store32 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 32) } := by
  simp only [exec, State.store32, h, ite_true]

/-- Running one instruction, then the rest of the block. -/
theorem wp_cons {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {P : State → Prop}
    (he : ∃ s', exec i s = some s' ∧ P s') (hk : ∀ s', P s' → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q := by
  obtain ⟨s', h, hp⟩ := he
  exact WP.block_cons_iff.mpr ⟨s', h, hk s' hp⟩

/-! ## Where the words are -/

/-- The rounds invariant, relative to the state `s₀` at the start of the
rounds: words 0–11 of `v` in their registers, words 12–15 in their slots. -/
structure RI (p : Addr) (v : Vector Word 16) (s₀ s : State) : Prop where
  regs : ∀ k (hk : k < 12), s.gpr (wreg k) = (v[k]'(by omega)).setWidth 64
  slots : ∀ k (hk : k < 16), 12 ≤ k → s.mem.readW (bufAt p (slotOff k)) 32 = v[k]
  frame : Frame [slotR p] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = p
  rdi : s.gpr .rdi = s₀.gpr .rdi
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem RI.upd_rax {p : Addr} {v : Vector Word 16} {s₀ s s' : State} (h : RI p v s₀ s)
    {x : BitVec 64} (hu : Upd .rax x s s') : RI p v s₀ s' where
  regs k hk := (hu.other _ (wreg_ne k hk).1).trans (h.regs k hk)
  slots k hk h12 := hu.mem ▸ h.slots k hk h12
  frame := hu.mem ▸ h.frame
  rd := hu.rd.trans h.rd
  wr := hu.wr.trans h.wr
  rsi := (hu.other _ (by decide)).trans h.rsi
  rdi := (hu.other _ (by decide)).trans h.rdi
  rsp := (hu.other _ (by decide)).trans h.rsp

theorem src_read {p : Addr} {v : Vector Word 16} {s₀ s : State} (h : RI p v s₀ s)
    (hw : scR p ∈ s₀.wr) {k : Nat} (hk : k < 16) : readSrc32 s (src k) = some v[k] := by
  unfold src
  split
  · rename_i hk12
    simp [readSrc32, h.regs k hk12]
  · rename_i hk12
    have hin : InRegions (s.rd ++ s.wr) (bufAt p (slotOff k)) 4 :=
      in_sc (h.wr ▸ hw) (by simp only [slotOff]; omega)
    simp only [readSrc32, ea_at, h.rsi, State.load32, hin, ite_true]
    rw [h.slots k hk (by omega)]

/-! ## One line -/

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

/-- The first three instructions of a line: `eax = R(x[j] + x[k], n)`. -/
theorem sum_ok {p : Addr} {v : Vector Word 16} {s₀ s : State} (h : RI p v s₀ s)
    (hw : scR p ∈ s₀.wr) {i j k n : Nat} (hj : j < 16) (hk : k < 16) (h1 : 1 ≤ n) (h2 : n ≤ 31)
    {Q : State → Prop}
    (hQ : ∀ s', RI p v s₀ s' → s'.gpr .rax = ((v[j] + v[k]).rotateLeft n).setWidth 64 →
      WP isa (.block (if i < 12 then [.alu32 .xor (wreg i) (.reg .rax)]
        else [.alu32 .xor .rax (.mem (at_ .rsi (slotOff i))),
          .store32 (at_ .rsi (slotOff i)) .rax])) s' Q) :
    WP isa (.block (line i j k n)) s Q := by
  rw [line, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_cons (mov32_upd (d := .rax) (src_read h hw hj)) fun s₁ u₁ => ?_
  have h₁ := h.upd_rax u₁
  refine wp_cons (add32_upd (d := .rax) (src_read h₁ hw hk)) fun s₂ u₂ => ?_
  have h₂ := h₁.upd_rax u₂
  refine wp_cons (ror32_upd (d := .rax) (s := s₂) (n := 32 - n) (by omega) (by omega))
    fun s₃ u₃ => ?_
  refine hQ s₃ (h₂.upd_rax u₃) ?_
  rw [u₃.gpr, u₂.gpr, u₁.gpr, rotateLeft_eq _ (by omega) (by omega)]
  simp

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {p : Addr} {v : Vector Word 16}
    {s₀ s : State} (h : RI p v s₀ s) (hw : scR p ∈ s₀.wr) :
    WP isa (.block (line i j k n)) s (RI p (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  refine sum_ok h hw hj hk h1 h2 fun s₃ h₃ hrax => ?_
  have get := stepN_get v n hi hj hk
  split
  · rename_i hi12
    refine wp_cons (xor32_upd (d := wreg i) (s := s₃) (src := .reg .rax) rfl) fun s₄ u₄ => ?_
    refine WP.block_nil ⟨fun m hm => ?_, fun m hm h12 => ?_, u₄.mem ▸ h₃.frame, u₄.rd.trans h₃.rd,
      u₄.wr.trans h₃.wr, (u₄.other _ (wreg_ne i hi12).2.1.symm).trans h₃.rsi,
      (u₄.other _ (wreg_ne i hi12).2.2.1.symm).trans h₃.rdi,
      (u₄.other _ (wreg_ne i hi12).2.2.2.symm).trans h₃.rsp⟩
    · rw [get m (by omega)]
      by_cases e : i = m
      · subst e
        rw [ite_pos' rfl, u₄.gpr, h₃.regs i hi12, hrax]
        simp
      · rw [ite_neg' e, u₄.other _ fun h' => e (wreg_inj i hi12 m hm h'.symm), h₃.regs m hm]
    · rw [get m hm, u₄.mem, ite_neg' (by omega)]
      exact h₃.slots m hm h12
  · rename_i hi12
    have hin : InRegions (s₃.rd ++ s₃.wr) (bufAt p (slotOff i)) 4 :=
      in_sc (h₃.wr ▸ hw) (by simp only [slotOff]; omega)
    have hr : readSrc32 s₃ (.mem (at_ .rsi (slotOff i))) = some v[i] := by
      simp only [readSrc32, ea_at, h₃.rsi, State.load32, hin, ite_true]
      rw [h₃.slots i hi (by omega)]
    refine wp_cons (xor32_upd (d := .rax) hr) fun s₄ u₄ => ?_
    have h₄ := h₃.upd_rax u₄
    have hout : InRegions s₄.wr (s₄.ea (at_ .rsi (slotOff i))) 4 := by
      rw [ea_at, h₄.rsi]; exact out_sc (h₄.wr ▸ hw) (by simp only [slotOff]; omega)
    refine WP.block_cons_iff.mpr ⟨_, store32_exec hout, WP.block_nil ?_⟩
    have hval : (s₄.gpr .rax).setWidth 32 = (stepN v i j k n)[i] := by
      rw [get i hi, ite_pos' rfl, u₄.gpr, hrax]
      simp [BitVec.xor_comm]
    rw [ea_at, h₄.rsi, hval]
    refine ⟨fun m hm => ?_, fun m hm h12 => ?_, ?_, h₄.rd, h₄.wr, h₄.rsi, h₄.rdi, h₄.rsp⟩
    · rw [get m (by omega), ite_neg' (by omega)]
      exact h₄.regs m hm
    · by_cases e : i = m
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega) (by simp only [slotOff]; omega)
          (by simp only [slotOff]; omega) (by simp only [slotOff]; omega), get m hm, ite_neg' e]
        exact h₄.slots m hm h12
    · exact h₄.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega))

/-! ## Double rounds -/

theorem lines_ok {p : Addr} {s₀ : State} (hw : scR p ∈ s₀.wr) :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI p v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI p (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h hw) fun s' h' => lines_ok hw l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {p : Addr} {v : Vector Word 16} {s₀ s : State} (h : RI p v s₀ s)
    (hw : scR p ∈ s₀.wr) : WP isa doubleRound s (RI p (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok hw lines (by decide) v s h

theorem rounds_ok {p : Addr} {v : Vector Word 16} {s₀ : State} (h : RI p v s₀ s₀)
    (hw : scR p ∈ s₀.wr) :
    ∀ n, WP isa (rounds n) s₀ (RI p (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (rounds_ok h hw n) fun _ h' => doubleRound_ok h' hw)

end VG.Proof.Scrypt.X86_64

/-!
# The Salsa20/8 Core on x86-64: loading, finishing, saving and restoring
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.X86_64 in
/-- X86-64 contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32;
16])`: replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` and `scratch` (64 bytes each; the contents of
`scratch` on exit are unspecified), which may not overlap each other or the
return address on the stack. The pointers are public; the data is secret. -/
def salsaX86_64 : Contract X86_64.isa where
  pre s :=
    let b : Region := ⟨s.gpr .rdi, 64⟩
    let scratch : Region := ⟨s.gpr .rsi, 64⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch ∧ ret.Disjoint b ∧ ret.Disjoint scratch
  post s s' := bytesAt s'.mem (s.gpr .rdi) 64 = salsa (bytesAt s.mem (s.gpr .rdi) 64)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .rdi
/-- `scratch`. -/
abbrev sp : Addr := s₀.gpr .rsi
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bufAt (bp s₀) (4 * j.1)) 32
end

abbrev bR (p : Addr) : Region := ⟨p, 64⟩

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR (bp s₀), scR (sp s₀)]
  b_sc : (bR (bp s₀)).Disjoint (scR (sp s₀))
  ret_b : (retR s₀).Disjoint (bR (bp s₀))
  ret_sc : (retR s₀).Disjoint (scR (sp s₀))

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem Pre.hb {s₀ : State} (hp : Pre s₀) : bR (bp s₀) ∈ s₀.wr := by simp [hp.wr]
theorem Pre.hs {s₀ : State} (hp : Pre s₀) : scR (sp s₀) ∈ s₀.wr := by simp [hp.wr]

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bufAt (bp s₀) (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem in_b {rs ws : List Region} {p : Addr} (hw : bR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (bufAt p d) n :=
  ⟨bR p, List.mem_append_right _ hw, contains_off h (by omega)⟩

theorem out_b {ws : List Region} {p : Addr} (hw : bR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (bufAt p d) n :=
  ⟨bR p, hw, contains_off h (by omega)⟩

/-- A part of a region: `[p + d, p + d + n)` inside `[p, p + len)`. -/
theorem sub_off (p : Addr) {len d n : Nat} (h : d + n ≤ len) (_hl : len < 2 ^ 32) :
    Region.Sub ⟨bufAt p d, n⟩ ⟨p, len⟩ := by
  simp only [bufAt, ofInt_natCast]; exact Offset.sub_base p h

/-- Reading `b` after writes to `scratch` only. -/
theorem read_b {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [scR (sp s₀)] s₀.mem m)
    {k : Nat} (hk : k < 16) : m.readW (bufAt (bp s₀) (4 * k)) 32 = (V s₀)[k] := by
  rw [V_get _ hk]
  refine hf.readW (r := ⟨bufAt (bp s₀) (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.b_sc.sub_left (sub_off _ (by omega) (by omega))

/-- Reading `scratch` after writes to `b` only. -/
theorem read_sc {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [bR (bp s₀)] m m')
    {d w : Nat} (hd : d + w / 8 ≤ 64) (hw : w / 8 < 2 ^ 64) :
    m'.readW (bufAt (sp s₀) d) w = m.readW (bufAt (sp s₀) d) w := by
  refine hf.readW (r := ⟨bufAt (sp s₀) d, w / 8⟩) (Region.contains_self _ _) ?_ hw
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.b_sc.symm.sub_left (sub_off _ hd (by omega))

theorem mem_read {s : State} {r : Reg} {d : Nat}
    (hin : InRegions (s.rd ++ s.wr) (bufAt (s.gpr r) d) 4) :
    readSrc32 s (.mem (at_ r d)) = some (s.mem.readW (bufAt (s.gpr r) d) 32) := by
  simp only [readSrc32, ea_at, State.load32, hin, ite_true]

/-! ## Saving the callee-saved registers -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (bufAt (sp s₀) 16) (s₀.gpr .rbx)).writeW (bufAt (sp s₀) 24)
    (s₀.gpr .rbp)).writeW (bufAt (sp s₀) 32) (s₀.gpr .r12)).writeW (bufAt (sp s₀) 40)
    (s₀.gpr .r13)).writeW (bufAt (sp s₀) 48) (s₀.gpr .r14)).writeW (bufAt (sp s₀) 56)
    (s₀.gpr .r15)

/-- The callee-saved registers are saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (bufAt (sp s₀) 16) 64 = s₀.gpr .rbx ∧ m.readW (bufAt (sp s₀) 24) 64 = s₀.gpr .rbp ∧
  m.readW (bufAt (sp s₀) 32) 64 = s₀.gpr .r12 ∧ m.readW (bufAt (sp s₀) 40) 64 = s₀.gpr .r13 ∧
  m.readW (bufAt (sp s₀) 48) 64 = s₀.gpr .r14 ∧ m.readW (bufAt (sp s₀) 56) 64 = s₀.gpr .r15

theorem save_eq : save = [
    .store (at_ .rsi 16) .rbx, .store (at_ .rsi 24) .rbp, .store (at_ .rsi 32) .r12,
    .store (at_ .rsi 40) .r13, .store (at_ .rsi 48) .r14, .store (at_ .rsi 56) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rsi 16)), .mov .rbp (.mem (at_ .rsi 24)), .mov .r12 (.mem (at_ .rsi 32)),
    .mov .r13 (.mem (at_ .rsi 40)), .mov .r14 (.mem (at_ .rsi 48)), .mov .r15 (.mem (at_ .rsi 56))] :=
  rfl

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := out_sc hp.hs (d := 16) (n := 8) (by omega)
  have o1 := out_sc hp.hs (d := 24) (n := 8) (by omega)
  have o2 := out_sc hp.hs (d := 32) (n := 8) (by omega)
  have o3 := out_sc hp.hs (d := 40) (n := 8) (by omega)
  have o4 := out_sc hp.hs (d := 48) (n := 8) (by omega)
  have o5 := out_sc hp.hs (d := 56) (n := 8) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, ea_at, State.store64, o0, o1, o2,
    o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

theorem readW64_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (bufAt p e) v).readW (bufAt p d) 64 = m.readW (bufAt p d) 64 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [scR (sp s₀)] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 64 → (scR (sp s₀)).Contains (bufAt (sp s₀) d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 16 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 24 (by omega))).writeW (List.mem_singleton_self _) _
    (c 32 (by omega))).writeW (List.mem_singleton_self _) _ (c 40 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 48 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 56 (by omega))

/-- The saved registers survive writes to the slots and to `b`. -/
theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m₁ m' : Mem} (h : Saved s₀ m)
    (hf₁ : Frame [slotR (sp s₀)] m m₁) (hf₂ : Frame [bR (bp s₀)] m₁ m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 16 ≤ d → d + 8 ≤ 64 →
      m'.readW (bufAt (sp s₀) d) 64 = m.readW (bufAt (sp s₀) d) 64 := by
    intro d h1 h2
    rw [read_sc hp hf₂ (by omega) (by decide)]
    refine hf₁.readW (r := ⟨bufAt (sp s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr x hx hy
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, bufAt, ofInt_natCast] at hx hy
    bv_omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 16 (by omega) (by omega)).trans h1, (key 24 (by omega) (by omega)).trans h2,
    (key 32 (by omega) (by omega)).trans h3, (key 40 (by omega) (by omega)).trans h4,
    (key 48 (by omega) (by omega)).trans h5, (key 56 (by omega) (by omega)).trans h6⟩

set_option simprocs false in
theorem restore_ok {s₀ : State} {s : State} (hs : Saved s₀ s.mem) (hrsi : s.gpr .rsi = sp s₀)
    (hw : scR (sp s₀) ∈ s.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rsp = s.gpr .rsp ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r := by
  have i0 := in_sc (rs := s.rd) hw (d := 16) (n := 8) (by omega)
  have i1 := in_sc (rs := s.rd) hw (d := 24) (n := 8) (by omega)
  have i2 := in_sc (rs := s.rd) hw (d := 32) (n := 8) (by omega)
  have i3 := in_sc (rs := s.rd) hw (d := 40) (n := 8) (by omega)
  have i4 := in_sc (rs := s.rd) hw (d := 48) (n := 8) (by omega)
  have i5 := in_sc (rs := s.rd) hw (d := 56) (n := 8) (by omega)
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

/-! ## Loading the words -/

/-- The load invariant after `n` words, relative to the state `s₁` after the
prologue's stores. -/
structure LI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ k (hk : k < 12), k < n → s.gpr (wreg k) = ((V s₀)[k]'(by omega)).setWidth 64
  slots : ∀ k (hk : k < 16), 12 ≤ k → k < n → s.mem.readW (bufAt (sp s₀) (slotOff k)) 32 = (V s₀)[k]
  frame : Frame [slotR (sp s₀)] s₁.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = sp s₀
  rdi : s.gpr .rdi = bp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem sub_slot_sc (p : Addr) : ∀ r ∈ [slotR p], ∃ r' ∈ [scR p], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scR p, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hf₁ : Frame [scR (sp s₀)] s₀.mem s₁.mem)
    {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ s₁ n s) :
    WP isa (.block (loadWord n)) s (LI s₀ s₁ (n + 1)) := by
  have hfs : Frame [scR (sp s₀)] s₀.mem s.mem := hf₁.trans (h.frame.sub (sub_slot_sc _))
  have hr : readSrc32 s (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
    rw [mem_read (by rw [h.rdi, h.rd, h.wr]; exact in_b hp.hb (by omega)), h.rdi, read_b hp hfs hn]
  unfold loadWord
  split
  · rename_i hn12
    refine wp_cons (mov32_upd (d := wreg n) hr) fun s' u => WP.block_nil ?_
    have ne := wreg_ne n hn12
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, u.mem ▸ h.frame, u.rd.trans h.rd,
      u.wr.trans h.wr, (u.other _ ne.2.1.symm).trans h.rsi, (u.other _ ne.2.2.1.symm).trans h.rdi,
      (u.other _ ne.2.2.2.symm).trans h.rsp⟩
    · by_cases e : k = n
      · subst e; exact u.gpr
      · rw [u.other _ fun h' => e (wreg_inj k hk n hn12 h'), h.regs k hk (by omega)]
    · rw [u.mem]; exact h.slots k hk h12 (by omega)
  · rename_i hn12
    refine wp_cons (mov32_upd (d := .rax) hr) fun s' u => ?_
    have hout : InRegions s'.wr (s'.ea (at_ .rsi (slotOff n))) 4 := by
      rw [ea_at, u.other _ (by decide), h.rsi, u.wr, h.wr]
      exact out_sc hp.hs (by simp only [slotOff]; omega)
    refine WP.block_cons_iff.mpr ⟨_, store32_exec hout, WP.block_nil ?_⟩
    rw [ea_at, u.other _ (by decide), h.rsi, u.gpr, u.mem]
    have e : ((V s₀)[n].setWidth 64).setWidth 32 = (V s₀)[n] := by simp
    rw [e]
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, ?_, u.rd.trans h.rd, u.wr.trans h.wr,
      (u.other _ (by decide)).trans h.rsi, (u.other _ (by decide)).trans h.rdi,
      (u.other _ (by decide)).trans h.rsp⟩
    · rw [u.other _ (wreg_ne k hk).1]; exact h.regs k hk (by omega)
    · by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega) (by simp only [slotOff]; omega)
          (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]
        exact h.slots k hk h12 (by omega)
    · exact h.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega))

/-! ## Adding the input and storing the result -/

/-- The finish invariant after `n` words: `b` holds `R[j] + V[j]` for the
words `j < n` and still `V[j]` for the others. -/
structure FI (s₀ : State) (R : Vector Word 16) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bufAt (bp s₀) (4 * j)) 32 =
    if j < n then R[j] + (V s₀)[j] else (V s₀)[j]
  regs : ∀ k (hk : k < 12), n ≤ k → s.gpr (wreg k) = (R[k]'(by omega)).setWidth 64
  frame : Frame [bR (bp s₀)] sB.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = sp s₀
  rdi : s.gpr .rdi = bp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {sB : State}
    (hsl : ∀ k (hk : k < 16), 12 ≤ k → sB.mem.readW (bufAt (sp s₀) (slotOff k)) 32 = R[k])
    {n : Nat} (hn : n < 16) {s : State} (h : FI s₀ R sB n s) :
    WP isa (.block (finishWord n)) s (FI s₀ R sB (n + 1)) := by
  have hb : readSrc32 s (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
    rw [mem_read (by rw [h.rdi, h.rd, h.wr]; exact in_b hp.hb (by omega)), h.rdi, h.out n hn]
    simp
  /- After the new sum is stored, the invariant holds. -/
  have fin : ∀ s' : State, s'.mem = s.mem.writeW (bufAt (bp s₀) (4 * n)) (R[n] + (V s₀)[n]) →
      (∀ k (hk : k < 12), n < k → s'.gpr (wreg k) = s.gpr (wreg k)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.gpr .rsi = s.gpr .rsi → s'.gpr .rdi = s.gpr .rdi →
      s'.gpr .rsp = s.gpr .rsp → FI s₀ R sB (n + 1) s' := by
    intro s' hm hg hrd hwr hrsi hrdi hrsp
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr,
      hrsi.trans h.rsi, hrdi.trans h.rdi, hrsp.trans h.rsp⟩
    · rw [hm]
      by_cases e : j = n
      · subst e; rw [Mem.readW_writeW_self32, ite_pos' (by omega)]
      · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega) (by omega), h.out j hj]
        by_cases hjn : j < n
        · rw [ite_pos' hjn, ite_pos' (by omega)]
        · rw [ite_neg' hjn, ite_neg' (by omega)]
    · rw [hg k hk (by omega)]; exact h.regs k hk (by omega)
    · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by omega) (by omega))
  have hout : ∀ s' : State, s'.gpr .rdi = s.gpr .rdi → s'.wr = s.wr →
      InRegions s'.wr (s'.ea (at_ .rdi (4 * n))) 4 := by
    intro s' h1 h2
    rw [ea_at, h1, h2, h.rdi, h.wr]; exact out_b hp.hb (by omega)
  unfold finishWord
  split
  · rename_i hn12
    have ne := wreg_ne n hn12
    refine wp_cons (add32_upd (d := wreg n) hb) fun s' u => ?_
    refine WP.block_cons_iff.mpr ⟨_, store32_exec (hout s' (u.other _ ne.2.2.1.symm) u.wr),
      WP.block_nil (fin _ ?_ ?_ u.rd u.wr (u.other _ ne.2.1.symm) (u.other _ ne.2.2.1.symm)
        (u.other _ ne.2.2.2.symm))⟩
    · simp only [ea_at, u.other _ ne.2.2.1.symm, h.rdi, u.gpr, u.mem, h.regs n hn12 (Nat.le_refl _)]
      simp [bufAt]
    · intro k hk hkn
      exact u.other _ fun e => by have := wreg_inj k hk n hn12 e; omega
  · rename_i hn12
    have hsl' : readSrc32 s (.mem (at_ .rsi (slotOff n))) = some R[n] := by
      rw [mem_read (by rw [h.rsi, h.rd, h.wr]; exact in_sc hp.hs (by simp only [slotOff]; omega)),
        h.rsi, read_sc hp h.frame (by simp only [slotOff]; omega) (by decide), hsl n hn (by omega)]
    refine wp_cons (mov32_upd (d := .rax) hsl') fun s₁ u₁ => ?_
    have hb₁ : readSrc32 s₁ (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
      have hin : InRegions (s₁.rd ++ s₁.wr) (bufAt (s₁.gpr .rdi) (4 * n)) 4 := by
        rw [u₁.other _ (by decide), h.rdi, u₁.rd, u₁.wr, h.rd, h.wr]
        exact in_b hp.hb (by omega)
      rw [mem_read hin, u₁.other _ (by decide), h.rdi, u₁.mem, h.out n hn]
      simp
    refine wp_cons (add32_upd (d := .rax) hb₁) fun s₂ u₂ => ?_
    have e1 : s₂.gpr .rdi = s.gpr .rdi := (u₂.other _ (by decide)).trans (u₁.other _ (by decide))
    refine WP.block_cons_iff.mpr ⟨_, store32_exec (hout s₂ e1 (u₂.wr.trans u₁.wr)),
      WP.block_nil (fin _ ?_ ?_ (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr)
        ((u₂.other _ (by decide)).trans (u₁.other _ (by decide))) e1
        ((u₂.other _ (by decide)).trans (u₁.other _ (by decide))))⟩
    · simp only [ea_at, e1, h.rdi, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
      simp [bufAt]
    · intro k hk _
      rw [u₂.other _ (wreg_ne k hk).1, u₁.other _ (wreg_ne k hk).1]

end VG.Proof.Scrypt.X86_64

/-!
# The Salsa20/8 Core on x86-64: the whole function
-/

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega), bufAt, ofInt_natCast]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bufAt (bp s₀) (4 * j)) 32 =
      (Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀))[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj, bufAt, ofInt_natCast]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Scrypt.salsaX86_64.post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [scR (sp s₀)] s₀.mem s₁.mem := hm₁ ▸ saveMem_frame s₀
  have hl₀ : LI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ h => absurd h (by omega), fun _ _ _ h => absurd h (by omega), Frame.refl _ _, hrd₁,
      hwr₁, by rw [hg₁], by rw [hg₁], by rw [hg₁]⟩
  refine WP.mono (wp_range_flatMap (LI s₀ s₁) (fun k s hk h => load_step hp hf₁ hk h) 16 (Nat.le_refl _)
    s₁ hl₀) fun s₂ hL => ?_
  have hri : RI (sp s₀) (V s₀) s₂ s₂ :=
    ⟨fun k hk => hL.regs k hk (by omega), fun k hk h12 => hL.slots k hk h12 hk, Frame.refl _ _,
      rfl, rfl, hL.rsi, rfl, rfl⟩
  have hw₂ : scR (sp s₀) ∈ s₂.wr := by rw [hL.wr]; exact hp.hs
  refine WP.seq (WP.mono (rounds_ok hri hw₂ 4) fun s₃ hR => ?_)
  rw [WP.block_append_iff]
  have hsc : Frame [slotR (sp s₀)] s₁.mem s₃.mem := hL.frame.trans hR.frame
  have hbf : Frame [scR (sp s₀)] s₀.mem s₃.mem := hf₁.trans (hsc.sub (sub_slot_sc _))
  have hF₀ : FI s₀ (Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)) s₃ 0 s₃ :=
    ⟨fun j hj => by rw [ite_neg' (by omega)]; exact read_b hp hbf hj, fun k hk _ => hR.regs k hk,
      Frame.refl _ _, hR.rd.trans hL.rd, hR.wr.trans hL.wr, hR.rsi, hR.rdi.trans hL.rdi,
      hR.rsp.trans hL.rsp⟩
  refine WP.mono (wp_range_flatMap (FI s₀ _ s₃)
    (fun k s hk h => finish_step hp (fun k hk h12 => hR.slots k hk h12) hk h) 16 (Nat.le_refl _) s₃ hF₀)
    fun s₄ hF => ?_
  have hsaved : Saved s₀ s₄.mem := saved_frame hp (hm₁ ▸ saveMem_saved s₀) hsc hF.frame
  refine WP.mono (restore_ok hsaved hF.rsi (by rw [hF.wr]; exact hp.hs))
    fun s' ⟨hm', hrsp', hg'⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hrsp'.trans hF.rsp
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
  · rw [hm', hF.frame.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_b)
      (by decide)]
    exact hbf.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_sc)
      (by decide)
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 =
      Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    rw [hm']
    exact post_of fun j hj => by simpa [hj] using hF.out j hj

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaX86_64.pre Proof.Scrypt.salsaX86_64.pub
    Impl.Scrypt.X86_64.salsa := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem salsa_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.salsa (Spec.Scrypt.salsaContract X86_64.abi) :=
  Verified.of_correct salsa_correct salsa_ct (by
    sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, Proof.Scrypt.salsaX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Scrypt.X86_64.satState] using Proof.Scrypt.X86_64.satState)

end VG.Proof.Scrypt.X86_64
