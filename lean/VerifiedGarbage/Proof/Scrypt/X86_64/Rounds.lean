import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
import VerifiedGarbage.Proof.Scrypt.Spec

/-!
# The Salsa20/8 Core on x86-64: the rounds

Untrusted: everything here is checked by Lean.
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
  simp only [Region.Contains, bufAt, ofInt_natCast]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (bufAt p d) n (bufAt p e) k := by
  intro x hx hy
  simp only [bufAt, ofInt_natCast] at hx hy
  bv_omega

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
