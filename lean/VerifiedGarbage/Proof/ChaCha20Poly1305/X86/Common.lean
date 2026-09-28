import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Proof.Framework.X86.Stack
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev CX : BitVec 32 := arg s₀ 0
abbrev AD : BitVec 32 := arg s₀ 1
abbrev ALN : BitVec 32 := arg s₀ 2
abbrev DP : BitVec 32 := arg s₀ 3
abbrev LN : BitVec 32 := arg s₀ 4
abbrev AL : Nat := (ALN s₀).toNat
abbrev L : Nat := (LN s₀).toNat
abbrev cx : Addr := (CX s₀).setWidth 64
abbrev ad : Addr := (AD s₀).setWidth 64
abbrev dp : Addr := (DP s₀).setWidth 64
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (cx s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (cx s₀ + 32) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (cx s₀ + 48) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
abbrev ctxR : Region := ⟨cx s₀, 1024⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
/-- The stack below the return address that the calls use. -/
abbrev stkR : Region := below (E s₀) 32
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨cx s₀ + BitVec.ofNat 64 k, n⟩
/-- `ctx + k`, as the code computes it. -/
abbrev C32 (k : Nat) : BitVec 32 := CX s₀ + BitVec.ofNat 32 k
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀, argR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  g_c : (argR s₀).Disjoint (ctxR s₀)
  g_a : (argR s₀).Disjoint (aR s₀)
  g_d : (argR s₀).Disjoint (dR s₀)
  ret_c : (retR s₀).Disjoint (ctxR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  stk_c : (stkR s₀).Disjoint (ctxR s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  fit_c : (CX s₀).toNat + 1024 ≤ 2 ^ 32
  fit_a : (AD s₀).toNat + AL s₀ ≤ 2 ^ 32
  fit_d : (DP s₀).toNat + L s₀ ≤ 2 ^ 32
  sp_lo : 32 ≤ (E s₀).toNat
  sp_hi : (E s₀).toNat + 24 ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : preX86 s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-! ## Addresses -/

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `[x + k]`, when it does not wrap. -/
theorem add_setWidth {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 k := addr_eq h

theorem add_toNat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, toNat_ofNat32 (by omega), Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : APre s₀)
include hp

theorem APre.c64 {k : Nat} (hk : k < 1024) : (C32 s₀ k).setWidth 64 = cx s₀ + BitVec.ofNat 64 k :=
  add_setWidth (by have := hp.fit_c; omega)

theorem APre.cNat {k : Nat} (hk : k < 1024) : (C32 s₀ k).toNat = (CX s₀).toNat + k :=
  add_toNat (by have := hp.fit_c; omega)

theorem APre.ea_ctx {d : Nat} (hd : d < 1024) : addr (CX s₀) d = cx s₀ + BitVec.ofNat 64 d :=
  hp.c64 hd

theorem APre.in_ctx {a w : Nat} (h : a + w ≤ 1024) : InRegions s₀.wr (cx s₀ + BitVec.ofNat 64 a) w :=
  ⟨ctxR s₀, by simp [hp.wr], contains_off h (by omega)⟩

theorem APre.in_ctx' {a w : Nat} (h : a + w ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (cx s₀ + BitVec.ofNat 64 a) w :=
  ⟨ctxR s₀, by simp [hp.wr], contains_off h (by omega)⟩

theorem APre.arg_contains {i : Nat} (hi : i < 5) : (argR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp_hi
  simp only [E] at this
  simp only [argR, argAddr]
  rw [show s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i) = (s₀.gpr .esp + BitVec.ofNat 32 4) +
    BitVec.ofNat 32 (4 * i) by rw [BitVec.add_assoc, ← BitVec.ofNat_add],
    add_setWidth (x := s₀.gpr .esp + BitVec.ofNat 32 4) (by rw [add_toNat (by omega)]; omega)]
  exact contains_off (by omega) (by omega)

theorem APre.in_arg {i : Nat} (hi : i < 5) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨argR s₀, by simp [hp.wr], hp.arg_contains hi⟩

theorem APre.E64 {n : Nat} (hn : n ≤ 32) :
    (E s₀ - BitVec.ofNat 32 n).setWidth 64 = (E s₀).setWidth 64 - BitVec.ofNat 64 n :=
  setWidth_sub32 (by have := hp.sp_lo; omega)

end

theorem ea_esp (s : State) (d : Nat) : s.ea (at_ .esp d) = addr (s.gpr .esp) d := rfl

theorem argAddr_eq (s₀ : State) (i : Nat) : argAddr s₀ i = addr (E s₀) (4 + 4 * i) := rfl

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - cx s₀).toNat ≤ (x - (cx s₀ + BitVec.ofNat 64 k)).toNat + k := by
    rw [show x - cx s₀ = (x - (cx s₀ + BitVec.ofNat 64 k)) + BitVec.ofNat 64 k by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := by
  intro x hx
  simp only [Region.Contains] at *
  have e : x - (cx s₀ + BitVec.ofNat 64 a) = (x - (cx s₀ + BitVec.ofNat 64 k)) + BitVec.ofNat 64 (k - a) := by
    rw [show k = a + (k - a) by omega, BitVec.ofNat_add]; bv_omega
  rw [e, BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  exact le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (cx s₀ + BitVec.ofNat 64 a) w := by
  simp only [Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - (cx s₀ + BitVec.ofNat 64 k) = BitVec.ofNat 64 (a - k) by
    rw [show a = k + (a - k) by omega, BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem stk_below (s₀ : State) {n : Nat} (hn : n ≤ 32) (hp : APre s₀) :
    Region.Sub (below (E s₀) n) (stkR s₀) := below_mono hn hp.sp_lo

section
variable {s₀ : State} (hp : APre s₀)
include hp

theorem APre.stk_sub {k n : Nat} (h : k + n ≤ 1024) : (stkR s₀).Disjoint (sub s₀ k n) :=
  hp.stk_c.sub_right (sub_ctx s₀ h)

theorem APre.below_sub {m k n : Nat} (hm : m ≤ 32) (h : k + n ≤ 1024) :
    (below (E s₀) m).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (stk_below s₀ hm hp)

theorem APre.g_sub {k n : Nat} (h : k + n ≤ 1024) : (argR s₀).Disjoint (sub s₀ k n) :=
  hp.g_c.sub_right (sub_ctx s₀ h)

theorem APre.ret_sub {k n : Nat} (h : k + n ≤ 1024) : (retR s₀).Disjoint (sub s₀ k n) :=
  hp.ret_c.sub_right (sub_ctx s₀ h)

theorem APre.d_sub {k n : Nat} (h : k + n ≤ 1024) : (dR s₀).Disjoint (sub s₀ k n) :=
  hp.c_d.symm.sub_right (sub_ctx s₀ h)

theorem APre.a_sub {k n : Nat} (h : k + n ≤ 1024) : (aR s₀).Disjoint (sub s₀ k n) :=
  hp.c_a.symm.sub_right (sub_ctx s₀ h)

/-- The arguments are above the stack the calls use. -/
theorem APre.g_stk : (argR s₀).Disjoint (stkR s₀) := by
  have h₁ := hp.sp_lo
  have h₂ := hp.sp_hi
  simp only [E] at h₁ h₂ ⊢
  intro x hx hy
  simp only [Region.Contains, argAddr] at hx hy
  rw [show s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0) = s₀.gpr .esp + BitVec.ofNat 32 4 from rfl,
    add_setWidth (by omega)] at hx
  have hE : ((s₀.gpr .esp).setWidth 64).toNat = (s₀.gpr .esp).toNat := toNat_setWidth64 _
  generalize (s₀.gpr .esp).setWidth 64 = e at hx hy hE
  bv_omega

theorem APre.ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have h₁ := hp.sp_lo
  simp only [E] at h₁ ⊢
  intro x hx hy
  simp only [Region.Contains] at hx hy
  have hE : ((s₀.gpr .esp).setWidth 64).toNat = (s₀.gpr .esp).toNat := toNat_setWidth64 _
  generalize (s₀.gpr .esp).setWidth 64 = e at hx hy hE
  bv_omega

end

/-! ## Memory -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by omega)))
      (by omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]
    exact h3

/-! ## The saved registers and the invariant -/

/-- Our caller's `ebx, esi, edi, ebp`, saved in `ctx[592, 608)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (cx s₀ + BitVec.ofNat 64 592) 32 = s₀.gpr .ebx ∧
  m.readW (cx s₀ + BitVec.ofNat 64 596) 32 = s₀.gpr .esi ∧
  m.readW (cx s₀ + BitVec.ofNat 64 600) 32 = s₀.gpr .edi ∧
  m.readW (cx s₀ + BitVec.ofNat 64 604) 32 = s₀.gpr .ebp

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 592 16).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 592 ≤ d → d + 4 ≤ 608 → (sub s₀ 592 16).Contains (cx s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hf.readW (c 592 le_rfl (by omega)) hd (by decide), h1],
    by rw [hf.readW (c 596 (by omega) (by omega)) hd (by decide), h2],
    by rw [hf.readW (c 600 (by omega) (by omega)) hd (by decide), h3],
    by rw [hf.readW (c 604 (by omega) (by omega)) hd (by decide), h4]⟩

/-- The working space: `ctx[64, 1024)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 64 960

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  edi : s.gpr .edi = CX s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem s.mem

/-- The arguments are never written. -/
theorem Inv.arg {s₀ s : State} (hp : APre s₀) (h : Inv s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  refine h.frame.readW (hp.arg_contains hi) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.g_sub (by omega)
  · exact hp.g_d
  · exact hp.g_stk

/-- The invariant survives code that keeps `edi` and `esp` and writes only
the working space (not the saved registers), the data and the stack. -/
theorem Inv.step {s₀ s s' : State} (h : Inv s₀ s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 16).Disjoint r) : Inv s₀ s' where
  edi := by rw [hedi, h.edi]
  esp := by rw [hesp, h.esp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## Pointers -/

set_option simprocs false in
theorem ptr_ok (d r : Reg) (k : Nat) (s : State) :
    WP isa (.block (ptr d r k)) s fun s' =>
      s'.gpr d = s.gpr r + BitVec.ofNat 32 k ∧ (∀ q, q ≠ d → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

/-! ## Covering the callees' regions -/

theorem covers_ctx {s₀ : State} (hp : APre s₀) {wr : List Region} (hwr : ctxR s₀ ∈ wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  have _ := hp
  exact ⟨ctxR s₀, hwr, k, by rw [hrk], hk⟩

end VG.Proof.ChaCha20Poly1305.X86
