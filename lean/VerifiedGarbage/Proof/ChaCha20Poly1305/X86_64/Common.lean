import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Calls
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Contract

/-!
# ChaCha20-Poly1305 on x86-64: the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by
  simp only [off]; congr 1

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem signExtend_of_msb {v : BitVec 32} (h : v.msb = false) :
    v.signExtend 64 = BitVec.ofNat 64 v.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false h]
  apply BitVec.eq_of_toNat_eq
  simp

theorem se_ofNat {k : Nat} (h : k < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := by
  rw [signExtend_of_msb (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .rdi
abbrev ad : Addr := s₀.gpr .rsi
abbrev AL : Nat := (s₀.gpr .rdx).toNat
abbrev dp : Addr := s₀.gpr .rcx
abbrev L : Nat := (s₀.gpr .r8).toNat
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
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  ret_c : (retR s₀).Disjoint (ctxR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  stk_c : (⟨s₀.gpr .rsp - 16, 16⟩ : Region).Disjoint (ctxR s₀)
  stk_a : (⟨s₀.gpr .rsp - 16, 16⟩ : Region).Disjoint (aR s₀)
  stk_d : (⟨s₀.gpr .rsp - 16, 16⟩ : Region).Disjoint (dR s₀)
  wrap_c : (cx s₀).toNat + 1024 ≤ 2 ^ 64
  wrap_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : preX86_64 s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem stkR_eq (s₀ : State) : stkR s₀ = ⟨s₀.gpr .rsp - 16, 16⟩ := rfl

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) := by
  rw [sub, off_eq]; exact sub_off _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := by
  intro x h₁ h₂
  simp only [off_eq, Region.Contains] at h₁ h₂
  bv_omega

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := by
  simp only [off_eq, Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - (cx s₀ + BitVec.ofNat 64 k) = BitVec.ofNat 64 (a - k) by
    rw [show a = k + (a - k) by omega, BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 1024) : (ctxR s₀).Contains (off (cx s₀) a) w := by
  simp only [off_eq, Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - cx s₀ = BitVec.ofNat 64 a by bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem APre.in_ctx {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions s₀.wr (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.in_ctx' {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.off_toNat {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 1024) :
    (off (cx s₀) k).toNat = (cx s₀).toNat + k := by
  have := hp.wrap_c
  rw [off_eq, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The stack below `rsp` that the calls use. -/
theorem below8_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) := below_sub (by omega) (by omega)

theorem APre.stk_sub {s₀ : State} (hp : APre s₀) {k n : Nat} (h : k + n ≤ 1024) :
    (stkR s₀).Disjoint (sub s₀ k n) := hp.stk_c.sub_right (sub_ctx s₀ h)

theorem APre.below8_sub {s₀ : State} (hp : APre s₀) {k n : Nat} (h : k + n ≤ 1024) :
    (below (s₀.gpr .rsp) 8).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (below8_stk s₀)

/-! ## The saved registers and the invariant -/

/-- Our caller's `rbx, rbp, r13, r14, r15`, saved in `ctx[592, 632)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (off (cx s₀) 592) 64 = s₀.gpr .rbx ∧ m.readW (off (cx s₀) 600) 64 = s₀.gpr .rbp ∧
  m.readW (off (cx s₀) 608) 64 = s₀.gpr .r13 ∧ m.readW (off (cx s₀) 616) 64 = s₀.gpr .r14 ∧
  m.readW (off (cx s₀) 624) 64 = s₀.gpr .r15

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 592 40).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 592 ≤ d → d + 8 ≤ 632 → (sub s₀ 592 40).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hf.readW (c 592 (Nat.le_refl _) (by omega)) hd (by decide), h1],
    by rw [hf.readW (c 600 (by omega) (by omega)) hd (by decide), h2],
    by rw [hf.readW (c 608 (by omega) (by omega)) hd (by decide), h3],
    by rw [hf.readW (c 616 (by omega) (by omega)) hd (by decide), h4],
    by rw [hf.readW (c 624 (by omega) (by omega)) hd (by decide), h5]⟩

/-- The working space: `ctx[64, 1024)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 64 960

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r8
  r12 : s.gpr .r12 = s₀.gpr .r12
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem s.mem

/-! ## Pointers -/

set_option simprocs false in
theorem ptr_ok (d r : Reg) {k : Nat} (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (ptr d r k)) s fun s' =>
      s'.gpr d = off (s.gpr r) k ∧ (∀ q, q ≠ d → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se_ofNat hk]
  exact ⟨by rw [off_eq], fun q hq => by simp [hq], trivial⟩

set_option simprocs false in
theorem anchor_ok (r : Reg) {k : Nat} (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (anchor r k)) s fun s' =>
      s'.gpr .r15 = s.gpr r - BitVec.ofNat 64 k ∧ (∀ q, q ≠ .r15 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [anchor, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se_ofNat hk]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem off_sub (p : Addr) (k : Nat) : off p k - BitVec.ofNat 64 k = p := by
  rw [off_eq]; exact BitVec.add_sub_cancel _ _

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by simp [hwr, hp.wr], k, by rw [hrk]; simp [off_eq], hk⟩

theorem covers_left {rs wr : List Region} (rd : List Region) (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_nil_append {rs rs' : List Region} (h : Covers rs rs') : Covers ([] ++ rs) rs' := by
  simpa using h

end VG.Proof.ChaCha20Poly1305.X86_64
