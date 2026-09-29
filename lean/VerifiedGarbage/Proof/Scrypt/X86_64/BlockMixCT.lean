import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptBlockMix on x86-64: correctness

Untrusted: everything here is checked by Lean. The calls of `vg_salsa20_8`
are used through `SalsaSpec`, what its proof says about a call; the proof
of this file holds for any code meeting it.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blk salsa blockMix)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ blockMix_eq yAt_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_movm wp_store wp_add wp_addi wp_subi)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem bytesAt_length frame_bytesAt bytesAt_writeBytes_self blk_bytesAt xorBytes_length
  bytesAt_add bytesAt_blocks)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c` replaces the 64 bytes at `rdi` by their Salsa20/8 Core,
with the 64 bytes at `rsi` as working space. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (d sc : Addr), s.gpr .rdi = d → s.gpr .rsi = sc →
    Region.Disjoint ⟨d, 64⟩ ⟨sc, 64⟩ →
    (below (s.gpr .rsp) 8).Disjoint ⟨d, 64⟩ → (below (s.gpr .rsp) 8).Disjoint ⟨sc, 64⟩ →
    d.toNat + 64 ≤ 2 ^ 64 → sc.toNat + 64 ≤ 2 ^ 64 →
    InRegions s.wr d 64 → InRegions s.wr sc 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr →
        (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨d, 64⟩, ⟨sc, 64⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
        bytesAt s'.mem d 64 = salsa (bytesAt s.mem d 64) → Q s') →
    WP isa (.call "vg_salsa20_8" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .rdi
abbrev rr : Nat := (s₀.gpr .rsi).toNat
abbrev yP : Addr := s₀.gpr .rdx
abbrev sc : Addr := s₀.gpr .r8
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, 128⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- The caller's callee-saved registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ bmSaved, m.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_y : (stkR s₀).Disjoint (yR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 64
  rcx : s₀.gpr .rcx = s₀.gpr .rsi
  pos : 0 < rr s₀

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, by rw [h2, h14], ?_, h4.sub_right ?_, h5, ?_, h7, ?_, ?_, h10, h11, ?_, h13, h14, h15⟩
  · rw [h14] at h3; exact h3
  · rw [h14]; exact fun _ h => h
  · rw [h14] at h6; exact h6
  · exact h8
  · rw [h14] at h9; exact h9
  · rw [h14] at h12; exact h12

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (sc s₀ - yP s₀).isLt
  omega

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega) (by have := r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega) (by have := r_lt hp; omega)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  (hp.b_y.symm.sub_left (Memory.sub_off (by omega) (by omega))).sub_right (Memory.sub_off (by omega) (by omega))

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  Memory.sub_off (by omega) (by have := r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  Memory.sub_off (by omega) (by have := r_lt hp; omega)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  Memory.sub_off h (by omega)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bB s₀ k
  rbp : s.gpr .rbp = yE s₀ k
  r12 : s.gpr .r12 = yO s₀ k
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (rr s₀ - k)
  r15 : s.gpr .r15 = xP s₀ k
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is never written. -/
theorem Inv.b_bytes {s₀ : State} (hp : Pre s₀) {k : Nat} {s : State} (h : Inv s₀ k s) {o n : Nat}
    (ho : o + n ≤ 128 * rr s₀) :
    bytesAt s.mem (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt h.frame (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)
  · exact (hp.stk_b.symm.sub_left (b_sub hp ho))

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rdi ∧ r ≠ .rsi := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem calleeSaved_ne_rax {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o)
    (h13 : s.gpr .r13 = sc s₀) (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hwr : s.wr = s₀.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yP s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => WP.block_nil ?_)
  have lt := r_lt hp
  have e₁ : s₂.gpr .rdi = yP s₀ + BitVec.ofNat 64 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  have e₂ : s₂.gpr .rsi = sc s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h13]
  have e₃ : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (calleeSaved_ne hr).2, u₁.other _ (calleeSaved_ne hr).1]
  have e₄ : s₂.gpr .rsp = s₀.gpr .rsp := by rw [e₃ _ (by simp [calleeSaved]), hrsp]
  have hsub : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩ (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨sc s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (sc s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₂ _ _ e₁ e₂ (hp.y_s.sub_left hsub |>.sub_right hsub')
    (by rw [e₄]; exact hp.stk_y.sub_right hsub) (by rw [e₄]; exact hp.stk_s.sub_right hsub')
    (by rw [toNat_add_ofNat _ (by have := hp.y_nw; omega)]; have := hp.y_nw; omega)
    (by have := hp.s_nw; omega)
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd hwr' hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (fun r hr => by rw [hcs r hr, e₃ r hr]) (by rw [u₂.mem, u₁.mem, e₄] at hf; exact hf)
      (by rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem xor64_full {dR xR sR : Reg} (hd : dR ≠ .rax) (hx : xR ≠ .rax) (hs : sR ≠ .rax)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (gd : s.gpr dR = d) (gx : s.gpr xR = x) (gy : s.gpr sR = y)
    (hinx : ∀ k < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < 8, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < 8, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem y 64)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xor64 dR xR sR ++ rest)) s Q :=
  xor64_ok hd hx hs hdx hdy 8 (Nat.le_refl _) rest s Q gd gx gy hinx hiny hout k

theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := by decide

/-- The input is unchanged in any memory that differs from the initial one
only in `y`, `scratch` and the stack. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)
  · exact (hp.stk_b.symm.sub_left (b_sub hp ho))

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨sc s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

theorem slot_stk {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint (stkR s₀) :=
  (hp.stk_y.sub_right (y_sub hp ho)).symm

/-- Where `X` is. -/
theorem xP_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, scR s₀]) :
    ∀ i < 8, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega))
  | succ j =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_y hp (by omega))

theorem xP_disj {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    Region.Disjoint (slot s₀ (64 * k)) ⟨xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact yb_disj hp (by omega) (by have := hp.pos; omega)
  | succ j => exact y_disj hp (by omega) (by omega) (by omega) (by omega) (by omega)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  have lt := r_lt hp
  intro p hp'
  rw [← h p hp']
  have hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := s_sub s₀ (by omega)
  refine hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this
  · exact (hp.stk_s.sub_right hsub).symm

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact y_disj hp hd ho' ho (by omega) (by omega)
  · exact slot_s hp ho'
  · exact slot_stk hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] m m') : Frame [yR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        fun _ h => h⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .rax) (hx : xR ≠ .rax) (hs : sR ≠ .rax) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, scR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 64 ob) (h13 : s.gpr .r13 = sc s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x, 64⟩)
    (hinx : ∀ i < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * i)) 8)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := r_lt hp
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_full hd hx hs hdx (yb_disj hp ho hob) gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ m₁ => WP.block_nil ?_
  have l1 : (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)).length
      = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (yP s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hS hp ho (by rw [g₁ _ hd, gd]) (by rw [g₁ _ (by decide), h13])
    (by rw [g₁ _ (by decide), hrsp]) (by rw [wr₁, hwr, hp.wr])
    fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (calleeSaved_ne_rax hr)])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  rbp : s.gpr .rbp = yE s₀ k
  r12 : s.gpr .r12 = yO s₀ k
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (rr s₀ - k)
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨sc s₀, 64⟩, stkR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨sc s₀, 64⟩, stkR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  have lt := r_lt hp
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  have F₂ := h.frame.trans (frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega, ← blk_B s₀ (by omega), yAt_eq]
  have hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega)]
    exact b_frame hp F₂ (by omega)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega) (by omega) f₅, slot_keep hp oE (by omega) (by omega) f₂, d₁]
    · rw [slot_keep hp oO (by omega) (by omega) f₅, slot_keep hp oE (by omega) (by omega) f₂, d₂]

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .rbp .r15 .rbx)) <| .seq (salsaAt c .rbp) <|
      .seq (.block (.alu .add .rbx (.imm 64) :: xor64 .r12 .rbp .rbx)) <| .seq (salsaAt c .r12) P)
      s Q := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) oE (ob := 128 * k) (by omega)
    hrd hwr h.rbp h.r15 h.rbx h.r13 h.rsp (xP_disj hp hk) (xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  refine WP.seq (wp_addi fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .rbx → r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  have e3bx : s₃.gpr .rbx = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by simp [calleeSaved]), h.rbx, sx64, add_ofNat]; congr 2; omega
  have hrd₃ : s₃.rd = [bR s₀] := by rw [u₃.rd, rd₂, hrd]
  have hwr₃ : s₃.wr = [yR s₀, scR s₀] := by rw [u₃.wr, wr₂, hwr]
  have e3bp : s₃.gpr .rbp = yE s₀ k := by rw [k3 _ (by decide) (by simp [calleeSaved]), h.rbp]
  refine half_ok hS hp (by decide) (by decide) (by decide) oO (ob := 64 * (2 * k + 1)) (by omega)
    hrd₃ hwr₃ (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.r12]) e3bp e3bx
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.r13])
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.rsp])
    (y_disj hp (by omega) oO oE (by omega) (by omega))
    (fun i hi => by rw [hrd₃, hwr₃, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₅ rd₅ wr₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .rbx → r ∈ calleeSaved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.rsp],
    by rw [cs₅ _ (by simp [calleeSaved]), e3bx],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.rbp],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.r12],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.r13],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.r14], F, S, D⟩

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [.mov .r15 (.reg .r12), .alu .add .rbx (.imm 64), .alu .add .rbp (.imm 64),
      .alu .add .r12 (.imm 64), .alu .sub .r14 (.imm 1)]) s fun s' => Inv s₀ (k + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0) := by
  have lt := r_lt hp
  refine wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_addi fun s₉ u₉ =>
    wp_subi fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have r14 : s₉.gpr .r14 = BitVec.ofNat 64 (rr s₀ - k) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r14]
  refine ⟨⟨(by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), h.rsp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.rbx, sx64, add_ofNat]
    congr 2; omega
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.rbp, sx64, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r12, sx64, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), h.r13]
  · rw [u₁₀.gpr, r14, sx1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, Memory.toNat_ofNat_lt (by omega), Memory.toNat_ofNat_lt (by omega),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.r12]
    rfl
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl
  · rw [z₁₀, r14, sx1]

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (bmBody c) s fun s' => Inv s₀ (k + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.X86_64.BlockMix

/-!
# Calls of `vg_salsa20_8` on x86-64

Untrusted: everything here is checked by Lean. `SalsaSpec` of the verified
Salsa20/8 Core, from its `Verified` proof by `WP.call`.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64
open VG.Spec.Scrypt (bytesAt salsa)
open VG.Proof.MdStream.X86_64 (callEntry_byte)
open VG.Proof.Scrypt.Memory (bytesAt_congr)

theorem salsa_depth : Impl.Scrypt.X86_64.salsa.depth = 0 := by decide +kernel

theorem salsa_nosp : NoSp Impl.Scrypt.X86_64.salsa := by
  have : ((instrs Impl.Scrypt.X86_64.salsa).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- A region inside one of `rs` is covered by `rs`. -/
theorem covers_of_in {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    Covers [⟨a, n⟩] rs := by
  obtain ⟨R, hR, hc⟩ := h
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨R, hR, (a - R.base).toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega, hc⟩

theorem covers_pair {rs : List Region} {a b : Region} (ha : Covers [a] rs) (hb : Covers [b] rs) :
    Covers [a, b] rs := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha x n ⟨_, List.mem_singleton_self _, hc⟩
  · exact hb x n ⟨_, List.mem_singleton_self _, hc⟩

theorem salsaSpec : SalsaSpec Impl.Scrypt.X86_64.salsa := by
  intro s d sc hd hsc hds hsd hss _ _ hind hins Q hQ
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine WP.call (k := Proof.Scrypt.salsaX86_64) salsa_correct salsa_nosp
    (by rw [salsa_depth]; decide) (rd := []) (wr := [⟨d, 64⟩, ⟨sc, 64⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hd, hsc]
    exact ⟨trivial, trivial, hds, hsd, hss⟩
  · have := covers_pair (covers_of_in hind) (covers_of_in hins)
    intro a n h
    obtain ⟨R, hR, hc⟩ := this a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · exact covers_pair (covers_of_in hind) (covers_of_in hins)
  · intro s₂ hrd hwr hcs hf _ ⟨s₃, hm₃, _, hpost⟩
    simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hd, hm₃] at hpost
    rw [salsa_depth] at hf
    refine hQ s₂ hrd hwr hcs (by simpa using hf) ?_
    rw [hpost]
    congr 1
    exact bytesAt_congr fun i hi => callEntry_byte s (R := ⟨d, 64⟩) hsd (by simp) hi

end VG.Proof.Scrypt.X86_64.BlockMix

/-!
# scryptBlockMix on x86-64: the whole function

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers in `scratch` and sets up the loop's; the loop runs the
`r` pairs; the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_movm wp_store wp_add wp_subi)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem bytesAt_add frame_bytesAt
  bytesAt_blocks)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 64) (s₀.gpr .rbx)).writeW
    (sc s₀ + BitVec.ofNat 64 72) (s₀.gpr .rbp)).writeW (sc s₀ + BitVec.ofNat 64 80)
    (s₀.gpr .r12)).writeW (sc s₀ + BitVec.ofNat 64 88) (s₀.gpr .r14)).writeW
    (sc s₀ + BitVec.ofNat 64 96) (s₀.gpr .r15)).writeW (sc s₀ + BitVec.ofNat 64 104)
    (s₀.gpr .r13)

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 := by
  refine Mem.readW_writeW_sep (fun x hx hy => ?_) (by decide)
  have t₁ : (BitVec.ofNat 64 d).toNat = d := Memory.toNat_ofNat_lt (by omega)
  have t₂ : (BitVec.ofNat 64 e).toNat = e := Memory.toNat_ofNat_lt (by omega)
  bv_omega

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 128 → (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => in_s s₀ hd
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 64 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 72 (by omega))).writeW (List.mem_singleton_self _) _
    (c 80 (by omega))).writeW (List.mem_singleton_self _) _ (c 88 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 96 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 104 (by omega))

theorem prologue_eq : bmPrologue =
    ([.store (at_ .r8 64) .rbx, .store (at_ .r8 72) .rbp, .store (at_ .r8 80) .r12,
     .store (at_ .r8 88) .r14, .store (at_ .r8 96) .r15, .store (at_ .r8 104) .r13] : List Instr) ++
    ([.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r13 (.reg .r8),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.store (at_ .r8 64) .rbx, .store (at_ .r8 72) .rbp, .store (at_ .r8 80) .r12,
      .store (at_ .r8 88) .r14, .store (at_ .r8 96) .r15, .store (at_ .r8 104) .r13] : List Instr) ++ rest))
      s₀ Q := by
  have o : ∀ d, d + 8 ≤ 128 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_store (ea_at _ _ _) (o 64 (by omega) _ rfl) fun s1 g1 m1 r1 w1 => ?_
  refine wp_store (by rw [ea_at, g1]) (o 72 (by omega) _ w1) fun s2 g2 m2 r2 w2 => ?_
  refine wp_store (by rw [ea_at, g2, g1]) (o 80 (by omega) _ (w2.trans w1))
    fun s3 g3 m3 r3 w3 => ?_
  refine wp_store (by rw [ea_at, g3, g2, g1]) (o 88 (by omega) _ (w3.trans (w2.trans w1)))
    fun s4 g4 m4 r4 w4 => ?_
  refine wp_store (by rw [ea_at, g4, g3, g2, g1])
    (o 96 (by omega) _ (w4.trans (w3.trans (w2.trans w1)))) fun s5 g5 m5 r5 w5 => ?_
  refine wp_store (by rw [ea_at, g5, g4, g3, g2, g1])
    (o 104 (by omega) _ (w5.trans (w4.trans (w3.trans (w2.trans w1))))) fun s6 g6 m6 r6 w6 => ?_
  exact k s6 (by rw [g6, g5, g4, g3, g2, g1]) (by rw [r6, r5, r4, r3, r2, r1])
    (w6.trans (w5.trans (w4.trans (w3.trans (w2.trans w1)))))
    (by rw [m6, m5, m4, m3, m2, m1, g5, g4, g3, g2, g1]; rfl)

theorem dbl {a : Addr} {n : Nat} (h : a = BitVec.ofNat 64 n) : a + a = BitVec.ofNat 64 (2 * n) := by
  rw [h, ← BitVec.ofNat_add, Nat.two_mul]

set_option linter.unusedSimpArgs false in
/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx),
     .mov .r13 (.reg .r8),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)]) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_mov fun f uf _ _ => wp_add fun g' ug =>
    wp_mov fun h uh _ _ => wp_add fun i ui => wp_add fun j uj => wp_subi fun l ul _ => WP.block_nil ?_
  have x0 : d.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (dbl x0)
  have x2 := u2.gpr.trans (dbl x1)
  have x3 := u3.gpr.trans (dbl x2)
  have x4 := u4.gpr.trans (dbl x3)
  have x5 := u5.gpr.trans (dbl x4)
  have x6 : e6.gpr .rsi = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [u6.gpr.trans (dbl x5)]; exact congrArg (BitVec.ofNat _) (by omega)
  have hm' : l.mem = saveMem s₀ := by
    rw [ul.mem, uj.mem, ui.mem, uh.mem, ug.mem, uf.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [ul.rd, uj.rd, ui.rd, uh.rd, ug.rd, uf.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ul.wr, uj.wr, ui.wr, uh.wr, ug.wr, uf.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g, BitVec.ofNat_toNat, BitVec.setWidth_eq]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g, sx64]
    show _ = bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
    rw [add_ofNat, ofNat_split (a := 64) (b := 64 * rr s₀ + 64 * rr s₀) (by omega),
      show 64 * rr s₀ + 64 * rr s₀ - 64 = 128 * rr s₀ - 64 by omega,
      BitVec.add_comm (BitVec.ofNat 64 64), ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega))

/-! ## The loop -/

/-- The loop's condition after pair `k`. -/
theorem eval_ne {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hz : s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) :
    isa.eval .ne s = some (decide (k + 1 ≠ rr s₀)) := by
  have lt := r_lt hp
  have e : BitVec.ofNat 64 (rr s₀ - k) - 1 = BitVec.ofNat 64 (rr s₀ - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, Memory.toNat_ofNat_lt (by omega), Memory.toNat_ofNat_lt (by omega),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  rw [e] at hz
  show s.zf.map (!·) = _
  rw [hz]
  by_cases hl : k + 1 = rr s₀
  · simp [hl]
  · have hne : (BitVec.ofNat 64 (rr s₀ - (k + 1)) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [Memory.toNat_ofNat_lt (by omega)] at this
      simp at this; omega
    rw [Option.map_some, hne]; simp [hl]

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  rw [eval_ne hp hk hz]
  by_cases hl : k + 1 = rr s₀
  · exact .inl ⟨by simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hin : ∀ d, d + 8 ≤ 128 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ bmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.saved
  simp only [bmEpilogue, bmSaved, List.map_cons, List.map_nil]
  refine wp_movm (by rw [ea_at, h.r13]) (hin 64 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_movm (by rw [ea_at, ua.other _ (by decide), h.r13])
    (hin 72 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_movm (by rw [ea_at, ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 80 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_movm (by rw [ea_at, uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13])
    (hin 88 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_movm (by rw [ea_at, ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 96 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_movm (by rw [ea_at, ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 104 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => WP.block_nil ?_
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, sv (.rbx, 64) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.mem, sv (.rbp, 72) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.rsp]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.mem, ua.mem, sv (.r12, 80) (by simp [bmSaved])]
  · rw [uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.r13, 104) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem,
      sv (.r14, 88) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem, sv (.r15, 96) (by simp [bmSaved])]

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block bmPrologue) s₀ (Inv s₀ 0) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hm => setup_ok hp g hrd hwr hm

theorem correct {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86_64.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_y
    · exact hp.ret_s
    · exact ret_stk s₀
  · show bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.X86_64.BlockMix

/-!
# scryptBlockMix on x86-64: constant time

Untrusted: everything here is checked by Lean.

The taint analysis alone cannot prove this: across a call of
`vg_salsa20_8`, which saves and restores our registers in memory it also
writes secrets to through a pointer of unknown provenance, it forgets that
our pointers are public. So we relate two runs (`RelCT`): at every point,
correctness determines our registers from the public arguments alone, so
they agree; between the calls, the taint analysis proves each block
constant time from that; and the calls are constant time by Salsa20/8's own
proof.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_addi)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

/-- The loop's registers during pair `k`, with `rbx = bx`. -/
structure KR (s₀ : State) (k : Nat) (bx : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bx
  rbp : s.gpr .rbp = yE s₀ k
  r12 : s.gpr .r12 = yO s₀ k
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (rr s₀ - k)
  r15 : s.gpr .r15 = xP s₀ k

theorem KR.of_inv {s₀ : State} {k : Nat} {s : State} (h : Inv s₀ k s) : KR s₀ k (bB s₀ k) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem KR.keep {s₀ : State} {k : Nat} {bx : Addr} {s s' : State} (h : KR s₀ k bx s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    KR s₀ k bx s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hk _ (by simp [calleeSaved])).trans h.rsp,
    (hk _ (by simp [calleeSaved])).trans h.rbx, (hk _ (by simp [calleeSaved])).trans h.rbp,
    (hk _ (by simp [calleeSaved])).trans h.r12, (hk _ (by simp [calleeSaved])).trans h.r13,
    (hk _ (by simp [calleeSaved])).trans h.r14, (hk _ (by simp [calleeSaved])).trans h.r15⟩

theorem PubEq.rr {s₀ s₀' : State} (hq : PubEq s₀ s₀') : rr s₀ = rr s₀' := by
  simp only [VG.Proof.Scrypt.X86_64.BlockMix.rr, hq.rsi]

theorem PubEq.xP {s₀ s₀' : State} (hq : PubEq s₀ s₀') (k : Nat) : xP s₀ k = xP s₀' k := by
  cases k <;> simp only [VG.Proof.Scrypt.X86_64.BlockMix.xP, bP, yO, yP, hq.rdi, hq.rdx, hq.rr]

/-- The registers the blocks use agree in two runs. -/
theorem KR.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {k : Nat} {bx bx' : Addr} {s s' : State}
    (h : KR s₀ k bx s) (h' : KR s₀' k bx' s') (hbx : bx = bx') :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, hbx]
  · rw [h.rbp, h'.rbp, yE, yE, yP, yP, hq.rdx]
  · rw [h.r12, h'.r12, yO, yO, yP, yP, hq.rdx, hq.rr]
  · rw [h.r13, h'.r13, sc, sc, hq.r8]
  · rw [h.r14, h'.r14, hq.rr]
  · rw [h.r15, h'.r15, hq.xP]
  · rw [h.rsp, h'.rsp, hq.rsp]

/-! ## What each piece of the loop body does to the registers -/

section
variable {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
include hp hk

theorem xor1_wp {s : State} (h : KR s₀ k (bB s₀ k) s) :
    WP isa (.block (xor64 .rbp .r15 .rbx)) s (KR s₀ k (bB s₀ k)) := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀] := h.rd.trans hp.rd
  have hwr : s.wr = [yR s₀, scR s₀] := h.wr.trans hp.wr
  rw [← List.append_nil (xor64 .rbp .r15 .rbx)]
  refine xor64_full (d := yE s₀ k) (x := xP s₀ k) (y := bB s₀ k) (by decide) (by decide)
    (by decide) (xP_disj hp hk) (yb_disj hp (by omega) (by omega)) h.rbp h.r15 h.rbx
    (xP_in hp hk hrd hwr)
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun _ g₁ rd₁ wr₁ _ => WP.block_nil (h.keep rd₁ wr₁ fun r hr => g₁ r (calleeSaved_ne_rax hr))

theorem xor2_wp {s : State} (h : KR s₀ k (bB s₀ k) s) :
    WP isa (.block (.alu .add .rbx (.imm 64) :: xor64 .r12 .rbp .rbx)) s
      (KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)))) := by
  have lt := r_lt hp
  refine wp_addi fun s₃ u₃ => ?_
  have hrd : s₃.rd = [bR s₀] := u₃.rd.trans (h.rd.trans hp.rd)
  have hwr : s₃.wr = [yR s₀, scR s₀] := u₃.wr.trans (h.wr.trans hp.wr)
  have e3bx : s₃.gpr .rbx = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, h.rbx, sx64, add_ofNat]; congr 2; omega
  have h₃ : KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s₃ :=
    ⟨u₃.rd.trans h.rd, u₃.wr.trans h.wr, (u₃.other _ (by decide)).trans h.rsp, e3bx,
      (u₃.other _ (by decide)).trans h.rbp, (u₃.other _ (by decide)).trans h.r12,
      (u₃.other _ (by decide)).trans h.r13, (u₃.other _ (by decide)).trans h.r14,
      (u₃.other _ (by decide)).trans h.r15⟩
  rw [← List.append_nil (xor64 .r12 .rbp .rbx)]
  refine xor64_full (d := yO s₀ k) (x := yE s₀ k) (y := bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)))
    (by decide) (by decide) (by decide) (y_disj hp (by omega) (by omega) (by omega) (by omega)
      (by omega))
    (yb_disj hp (by omega) (by omega)) h₃.r12 h₃.rbp e3bx
    (fun i hi => by rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    (fun i hi => by rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun _ g₁ rd₁ wr₁ _ => WP.block_nil (h₃.keep rd₁ wr₁ fun r hr => g₁ r (calleeSaved_ne_rax hr))

end

theorem salsa_wp {s₀ : State} (hp : Pre s₀) {k : Nat} {bx : Addr} {dR : Reg} {o : Nat}
    (ho : o + 64 ≤ 128 * rr s₀) {s : State} (h : KR s₀ k bx s)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) :
    WP isa (salsaAt salsa dR) s (KR s₀ k bx) :=
  salsaAt_ok salsaSpec hp ho hd h.r13 h.rsp h.wr fun _ rd wr cs _ _ => h.keep rd wr cs

theorem movs_wp {s₀ : State} {k : Nat} {bx : Addr} {dR : Reg} {o : Addr}
    {s : State} (h : KR s₀ k bx s) (hd : s.gpr dR = o) :
    WP isa (.block [.mov .rdi (.reg dR), .mov .rsi (.reg .r13)]) s fun s' =>
      KR s₀ k bx s' ∧ s'.gpr .rdi = o ∧ s'.gpr .rsi = sc s₀ := by
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · refine h.keep (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) fun r hr => ?_
    rw [u₂.other _ (calleeSaved_ne hr).2, u₁.other _ (calleeSaved_ne hr).1]
  · rw [u₂.other _ (by decide), u₁.gpr, hd]
  · rw [u₂.gpr, u₁.other _ (by decide), h.r13]

/-- What a call of `vg_salsa20_8` on block `o` of `y` needs. -/
theorem call_hyps {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {s : State}
    (hrdi : s.gpr .rdi = yP s₀ + BitVec.ofNat 64 o) (hrsi : s.gpr .rsi = sc s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hwr : s.wr = s₀.wr) :
    Proof.Scrypt.salsaX86_64.pre
      (s.callEntry.withRegions [] [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩]) ∧
    Covers ([] ++ [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩] s.wr := by
  have lt := r_lt hp
  have hsub : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩ (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨sc s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (sc s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have cw : Covers [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩] s.wr := by
    rw [hwr, hp.wr]
    exact covers_pair (covers_of_in (InRegions.of_mem (by simp) (in_y hp ho)))
      (covers_of_in (InRegions.of_mem (R := scR s₀) (by simp) hsc))
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, fun a n h => ?_, cw⟩
  · simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi, hrsp]
    exact ⟨trivial, trivial, hp.y_s.sub_left hsub |>.sub_right hsub',
      hp.stk_y.sub_right hsub, hp.stk_s.sub_right hsub'⟩
  · obtain ⟨R, hR, hc⟩ := cw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩

/-! ## Two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

omit hp hp' hq in
theorem movs_rel {k : Nat} {bx bx' : Addr} {dR : Reg} (hdR : dR = .rbp ∨ dR = .r12) {o : Nat} :
    RelCT isa (fun s s' => (KR s₀ k bx s ∧ s.gpr dR = yP s₀ + BitVec.ofNat 64 o) ∧
        (KR s₀' k bx' s' ∧ s'.gpr dR = yP s₀' + BitVec.ofNat 64 o))
      (.block [.mov .rdi (.reg dR), .mov .rsi (.reg .r13)]) fun s s' =>
      (KR s₀ k bx s ∧ s.gpr .rdi = yP s₀ + BitVec.ofNat 64 o ∧ s.gpr .rsi = sc s₀) ∧
      (KR s₀' k bx' s' ∧ s'.gpr .rdi = yP s₀' + BitVec.ofNat 64 o ∧ s'.gpr .rsi = sc s₀') := by
  have ct : RelCT isa (fun s s' => (KR s₀ k bx s ∧ s.gpr dR = yP s₀ + BitVec.ofNat 64 o) ∧
        (KR s₀' k bx' s' ∧ s'.gpr dR = yP s₀' + BitVec.ofNat 64 o))
      (.block [.mov .rdi (.reg dR), .mov .rsi (.reg .r13)]) fun _ _ => True := by
    rcases hdR with rfl | rfl
    · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
        (by taint_decide)
    · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
        (by taint_decide)
  exact (ct.wp fun s s' h => ⟨movs_wp h.1.1 h.1.2, movs_wp h.2.1 h.2.2⟩).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem salsaAt_rel {k : Nat} {bx bx' : Addr} {dR : Reg} (hdR : dR = .rbp ∨ dR = .r12) {o : Nat}
    (ho : o + 64 ≤ 128 * rr s₀) :
    RelCT isa (fun s s' => (KR s₀ k bx s ∧ s.gpr dR = yP s₀ + BitVec.ofNat 64 o) ∧
        (KR s₀' k bx' s' ∧ s'.gpr dR = yP s₀' + BitVec.ofNat 64 o))
      (salsaAt salsa dR) fun s s' => KR s₀ k bx s ∧ KR s₀' k bx' s' := by
  have ho' : o + 64 ≤ 128 * rr s₀' := hq.rr ▸ ho
  have ey : yP s₀' = yP s₀ := hq.rdx.symm
  have es : sc s₀' = sc s₀ := hq.r8.symm
  have call := RelCT.call (n := "vg_salsa20_8") (P := fun s s' =>
      (KR s₀ k bx s ∧ s.gpr .rdi = yP s₀ + BitVec.ofNat 64 o ∧ s.gpr .rsi = sc s₀) ∧
      (KR s₀' k bx' s' ∧ s'.gpr .rdi = yP s₀' + BitVec.ofNat 64 o ∧ s'.gpr .rsi = sc s₀'))
    salsa_correct salsa_ct [] [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩]
    fun s s' ⟨⟨h, hd, hs⟩, ⟨h', hd', hs'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_hyps hp ho hd hs h.rsp h.wr
      obtain ⟨p₂, c₂, w₂⟩ := call_hyps hp' ho' hd' hs' h'.rsp h'.wr
      rw [ey, es] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [h.rsp, h'.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), hd, hs, hd', hs', ey, es]
      exact ⟨trivial, trivial⟩
  exact ((RelCT.seq (movs_rel hdR) call).wp fun s s' h =>
    ⟨salsa_wp hp ho h.1.1 h.1.2, salsa_wp hp' ho' h.2.1 h.2.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

end

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- The registers the loop's blocks use. -/
abbrev τK : X86_64.Taint.T := Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem body_rel {k : Nat} (hk : k < rr s₀) :
    RelCT isa (fun s s' => Inv s₀ k s ∧ Inv s₀' k s') (bmBody salsa) fun s s' =>
      (Inv s₀ (k + 1) s ∧ s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) ∧
      (Inv s₀' (k + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (rr s₀' - k) - 1 == 0)) := by
  have lt := r_lt hp
  have hk' : k < rr s₀' := hq.rr ▸ hk
  have hbB : bB s₀ k = bB s₀' k := by simp only [bB, bP, hq.rdi]
  have hb1 : bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) =
      bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1)) := by simp only [bP, hq.rdi]
  have x1 : RelCT isa (fun s s' => Inv s₀ k s ∧ Inv s₀' k s') (.block (xor64 .rbp .r15 .rbx))
      fun s s' => KR s₀ k (bB s₀ k) s ∧ KR s₀' k (bB s₀' k) s' :=
    ((RelCT.taint (A := taint) τK (fun _ _ h => Taint.agree_ofRegs
      (KR.agree hq (KR.of_inv h.1) (KR.of_inv h.2) hbB)) (by taint_decide)).wp fun _ _ h =>
      ⟨xor1_wp hp hk (KR.of_inv h.1), xor1_wp hp' hk' (KR.of_inv h.2)⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have s1 := (salsaAt_rel hp hp' hq (k := k) (bx := bB s₀ k) (bx' := bB s₀' k) (.inl rfl)
    (o := 64 * k) (by omega)).mono (P' := fun s s' => KR s₀ k (bB s₀ k) s ∧ KR s₀' k (bB s₀' k) s')
      (fun _ _ h => ⟨⟨h.1, h.1.rbp⟩, ⟨h.2, h.2.rbp⟩⟩) fun _ _ h => h
  have x2 : RelCT isa (fun s s' => KR s₀ k (bB s₀ k) s ∧ KR s₀' k (bB s₀' k) s')
      (.block (.alu .add .rbx (.imm 64) :: xor64 .r12 .rbp .rbx)) fun s s' =>
        KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s ∧
        KR s₀' k (bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) s' :=
    ((RelCT.taint (A := taint) τK (fun _ _ h => Taint.agree_ofRegs (KR.agree hq h.1 h.2 hbB))
      (by taint_decide)).wp fun _ _ h => ⟨xor2_wp hp hk h.1, xor2_wp hp' hk' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have s2 := (salsaAt_rel hp hp' hq (k := k) (bx := bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)))
    (bx' := bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) (.inr rfl) (o := 64 * (rr s₀ + k))
    (by omega)).mono (P' := fun s s' => KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s ∧
      KR s₀' k (bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) s')
      (fun _ _ h => ⟨⟨h.1, h.1.r12⟩, ⟨h.2, by rw [h.2.r12, hq.rr]⟩⟩) fun _ _ h => h
  have r : RelCT isa (fun s s' => KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s ∧
        KR s₀' k (bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) s')
      (.block [.mov .r15 (.reg .r12), .alu .add .rbx (.imm 64), .alu .add .rbp (.imm 64),
        .alu .add .r12 (.imm 64), .alu .sub .r14 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) τK (fun _ _ h => Taint.agree_ofRegs (KR.agree hq h.1 h.2 hb1))
      (by taint_decide)
  exact ((x1.seq (s1.seq (x2.seq (s2.seq r)))).wp fun _ _ h =>
    ⟨body_ok salsaSpec hp hk h.1, body_ok salsaSpec hp' hk' h.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop (bmBody salsa) .ne) fun s s' =>
      Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := bmBody salsa) (c := .ne)
    (Q := fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s')
    (fun n s s' => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s ∧ Inv s₀' k s') (fun n => by
      intro s s' t t' u u' ⟨k, hn, hk, h, h'⟩ e e'
      have hk' : k < rr s₀' := hq.rr ▸ hk
      obtain ⟨ht, ⟨i, z⟩, ⟨i', z'⟩⟩ := body_rel hp hp' hq hk _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_ne hp hk z, eval_ne hp' hk' z', ← hq.rr]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : k + 1 = rr s₀ := by simpa using hf
        exact ⟨hl ▸ i, hl ▸ i'⟩
      · have hl : k + 1 ≠ rr s₀ := by simpa using ht'
        exact ⟨rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, i, i'⟩) (rr s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, hp.pos, h.1, h.2⟩) fun _ _ h => h

theorem blockMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') blockMix fun _ _ => True := by
  show RelCT isa _ (blockMixWith salsa) _
  unfold blockMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block bmPrologue)
      fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.r8
        · exact hq.rsp) (c := .block bmPrologue) (by taint_decide)).wp
      (F₁ := Inv s₀ 0) (F₂ := Inv s₀' 0) fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s') (.block bmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq ((loop_rel hp hp' hq).seq epi)

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.blockMixX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .rsp => 0x4000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct salsaSpec (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre
    Proof.Scrypt.blockMixX86_64.pub Impl.Scrypt.X86_64.blockMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (blockMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem blockMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.blockMix (Spec.Scrypt.blockMixContract X86_64.abi 8) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.BlockMix.satState]
          [Proof.Scrypt.X86_64.BlockMix.satState] using Proof.Scrypt.X86_64.BlockMix.satState }

end VG.Proof.Scrypt.X86_64.BlockMix
