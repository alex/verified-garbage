import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Proof.Scrypt.X86_64.Contract

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
open VG.Proof.Sha1.X86_64.Stream (Upd wp_mov wp_movm wp_store wp_add wp_addi wp_subi)

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
  contains_off (by omega) (by have := r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

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
  (hp.b_y.symm.sub_left (sub_off (by omega) (by omega))).sub_right (sub_off (by omega) (by omega))

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega)

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
    rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega),
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
