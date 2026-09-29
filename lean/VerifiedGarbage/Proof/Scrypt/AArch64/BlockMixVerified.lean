import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.AArch64.Common
import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptBlockMix on AArch64: correctness of the loop

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Scrypt/X86_64/BlockMixCT.lean`), the calls of `vg_salsa20_8` are used
through `SalsaSpec`, what its proof says about a call; the proof of this file
holds for any code meeting it.

The function's body runs inside a frame saving `x30`; the state `s₀` here is
the one the body starts in, and the frame is handled in
this file.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_subImm sub_ofNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c` replaces the 64 bytes at `x0` by their Salsa20/8 Core,
with the 64 bytes at `x1` as working space. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (d sc : Addr), s.gpr .x0 = d → s.gpr .x1 = sc →
    Region.Disjoint ⟨d, 64⟩ ⟨sc, 64⟩ → InRegions s.wr d 64 → InRegions s.wr sc 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
        Frame [⟨d, 64⟩, ⟨sc, 64⟩] s.mem s'.mem →
        bytesAt s'.mem d 64 = salsa (bytesAt s.mem d 64) → Q s') →
    WP isa (.call "vg_salsa20_8" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev rr : Nat := (s₀.gpr .x1).toNat
abbrev yP : Addr := s₀.gpr .x2
abbrev sc : Addr := s₀.gpr .x4
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, 128⟩
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

/-- The caller's `x19`–`x24` are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ bmSaved, m.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

/-- The callee-saved registers the code never writes (`x30` aside). -/
def others : List Reg := [.x25, .x26, .x27, .x28, .x29]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 64
  x3 : s₀.gpr .x3 = s₀.gpr .x1
  pos : 0 < rr s₀

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

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

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
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bB s₀ k
  x20 : s.gpr .x20 = yE s₀ k
  x21 : s.gpr .x21 = yO s₀ k
  x22 : s.gpr .x22 = sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ - k)
  x24 : s.gpr .x24 = xP s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `scratch`. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x9 ∧ r ≠ .x10 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o)
    (h22 : s.gpr .x22 = sc s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨sc s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yP s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have e₁ : s₂.gpr .x0 = yP s₀ + BitVec.ofNat 64 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  have e₂ : s₂.gpr .x1 = sc s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h22]
  have e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (pres_ne r hr).2.1, u₁.other _ (pres_ne r hr).1]
  have hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨sc s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (sc s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₂ _ _ e₁ e₂ (hp.y_s.sub_left hsub |>.sub_right hsub')
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr h30 => by rw [hcs r hr h30, e₃ r hr])
      (by rw [u₂.mem, u₁.mem] at hf; exact hf) (by rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨sc s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

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
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := s_sub s₀ (by omega)
  refine hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho (by omega) (by omega)
  · exact slot_s hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') : Frame [yR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .x9 ∧ dR ≠ .x10) (hx : xR ≠ .x9 ∧ xR ≠ .x10) (hs : sR ≠ .x9 ∧ sR ≠ .x10)
    {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, scR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 64 ob) (h22 : s.gpr .x22 = sc s₀)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x, 64⟩)
    (hinx : ∀ i < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * i)) 8)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨sc s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := r_lt hp
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_ok hd hx hs hdx (yb_disj hp ho hob) 8 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  have l1 : (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)).length
      = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (yP s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hS hp ho (by rw [g₁ _ hd.1 hd.2, gd]) (by rw [g₁ _ (by decide) (by decide), h22])
    (by rw [wr₁, hwr, hp.wr]) fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr h30 => by rw [cs₂ r hr h30, g₁ r (pres_ne r hr).2.2.1 (pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  x20 : s.gpr .x20 = yE s₀ k
  x21 : s.gpr .x21 = yO s₀ k
  x22 : s.gpr .x22 = sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨sc s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨sc s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
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

theorem others_pres : ∀ r ∈ others, r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x19 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .x20 .x24 .x19)) <| .seq (salsaAt c .x20) <|
      .seq (.block (.addImm .x .x19 .x19 64 :: xor64 .x21 .x20 .x19)) <| .seq (salsaAt c .x21) P)
      s Q := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) oE (ob := 128 * k) (by omega)
    hrd hwr h.x20 h.x24 h.x19 h.x22 (xP_disj hp hk) (xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine WP.seq (wp_addImm (by decide) fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .x19 → r ∈ preserved → r ≠ .x30 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other _ h1, cs₂ r h2 h3]
  have e3 : s₃.gpr .x19 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide) (by decide), h.x19, add_ofNat]; congr 2; omega
  have hrd₃ : s₃.rd = [bR s₀] := by rw [u₃.rd, rd₂, hrd]
  have hwr₃ : s₃.wr = [yR s₀, scR s₀] := by rw [u₃.wr, wr₂, hwr]
  have e20 : s₃.gpr .x20 = yE s₀ k := by rw [k3 _ (by decide) (by decide) (by decide), h.x20]
  refine half_ok hS hp (by decide) (by decide) (by decide) oO (ob := 64 * (2 * k + 1)) (by omega)
    hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide) (by decide), h.x21]) e20 e3
    (by rw [k3 _ (by decide) (by decide) (by decide), h.x22])
    (y_disj hp (by omega) oO oE (by omega) (by omega))
    (fun i hi => by rw [hrd₃, hwr₃, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .x19 → r ∈ preserved → r ≠ .x30 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [cs₅ r h2 h3, k3 r h1 h2 h3]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide) (by decide), e3],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x20],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x21],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x22],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x23],
    fun r hr => by
      rw [k5 r (others_pres r hr).2.2 (others_pres r hr).1 (others_pres r hr).2.1, h.keep r hr],
    F, S, D⟩

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [mov .x24 .x21, .addImm .x .x19 .x19 64, .addImm .x .x20 .x20 64,
      .addImm .x .x21 .x21 64, .subImm .x .x23 .x23 1]) s (Inv s₀ (k + 1)) := by
  have lt := r_lt hp
  refine wp_mov fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => wp_addImm (by decide) fun s₈ u₈ =>
    wp_addImm (by decide) fun s₉ u₉ => wp_subImm (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → s₁₀.gpr r = s.gpr r :=
    fun r h19 h20 h21 h23 h24 => by
      rw [u₁₀.other _ h23, u₉.other _ h21, u₈.other _ h20, u₇.other _ h19, u₆.other _ h24]
  refine ⟨(by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.x19, add_ofNat]
    congr 2; omega
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.x20, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x21, add_ofNat]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x23, sub_ofNat (by omega)]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.x21]
    rfl
  · intro r hr
    have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) : WP isa (bmBody c) s (Inv s₀ (k + 1)) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the whole function

Untrusted: everything here is checked by Lean. The prologue saves our
caller's `x19`–`x24` in `scratch` and sets up the loop's registers; the loop
runs the `r` pairs; the epilogue restores the registers. Around all of it, a
frame saves `x30`, which the calls replace.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero readW_writeW_save write_frame_bytes)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks bytesAt_congr)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 64) (s₀.gpr .x19)).writeW
    (sc s₀ + BitVec.ofNat 64 72) (s₀.gpr .x20)).writeW (sc s₀ + BitVec.ofNat 64 80)
    (s₀.gpr .x21)).writeW (sc s₀ + BitVec.ofNat 64 88) (s₀.gpr .x23)).writeW
    (sc s₀ + BitVec.ofNat 64 96) (s₀.gpr .x24)).writeW (sc s₀ + BitVec.ofNat 64 104)
    (s₀.gpr .x22)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save]

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
    ([.str .x .x19 .x4 64, .str .x .x20 .x4 72, .str .x .x21 .x4 80, .str .x .x23 .x4 88,
     .str .x .x24 .x4 96, .str .x .x22 .x4 104] : List Instr) ++
    [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64] := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.str .x .x19 .x4 64, .str .x .x20 .x4 72, .str .x .x21 .x4 80,
      .str .x .x23 .x4 88, .str .x .x24 .x4 96, .str .x .x22 .x4 104] : List Instr) ++ rest)) s₀ Q := by
  have o : ∀ d, d + 8 ≤ 128 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by decide) rfl (o 64 (by omega) _ rfl) fun s1 u1 => ?_
  refine wp_str (by decide) (by rw [u1.gpr]) (o 72 (by omega) _ u1.wr) fun s2 u2 => ?_
  refine wp_str (by decide) (by rw [u2.gpr, u1.gpr]) (o 80 (by omega) _ (u2.wr.trans u1.wr))
    fun s3 u3 => ?_
  refine wp_str (by decide) (by rw [u3.gpr, u2.gpr, u1.gpr])
    (o 88 (by omega) _ (u3.wr.trans (u2.wr.trans u1.wr))) fun s4 u4 => ?_
  refine wp_str (by decide) (by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 96 (by omega) _ (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))) fun s5 u5 => ?_
  refine wp_str (by decide) (by rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 104 (by omega) _ (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))))
    fun s6 u6 => ?_
  exact k s6 (by rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (by rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (u6.wr.trans (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))))
    (by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp])
    (by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
        rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64]) s₁ (Inv s₀ 0) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_mov fun d ud =>
    wp_lsl (by decide) fun e ue => wp_add fun f uf => wp_lsl (by decide) fun g' ug =>
    wp_add fun h uh => wp_subImm (by decide) fun i ui => WP.block_nil ?_
  have x1 : d.gpr .x1 = s₀.gpr .x1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  have e9 : e.gpr .x9 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, x1, shl_eq (by simp; omega), Nat.mul_comm]
  have g9 : g'.gpr .x9 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), x1, shl_eq (by simp; omega),
      Nat.mul_comm]
  have hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  have k : ∀ r, r ≠ .x9 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
      i.gpr r = s₀.gpr r := fun r h9 h19 h20 h21 h22 h23 h24 => by
    rw [ui.other _ h24, uh.other _ h24, ug.other _ h9, uf.other _ h21, ue.other _ h9,
      ud.other _ h22, uc.other _ h20, ub.other _ h19, ua.other _ h23, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e9,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g9, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega)]
    rfl
  · intro r hr
    have : r ≠ .x9 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h9, h19, h20, h21, h22, h23, h24⟩ := this
    exact k r h9 h19 h20 h21 h22 h23 h24
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

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) (.nonzero .x .x23)) s (Inv s₀ (rr s₀)) := by
  have lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' hi' => ?_
  have hz : isa.eval (.nonzero .x .x23) s' = some (decide (rr s₀ - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x23) s' = _
    rw [eval_nonzero, hi'.x23, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = rr s₀ by omega] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) := by
  have hin : ∀ d, d + 8 ≤ 128 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ bmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.saved
  simp only [bmEpilogue, bmSaved, List.map_cons, List.map_nil]
  refine wp_ldr (by decide) (by rw [h.x22]) (hin 64 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_ldr (by decide) (by rw [ua.other _ (by decide), h.x22])
    (hin 72 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_ldr (by decide) (by rw [ub.other _ (by decide), ua.other _ (by decide), h.x22])
    (hin 80 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_ldr (by decide) (by rw [uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x22])
    (hin 88 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_ldr (by decide) (by rw [ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.x22])
    (hin 96 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_ldr (by decide) (by rw [ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.x22])
    (hin 104 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => WP.block_nil ?_
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, by rw [uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp], fun r hr h30 => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, sv (.x19, 64) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.mem, sv (.x20, 72) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.mem, ua.mem, sv (.x21, 80) (by simp [bmSaved])]
  · rw [uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.x22, 104) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem,
      sv (.x23, 88) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.x24, 96) (by simp [bmSaved])]
  all_goals first
    | exact absurd rfl h30
    | rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
        uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide)]
      exact h.keep _ (by simp [others])

/-! ## The body of the frame -/

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

theorem correctMain {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixMain c) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  unfold blockMixMain
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hsp hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hsp hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₃.sp, ?_⟩
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

/-! ## The whole function -/

/-- The frame's 16 bytes are free. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  b : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (bR s₀)
  y : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (yR s₀)
  s : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rw [h13] at h2 h3 h4 h8 h11
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11, h12, h13, h14⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The state the body starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {c : Prog isa} (hS : SalsaSpec c)
    (hd : 16 * (blockMixMain c).fdepth + 16 < 2 ^ 64) {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixAArch64.post s₀ s' := by
  have hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.y_s, hp.b_y, hp.b_s, hp.b_nw, hp.y_nw, hp.s_nw,
    hp.x3, hp.pos⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hS hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_) hd
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.y
    · exact hs.s
  · refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : B (inner s₀) = bytesAt s₀.mem (bP s₀) (128 * rr s₀) :=
        bytesAt_congr fun i hi => by
          have hi' : i < 128 * rr s₀ := hi
          exact write_frame_bytes (R := bR s₀) hs.b (by have := r_lt hp; simp only; omega)
            (by simp only; omega)
      show bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s₀.mem (bP s₀) (128 * rr s₀))
      rw [← e]
      exact hpost

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: verified

Untrusted: everything here is checked by Lean. `SalsaSpec` of the verified
Salsa20/8 Core, from its `Verified` proof by `WP.call`; then the `Verified`
proof of `vg_scrypt_blockmix`. Only the pointers and `r` are public, and the
taint analysis checks that nothing else reaches an address or a branch.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64

theorem salsa_noFrames : Impl.Scrypt.AArch64.salsa.noFrames = true := by decide +kernel

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

theorem salsaSpec : SalsaSpec Impl.Scrypt.AArch64.salsa := by
  intro s d sc hd hsc hds hind hins Q hQ
  have c0 : s.callEntry.gpr .x0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  have c1 : s.callEntry.gpr .x1 = sc := (State.callEntry_gpr _ (by decide)).trans hsc
  have hw : Covers [⟨d, 64⟩, ⟨sc, 64⟩] s.wr := covers_pair (covers_of_in hind) (covers_of_in hins)
  refine WP.call (k := Proof.Scrypt.salsaAArch64) Proof.Scrypt.AArch64.salsa_correct
    (rd := []) (wr := [⟨d, 64⟩, ⟨sc, 64⟩]) ?_ ?_ hw ?_ salsa_noFrames
  · simp only [Proof.Scrypt.salsaAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hds⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

theorem main_fdepth : 16 * (Impl.Scrypt.AArch64.blockMixMain Impl.Scrypt.AArch64.salsa).fdepth + 16 < 2 ^ 64 := by
  decide +kernel

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Scrypt.blockMixAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no data). -/
def bmSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixAArch64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.AArch64.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ :=
    BlockMix.correct salsaSpec main_fdepth (pre_of hs).1 (pre_of hs).2
  exact ⟨t, s', he, h⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixAArch64.pre
    Proof.Scrypt.blockMixAArch64.pub Impl.Scrypt.AArch64.blockMix := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem blockMix_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.blockMix (Spec.Scrypt.blockMixContract AArch64.abi
      16) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs,
          Proof.Scrypt.AArch64.BlockMix.bmSat]
          [Proof.Scrypt.AArch64.BlockMix.bmSat] using Proof.Scrypt.AArch64.BlockMix.bmSat }

end VG.Proof.Scrypt.AArch64.BlockMix
