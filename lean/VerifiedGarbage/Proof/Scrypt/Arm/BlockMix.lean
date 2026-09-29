import VerifiedGarbage.Proof.Scrypt.Arm.Common

/-!
# scryptBlockMix on 32-bit ARM: the loop

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Scrypt/AArch64/BlockMix.lean`), the calls of `vg_salsa20_8` are used
through `SalsaSpec`, what its proof says about a call; the proof of this file
holds for any code meeting it. Registers hold 32-bit pointers, and memory is
addressed by their zero extensions (`State.addr`), which do not wrap.
-/

namespace VG.Proof.Scrypt.Arm.BlockMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.Arm.Stream (Upd wp_mov wp_add op2_reg op2_imm)
open VG.Proof.Scrypt.X86_64.BlockMix (toNat_ofNat_lt add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c` replaces the 64 bytes at `r0` by their Salsa20/8 Core,
with the 64 bytes at `r1` as working space. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (d sc : BitVec 32), s.gpr .r0 = d → s.gpr .r1 = sc →
    d.toNat + 64 ≤ 2 ^ 32 → sc.toNat + 64 ≤ 2 ^ 32 →
    Region.Disjoint ⟨State.addr d, 64⟩ ⟨State.addr sc, 64⟩ → InRegions s.wr (State.addr d) 64 →
    InRegions s.wr (State.addr sc) 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
        Frame [⟨State.addr d, 64⟩, ⟨State.addr sc, 64⟩] s.mem s'.mem →
        bytesAt s'.mem (State.addr d) 64 = salsa (bytesAt s.mem (State.addr d) 64) → Q s') →
    WP isa (.call "vg_salsa20_8" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : BitVec 32 := s₀.gpr .r0
abbrev rr : Nat := (s₀.gpr .r1).toNat
abbrev yP : BitVec 32 := s₀.gpr .r2
abbrev sc : BitVec 32 := stackArg s₀ 0
abbrev bA : Addr := State.addr (bP s₀)
abbrev yA : Addr := State.addr (yP s₀)
abbrev scA : Addr := State.addr (sc s₀)
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yA s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, 128⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yA s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yA s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k
/-- `xP`, as the 32-bit pointer in `r9`. -/
def xP32 : Nat → BitVec 32
  | 0 => bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64)
  | k + 1 => yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))

/-- The caller's `r4`–`r9` and our return address are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ bmSaved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

/-- The callee-saved registers the code never writes. -/
def others : List Reg := [.r10, .r11]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀, argR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  a_y : (argR s₀).Disjoint (yR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_nw : s₀.sp.toNat + 4 ≤ 2 ^ 32
  r3 : s₀.gpr .r3 = s₀.gpr .r1
  pos : 0 < rr s₀

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 32 := by
  by_contra hc
  have hy : yA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.y_nw; omega
  have hs : (scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (sc s₀).isLt
  refine hp.y_s (scA s₀) ?_ ?_
  · show (scA s₀ - yA s₀).toNat + 1 ≤ rr s₀ * 128
    rw [hy, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega
  · show (scA s₀ - scA s₀).toNat + 1 ≤ 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yA s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bA s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

/-- A pointer into `y`, as an address. -/
theorem y_addr {o : Nat} (h : o < 128 * rr s₀) :
    State.addr (yP s₀ + BitVec.ofNat 32 o) = yA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.y_nw; omega)

theorem b_addr {o : Nat} (h : o < 128 * rr s₀) :
    State.addr (bP s₀ + BitVec.ofNat 32 o) = bA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.b_nw; omega)

theorem y_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (yP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.y_nw
  rw [toNat_add32 (by omega)]; omega

theorem b_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (bP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.b_nw
  rw [toNat_add32 (by omega)]; omega

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀ + BitVec.ofNat 32 (128 * k)
  r5 : s.gpr .r5 = yP s₀ + BitVec.ofNat 32 (64 * k)
  r6 : s.gpr .r6 = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  r7 : s.gpr .r7 = sc s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (rr s₀ - k)
  r9 : s.gpr .r9 = xP32 s₀ k
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
    bytesAt m (bA s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yA s₀ + BitVec.ofNat 64 o, 64⟩

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (hd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o)
    (h7 : s.gpr .r7 = sc s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yA s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_)
  have e₁ : s₂.gpr .r0 = yP s₀ + BitVec.ofNat 32 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  have e₂ : s₂.gpr .r1 = sc s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h7]
  have e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (pres_ne r hr).2.1, u₁.other _ (pres_ne r hr).1]
  have ea : State.addr (yP s₀ + BitVec.ofNat 32 o) = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega)
  have hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨scA s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (scA s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₂ _ _ e₁ e₂ (y_fit hp ho) (by have := hp.s_nw; omega)
    (by rw [ea]; exact hp.y_s.sub_left hsub |>.sub_right hsub')
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr, ea]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr hlr => by rw [hcs r hr hlr, e₃ r hr])
      (by rw [u₂.mem, u₁.mem, ea] at hf; exact hf) (by rw [ea] at hb; rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨scA s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

/-- Where `X` is, as an address. -/
theorem xP_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    State.addr (xP32 s₀ k) = xP s₀ k := by
  cases k with
  | zero => exact b_addr hp (by have := hp.pos; omega)
  | succ j => exact y_addr hp (by omega)

theorem xP_fit {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    (xP32 s₀ k).toNat + 64 ≤ 2 ^ 32 := by
  cases k with
  | zero => exact b_fit hp (by have := hp.pos; omega)
  | succ j => exact y_fit hp (by omega)

theorem xP_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀, argR s₀]) (hwr : s.wr = [yR s₀, scR s₀]) :
    ∀ i < 16, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (4 * i)) 4 := by
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
  | succ j => exact y_disj hp (by omega) (by omega) (by omega)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hp4 : p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) := s_sub s₀ (by omega)
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (scA s₀) (o₁ := p.2) (n₁ := 4) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩] m m') :
    bytesAt m' (yA s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yA s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho
  · exact slot_s hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩] m m') : Frame [yR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .r2 ∧ dR ≠ .r3) (hx : xR ≠ .r2 ∧ xR ≠ .r3) (hs : sR ≠ .r2 ∧ sR ≠ .r3)
    {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {x : BitVec 32} (fx : x.toNat + 64 ≤ 2 ^ 32) {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) {s : State}
    (hrd : s.rd = [bR s₀, argR s₀]) (hwr : s.wr = [yR s₀, scR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 32 ob) (h7 : s.gpr .r7 = sc s₀)
    (hdx : Region.Disjoint (slot s₀ o) ⟨State.addr x, 64⟩)
    (hinx : ∀ i < 16, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * i)) 4)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem (State.addr x) 64)
          (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := r_lt hp
  have ed : State.addr (yP s₀ + BitVec.ofNat 32 o) = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega)
  have eb : State.addr (bP s₀ + BitVec.ofNat 32 ob) = bA s₀ + BitVec.ofNat 64 ob := b_addr hp (by omega)
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_ok hd hx hs (y_fit hp ho) fx (b_fit hp hob) (by rw [ed]; exact hdx)
    (by rw [ed, eb]; exact yb_disj hp ho hob) 16 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, eb, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, ed, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  rw [ed, eb] at m₁
  have l1 : (xorBytes (bytesAt s.mem (State.addr x) 64)
      (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)).length = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (yA s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hS hp ho (by rw [g₁ _ hd.1 hd.2, gd]) (by rw [g₁ _ (by decide) (by decide), h7])
    (by rw [wr₁, hwr, hp.wr]) fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr hlr => by rw [cs₂ r hr hlr, g₁ r (pres_ne r hr).2.2.1 (pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1))
  r5 : s.gpr .r5 = yP s₀ + BitVec.ofNat 32 (64 * k)
  r6 : s.gpr .r6 = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  r7 : s.gpr .r7 = sc s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨scA s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 (128 * k)) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨scA s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
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
  have hb : bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
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

theorem others_pres : ∀ r ∈ others, r ∈ preserved ∧ r ≠ .lr ∧ r ≠ .r4 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .r5 .r9 .r4)) <| .seq (salsaAt c .r5) <|
      .seq (.block (.dp .add .r4 .r4 (.imm 64) :: xor64 .r6 .r5 .r4)) <| .seq (salsaAt c .r6) P)
      s Q := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀, argR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  have ex := xP_addr hp hk
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) oE (xP_fit hp hk) (ob := 128 * k)
    (by omega) hrd hwr h.r5 h.r9 h.r4 h.r7 (by rw [ex]; exact xP_disj hp hk)
    (by rw [ex]; exact xP_in hp hk hrd hwr) fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  rw [ex] at b₂
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other _ h1, cs₂ r h2 h3]
  have e3 : s₃.gpr .r4 = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide) (by decide), h.r4, add32_lit]; congr 2; omega
  have hrd₃ : s₃.rd = [bR s₀, argR s₀] := by rw [u₃.rd, rd₂, hrd]
  have hwr₃ : s₃.wr = [yR s₀, scR s₀] := by rw [u₃.wr, wr₂, hwr]
  have e5 : s₃.gpr .r5 = yP s₀ + BitVec.ofNat 32 (64 * k) := by
    rw [k3 _ (by decide) (by decide) (by decide), h.r5]
  refine half_ok hS hp (by decide) (by decide) (by decide) oO (y_fit hp oE) (ob := 64 * (2 * k + 1))
    (by omega) hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide) (by decide), h.r6]) e5 e3
    (by rw [k3 _ (by decide) (by decide) (by decide), h.r7])
    (by rw [y_addr hp (by omega)]; exact y_disj hp (by omega) oO oE)
    (fun i hi => by
      rw [hrd₃, hwr₃, y_addr hp (by omega), add_ofNat]
      exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem, y_addr hp (by omega)] at b₅
  rw [u₃.mem] at f₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [cs₅ r h2 h3, k3 r h1 h2 h3]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide) (by decide), e3],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r5],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r6],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r7],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r8],
    fun r hr => by
      rw [k5 r (others_pres r hr).2.2 (others_pres r hr).1 (others_pres r hr).2.1, h.keep r hr],
    F, S, D⟩

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [.mov .r9 (.reg .r6), .dp .add .r4 .r4 (.imm 64), .dp .add .r5 .r5 (.imm 64),
      .dp .add .r6 .r6 (.imm 64), .subs .r8 .r8 (.imm 1)]) s
      fun s' => Inv s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = rr s₀) := by
  have lt := r_lt hp
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₇ u₇ =>
    wp_add (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ =>
    Proof.Sha256.Arm.Stream.wp_subs (op2_imm (by decide)) fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r8 → r ≠ .r9 → s₁₀.gpr r = s.gpr r :=
    fun r h4 h5 h6 h8 h9 => by
      rw [u₁₀.other _ h8, u₉.other _ h6, u₈.other _ h5, u₇.other _ h4, u₆.other _ h9]
  have e8 : s₁₀.gpr .r8 = BitVec.ofNat 32 (rr s₀ - (k + 1)) := by
    rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r8, ofNat_pred32 (by omega), Nat.sub_sub]
  refine ⟨⟨(by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, e8, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.r4, add32_lit]
    congr 2; omega
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.r5, add32_lit]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r6, add32_lit]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.r6]
    rfl
  · intro r hr
    have : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r8 ∧ r ≠ .r9 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl
  · rw [z₁₀, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r8,
      ofNat_pred32 (by omega), Proof.Sha256.Arm.Stream.ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]
    omega

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (bmBody c) s fun s' => Inv s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = rr s₀) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.Arm.BlockMix
