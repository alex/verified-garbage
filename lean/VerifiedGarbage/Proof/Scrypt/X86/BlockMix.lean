import VerifiedGarbage.Proof.Scrypt.X86.Common

/-!
# scryptBlockMix on x86 (32-bit): the loop

As on 32-bit ARM (`Proof/Scrypt/Arm/BlockMixVerified.lean`), the calls of
`vg_salsa20_8` are used through `SalsaSpec`, what its proof says about a call in
a frame of its arguments; the proof of this file holds for any code meeting it.
Pointers are read from the arguments on the stack, which nothing writes; the
calls use the 12 bytes below `esp` (`stkR`), which the memory frames include, as
on x86-64 (`Proof/Scrypt/X86_64/BlockMixCT.lean`).
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_add wp_addi wp_cmp addr_toNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c`, in a frame of its arguments pushed from `eax` and `dR`,
replaces the 64 bytes at `dR` by their Salsa20/8 Core, with the 64 bytes at
`eax` as working space, using the 12 bytes below `esp`. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (dR : Reg) (d sc : BitVec 32), dR ≠ .esp → s.gpr dR = d → s.gpr .eax = sc →
    d.toNat + 64 ≤ 2 ^ 32 → sc.toNat + 64 ≤ 2 ^ 32 →
    Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨sc.setWidth 64, 64⟩ → 12 ≤ (s.gpr .esp).toNat →
    (below (s.gpr .esp) 12).Disjoint ⟨d.setWidth 64, 64⟩ →
    (below (s.gpr .esp) 12).Disjoint ⟨sc.setWidth 64, 64⟩ →
    InRegions s.wr (d.setWidth 64) 64 → InRegions s.wr (sc.setWidth 64) 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨d.setWidth 64, 64⟩, ⟨sc.setWidth 64, 64⟩, below (s.gpr .esp) 12] s.mem s'.mem →
        bytesAt s'.mem (d.setWidth 64) 64 = salsa (bytesAt s.mem (d.setWidth 64) 64) → Q s') →
    WP isa (.frame (.push [.eax, dR]) (.call "vg_salsa20_8" c) (.pop .eax 2)) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev bP : BitVec 32 := arg s₀ 0
abbrev rr : Nat := (arg s₀ 1).toNat
abbrev yP : BitVec 32 := arg s₀ 2
abbrev sc : BitVec 32 := arg s₀ 4
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev yA : Addr := (yP s₀).setWidth 64
abbrev scA : Addr := (sc s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yA s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, 128⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The stack the calls use. -/
abbrev stkR : Region := below (esp₀ s₀) 12
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
/-- `xP`, as the 32-bit pointer in `ebp`. -/
def xP32 : Nat → BitVec 32
  | 0 => bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64)
  | k + 1 => yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (scA s₀ + BitVec.ofNat 64 ·) s₀.gpr bmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀, argR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  a_y : (argR s₀).Disjoint (yR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_y : (stkR s₀).Disjoint (yR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_lo : 12 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32
  r3 : arg s₀ 3 = arg s₀ 1
  pos : 0 < rr s₀

/-- The 12 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 12 ≤ E.toNat) : below E 12 = ⟨E.setWidth 64 - 12, 12⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := stk_eq h16
  simp only [h18] at h2 h3 h4 h6 h8 h11 h14
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by rw [stkR, e]; exact h10, by rw [stkR, e]; exact h11,
    by rw [stkR, e]; exact h12, h13, h14, h15, h16, h17, h18, h19⟩

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
    (yP s₀ + BitVec.ofNat 32 o).setWidth 64 = yA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.y_nw; omega)

theorem b_addr {o : Nat} (h : o < 128 * rr s₀) :
    (bP s₀ + BitVec.ofNat 32 o).setWidth 64 = bA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.b_nw; omega)

theorem y_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (yP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.y_nw
  rw [toNat_add32 (by omega)]; omega

theorem b_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (bP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.b_nw
  rw [toNat_add32 (by omega)]; omega

/-- The argument words are in the arguments' region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (esp₀ s₀) d - addr (esp₀ s₀) 4).toNat + 4 ≤ 20
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains, argAddr] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are kept by anything that writes only `y`, `scratch` and the
stack below `esp`. -/
theorem arg_keep {m : Mem} (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem m) {d : Nat} (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ 24) : m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_y.sub_left (arg_sub hp hd₁ hd)
  · exact hp.a_s.sub_left (arg_sub hp hd₁ hd)
  · exact (stk_arg hp).symm.sub_left (arg_sub hp hd₁ hd)

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
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = bP s₀ + BitVec.ofNat 32 (128 * k)
  esi : s.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * k)
  edi : s.gpr .edi = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  ebp : s.gpr .ebp = xP32 s₀ k
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y`, `scratch` and the stack. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bA s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)
  · exact hp.stk_b.symm.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yA s₀ + BitVec.ofNat 64 o, 64⟩

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .eax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    (hdR : dR ≠ .esp) (hdR' : dR ≠ .eax) {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o) (hesp : s.gpr .esp = esp₀ s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yA s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  have lt := r_lt hp
  unfold salsaAt
  refine WP.seq (wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, hesp])
    (by rw [hrd, hwr]; exact arg_in hp (by omega) (by omega)) fun s₁ u₁ => WP.block_nil ?_)
  have e₁ : s₁.gpr .eax = sc s₀ := by rw [u₁.gpr, arg_keep hp hf (by omega) (by omega)]; rfl
  have e₃ : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r := fun r hr => u₁.other _ (calleeSaved_ne hr)
  have e₄ : s₁.gpr .esp = esp₀ s₀ := by rw [e₃ _ (by simp [calleeSaved]), hesp]
  have ea : (yP s₀ + BitVec.ofNat 32 o).setWidth 64 = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega)
  have hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨scA s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (scA s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₁ dR _ _ hdR (by rw [u₁.other _ hdR', hd]) e₁ (y_fit hp ho) (by have := hp.s_nw; omega)
    (by rw [ea]; exact hp.y_s.sub_left hsub |>.sub_right hsub') (by rw [e₄]; exact hp.sp_lo)
    (by rw [e₄, ea]; exact hp.stk_y.sub_right hsub) (by rw [e₄]; exact hp.stk_s.sub_right hsub')
    (by rw [u₁.wr, hwr, hp.wr, ea]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd' hwr' hcs hf' hb => hQ s' (by rw [hrd', u₁.rd]) (by rw [hwr', u₁.wr])
      (fun r hr => by rw [hcs r hr, e₃ r hr]) (by rw [u₁.mem, ea, e₄] at hf'; exact hf')
      (by rw [ea] at hb; rw [hb, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨scA s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

theorem slot_stk {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint (stkR s₀) :=
  (hp.stk_y.sub_right (y_sub hp ho)).symm

/-- Where `X` is, as an address. -/
theorem xP_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    (xP32 s₀ k).setWidth 64 = xP s₀ k := by
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
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hp4 : p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) := s_sub s₀ (by omega)
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (scA s₀) (o₁ := p.2) (n₁ := 4) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this
  · exact (hp.stk_s.sub_right hsub).symm

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] m m') :
    bytesAt m' (yA s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yA s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact y_disj hp hd ho' ho
  · exact slot_s hp ho'
  · exact slot_stk hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] m m') : Frame [yR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        fun _ h => h⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .eax) (hd' : dR ≠ .esp) (hx : xR ≠ .eax) (hs : sR ≠ .eax) {o : Nat}
    (ho : o + 64 ≤ 128 * rr s₀) {x : BitVec 32} (fx : x.toNat + 64 ≤ 2 ^ 32) {ob : Nat}
    (hob : ob + 64 ≤ 128 * rr s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hesp : s.gpr .esp = esp₀ s₀) (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem)
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 32 ob)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x.setWidth 64, 64⟩)
    (hinx : ∀ i < 16, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (4 * i)) 4)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem (x.setWidth 64) 64)
          (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := r_lt hp
  have ed : (yP s₀ + BitVec.ofNat 32 o).setWidth 64 = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega)
  have eb : (bP s₀ + BitVec.ofNat 32 ob).setWidth 64 = bA s₀ + BitVec.ofNat 64 ob := b_addr hp (by omega)
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_ok hd hx hs (y_fit hp ho) fx (b_fit hp hob) (by rw [ed]; exact hdx)
    (by rw [ed, eb]; exact yb_disj hp ho hob) 16 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, hp.rd, hp.wr, eb, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, hp.wr, ed, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ m₁ => WP.block_nil ?_
  rw [ed, eb, show 4 * 16 = 64 from rfl] at m₁
  have l1 : (xorBytes (bytesAt s.mem (x.setWidth 64) 64)
      (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)).length = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (yA s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  have hf₁ : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₁.mem :=
    hf.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩)
  refine WP.seq (salsaAt_ok hS hp hd' hd ho (by rw [g₁ _ hd, gd]) (by rw [g₁ _ (by decide), hesp])
    (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) hf₁ fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (calleeSaved_ne hr)])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1))
  esi : s.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * k)
  edi : s.gpr .edi = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨scA s₀, 64⟩, stkR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 (128 * k)) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨scA s₀, 64⟩, stkR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
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

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .esi .ebp .ebx)) <| .seq (salsaAt c .esi) <|
      .seq (.block (.alu .add .ebx (.imm 64) :: xor64 .edi .esi .ebx)) <| .seq (salsaAt c .edi) P)
      s Q := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀, argR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  have ex := xP_addr hp hk
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) (by decide) oE (xP_fit hp hk)
    (ob := 128 * k) (by omega) h.rd h.wr h.esp h.frame h.esi h.ebp h.ebx
    (by rw [ex]; exact xP_disj hp hk) (by rw [ex]; exact xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  rw [ex] at b₂
  refine WP.seq (wp_addi fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .ebx → r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  have e3 : s₃.gpr .ebx = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by simp [calleeSaved]), h.ebx, add32_lit]; congr 2; omega
  have hf₂ : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₃.mem := by
    rw [u₃.mem]; exact h.frame.trans (frame_big hp oE f₂)
  have e5 : s₃.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * k) := by
    rw [k3 _ (by decide) (by simp [calleeSaved]), h.esi]
  refine half_ok hS hp (by decide) (by decide) (by decide) (by decide) oO (y_fit hp oE)
    (ob := 64 * (2 * k + 1)) (by omega) (by rw [u₃.rd, rd₂, h.rd]) (by rw [u₃.wr, wr₂, h.wr])
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.esp]) hf₂
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.edi]) e5 e3
    (by rw [y_addr hp (by omega)]; exact y_disj hp (by omega) oO oE)
    (fun i hi => by
      rw [u₃.rd, u₃.wr, rd₂, wr₂, hrd, hwr, y_addr hp (by omega), add_ofNat]
      exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₅ rd₅ wr₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem, y_addr hp (by omega)] at b₅
  rw [u₃.mem] at f₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .ebx → r ∈ calleeSaved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, u₃.rd, rd₂, h.rd], by rw [wr₅, u₃.wr, wr₂, h.wr],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.esp],
    by rw [cs₅ _ (by simp [calleeSaved]), e3],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.esi],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.edi], F, S, D⟩

/-- `y + 64 (k + 1)` is `y + 64 r` exactly when `k + 1 = r`. -/
theorem cmp_end (y : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (y + BitVec.ofNat 32 a - (BitVec.ofNat 32 b + y) == 0) = decide (a = b) := by
  rw [show y + BitVec.ofNat 32 a - (BitVec.ofNat 32 b + y) = BitVec.ofNat 32 a - BitVec.ofNat 32 b by
    bv_omega]
  exact Proof.Sha256.X86.Stream.sub_beq ha hb

theorem bmNext_eq : bmNext = .mov .ebp (.reg .edi) :: .alu .add .ebx (.imm 64) ::
    .alu .add .esi (.imm 64) :: .alu .add .edi (.imm 64) ::
    (timesR 64 ++ ([.mov .ecx (.mem (at_ .esp 12)), .alu .add .eax (.reg .ecx), .alu .cmp .esi (.reg .eax)] :
      List Instr)) := rfl

/-- The pointers move on, and ZF is set after the last pair. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block bmNext) s fun s' => Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = rr s₀)) := by
  have lt := r_lt hp
  rw [bmNext_eq]
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_addi fun s₉ u₉ => ?_
  have m₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g₉ : ∀ r, r ≠ .ebp → r ≠ .ebx → r ≠ .esi → r ≠ .edi → s₉.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, u₆.other _ h1]
  have esp₉ : s₉.gpr .esp = esp₀ s₀ := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), h.esp]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  refine timesR_ok (r := arg s₀ 1) (by rw [esp₉, m₉, arg_keep hp h.frame (by omega) (by omega)]; rfl)
    (by rw [esp₉, rd₉, wr₉]; exact arg_in hp (by omega) (by omega)) fun t e o mt rdt wrt => ?_
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, o _ (by decide) (by decide) (by decide), esp₉])
    (by rw [rdt, wrt, rd₉, wr₉]; exact arg_in hp (by omega) (by omega)) fun t₀ u₀ => ?_
  refine wp_add fun t₁ u₁ => wp_cmp fun t₂ f₂ _ z₂ => WP.block_nil ?_
  have gt : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = s₉.gpr r := fun r h1 h2 h3 => by
    rw [f₂.gpr, u₁.other _ h1, u₀.other _ h2, o r h1 h2 h3]
  have mt₂ : t₂.mem = s.mem := by rw [f₂.mem, u₁.mem, u₀.mem, mt, m₉]
  have esi₉ : s₉.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * (k + 1)) := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), h.esi, add32_lit]
    congr 2
  refine ⟨⟨(by omega), by rw [f₂.rd, u₁.rd, u₀.rd, rdt, rd₉], by rw [f₂.wr, u₁.wr, u₀.wr, wrt, wr₉],
    by rw [gt _ (by decide) (by decide) (by decide), esp₉], ?_, ?_, ?_, ?_,
    by rw [mt₂]; exact h.frame, by rw [mt₂]; exact h.saved, by rw [mt₂]; exact h.done, ?_⟩, ?_⟩
  · rw [gt _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, u₆.other _ (by decide), h.ebx, add32_lit]
    congr 2; omega
  · rw [gt _ (by decide) (by decide) (by decide), esi₉]
  · rw [gt _ (by decide) (by decide) (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.edi, add32_lit]
    congr 2
  · rw [gt _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.edi]
    rfl
  · rw [mt₂]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl
  · have hax : t₁.gpr .eax = BitVec.ofNat 32 (64 * rr s₀) + yP s₀ := by
      rw [u₁.gpr, u₀.gpr, u₀.other _ (by decide), e, mt, m₉, arg_keep hp h.frame (by omega) (by omega),
        show (64 : BitVec 32).toNat = 64 from rfl, Nat.mul_comm]
      rfl
    rw [z₂, u₁.other _ (by decide), u₀.other _ (by decide), o _ (by decide) (by decide) (by decide), esi₉,
      hax,
      cmp_end _ (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (bmBody c) s fun s' => Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = rr s₀)) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.X86.BlockMix
