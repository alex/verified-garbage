import VerifiedGarbage.Proof.Sha512.X86.Stream.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.ArgTaint

/-!
# Streaming SHA-512 on x86 (32-bit): `update`

The structure of the ARMv7 proof (`VG.Proof.Sha512.Arm.Stream.Update`), with
`state` in `ebx`, `data` in `esi`, the bytes left in `ebp` and the buffered
bytes in `edi`; every block goes through the buffer, which is compressed as
soon as it is full, by calling the compression function (`compressAt_ok`) with
the 20 bytes below `esp` for its frame.
-/

namespace VG.Proof.Sha512.X86.Stream.Update

open VG VG.X86 VG.Impl.Sha512.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_movzx8 wp_store wp_store8 wp_add
  wp_addi wp_sub wp_subi wp_andi wp_cmp wp_cmpi wp_test contains_addr sub_offset frame_bytes addr_add_ofNat
  readW_writeW_addr ofNat_beq_zero sub_ofNat sub_beq ofNat_succ ofNat_pred toNat_ofNat_lt bytesAt_getD
  addr_toNat)
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt)
open VG.Proof.Sha512 (countX86)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 192⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 272⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dA s₀) (len s₀)

/-- The messages the initial state represents, from the initial hash value `iv`. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (stA s₀) m ∧ countX86 s₀ = BitVec.ofNat 64 m.length

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  st_fit : (st s₀).toNat + 192 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 272 ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Sha512.updateX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have e := stk_eq h16
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by show (below _ _).Disjoint _; rw [e]; exact h10,
    by show (below _ _).Disjoint _; rw [e]; exact h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    h13, h14, h15, h16, h17⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 128 = (arg s₀ 1).toNat % 128 := by
  simp only [cnt, countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) :
    cnt s₀ % 128 = m.length % 128 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 272) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 272) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 24⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 24⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (esp₀ s₀) 4, 24⟩ (below (esp₀ s₀) 20)
  rw [stk_eq hp.sp_lo, addr_eq (by omega)]
  exact (Offset.disjoint_below_above (m := 20) (a := 4) _ (by omega)).symm

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ (below (esp₀ s₀) 20)
  rw [stk_eq hp.sp_lo]
  have h := Offset.disjoint_below_above ((esp₀ s₀).setWidth 64) (m := 20) (a := 0) (l := 4) (by omega)
  rw [show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 0 = (esp₀ s₀).setWidth 64 from BitVec.add_zero _] at h
  exact h.symm

/-- The words of the scratch space from 224 on (the saved registers) are
outside the regions the compression function writes. -/
theorem saved_sep {d : Nat} (hd₁ : 224 ≤ d) (hd : d + 4 ≤ 272) :
    ∀ r ∈ [(⟨stA s₀, 64⟩ : Region), ⟨scA s₀, 224⟩, stkR s₀], Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r := by
  have := hp.scr_fit
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.st_scr.symm.sub_left (hp.scr_sub hd)).sub_right (Region.sub_prefix (by omega))
  · rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd₁ (by omega)
  · exact (hp.stk_scr.symm.sub_left (hp.scr_sub hd))

end Pre

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  ebp : s.gpr .ebp = BitVec.ofNat 32 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  edi : s.gpr .edi = BitVec.ofNat 32 ((cnt s₀ + c) % 128)
  repr : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.Repr iv s.mem (stA s₀) (m ++ (D s₀).take c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .esi, .ebp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  esp := by rw [hg _ (by simp)]; exact h.esp
  esi := by rw [hg _ (by simp)]; exact h.esi
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .esi, .ebp, .edi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [Reg.edi] hr)) hm hrd hwr with
    edi := by rw [hg _ (by simp)]; exact h.edi
    repr := by rw [hm]; exact h.repr }

theorem Inv.of_upd {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ [Reg.ebx, .esp, .esi, .ebp, .edi]) : Inv s₀ c s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr

theorem Inv.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s) (u : Fupd s s') : Inv s₀ c s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr

/-- The argument words are never written. -/
theorem Common.arg {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {d : Nat}
    (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    s.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine h.frame.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by have := len_lt s₀; show len s₀ ≤ 2 ^ 64; omega) hi

theorem length_mid (s₀ : State) {iv : HashValue} {m : List Byte} (hm : R₀ s₀ iv m) {c : Nat}
    (hc : c ≤ len s₀) : (m ++ (D s₀).take c).length % 128 = (cnt s₀ + c) % 128 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Buffering data -/

section
variable (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 128
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (128 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := stA s₀ + 64 + BitVec.ofNat 64 (rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 128 := Nat.mod_lt _ (by omega)
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 128 - rr s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 128 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (128 - rr s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q s₀ c = stA s₀ + BitVec.ofNat 64 (64 + rr s₀ c) := by
  simp only [q, BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 (c + j)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  edi : s.gpr .edi = BitVec.ofNat 32 (rr s₀ c + j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (tt s₀ c - j)
  mem : s.mem = writeBytes mI (q s₀ c) ((xs s₀ c).take j)

theorem write_frame (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR s₀] mI (writeBytes mI (q s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .edx (at_ .esi 0), .mov .eax (.reg .ebx), .alu .add .eax (.reg .edi),
   .store8 (at_ .eax 64) .dl, .alu .add .esi (.imm 1), .alu .add .edi (.imm 1),
   .alu .sub .ecx (.imm 1)]

theorem copy_step {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {j : Nat}
    (hj : j < tt s₀ c) {s : State} (h : Copy s₀ c sI.mem j s) :
    WP isa (.block copyBody) s fun s' =>
      Copy s₀ c sI.mem (j + 1) s' ∧ s'.zf = some (BitVec.ofNat 32 (tt s₀ c - (j + 1)) == 0) := by
  have hlen := len_lt s₀; have hd := hp.d_fit; have hst := hp.st_fit
  have hc := hI.c_le
  have hr := rr_lt s₀ c
  have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dA s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dA s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have hq : q s₀ c + BitVec.ofNat 64 j = stA s₀ + BitVec.ofNat 64 (rr s₀ c + j + 64) := by
    rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hout : InRegions s.wr (q s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by rw [hq]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length s₀ c
  unfold copyBody
  refine wp_movzx8 (a := dA s₀ + BitVec.ofNat 64 (c + j))
    (by rw [ea_at, h.esi, addr_add_ofNat (by omega), Nat.add_zero]) hin fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  refine wp_store8 (r := .dl) (a := q s₀ c + BitVec.ofNat 64 j) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hout) fun s₄ u₄ => ?_
  · rw [ea_at, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide), h.ebx,
      h.edi, hq, addr_add_ofNat (by omega)]
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_subi fun s₇ u₇ z₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .edx → r ≠ .eax → r ≠ .esi → r ≠ .edi → r ≠ .ecx → s₇.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.gpr, u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have h8 : s₇.gpr .ecx = BitVec.ofNat 32 (tt s₀ c - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx, ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_⟩, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide) (by decide) (by decide), h.esp]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esi, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .ebp (by decide) (by decide) (by decide) (by decide) (by decide), h.ebp]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.edi, ← ofNat_succ, Nat.add_assoc]
  · have hj' : j < (xs s₀ c).length := by omega
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.dl.reg = Reg.edx from rfl,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 32).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]
  · rw [z₇, ← u₇.gpr, h8]

theorem copy_loop_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block copyBody) .ne) s (Copy s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hp hI hj hc) fun s' ⟨hc', hz'⟩ => ?_
  have hz : isa.eval .ne s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
    show s'.zf.map (!·) = _
    rw [hz', ofNat_beq_zero (by have := tt_le' s₀ c; omega)]
    simp
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) :
    let mem := writeBytes sI.mem (q s₀ c) (xs s₀ c)
    Frame [stR s₀, scR s₀, stkR s₀] s₀.mem mem ∧ Saved s₀ mem ∧
      stateAt mem (stA s₀) = stateAt sI.mem (stA s₀) ∧
      bytesAt mem (stA s₀ + 64) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (stA s₀ + 64) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hf : Frame [stR s₀] sI.mem mem := by
    have := write_frame s₀ c sI.mem (tt s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · have hd : 224 ≤ p.2 ∧ p.2 + 4 ≤ 240 := by
      simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [← hI.saved p hp']
    refine hf.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    exact hp.st_scr.symm.sub_left (hp.scr_sub (by omega))
  · apply stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- What the call of the compression function needs. -/
theorem Common.atPre {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hC : Common s₀ c s) :
    AtPre (st s₀) (scr s₀) (esp₀ s₀) 24 s :=
  ⟨hC.esp, hC.ebx, ⟨argR s₀, by simp [hC.rd, hp.rd], hp.arg_in (by omega) (by omega)⟩,
    by rw [hC.arg hp (by omega) (by omega)]; rfl, by simp [hC.wr, hp.wr], by simp [hC.wr, hp.wr]⟩

/-- Once the bytes are copied. -/
theorem Copy.common {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) : Common s₀ (c + tt s₀ c) s := by
  have ht := tt_le s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, -, -⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  exact ⟨by omega, h.rd, h.wr, h.ebx, h.esp, h.esi, by rw [h.ebp, Nat.sub_sub], by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩

/-- The call of the compression function on the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hC : Common s₀ c s) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ c s' → (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s'.gpr r = s.gpr r) →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (stA s₀ + 64)) → Q s') :
    WP isa (compressAt 24) s Q := by
  refine compressAt_ok hp.st_fit hp.scr_fit hp.sp_lo hp.st_scr hp.stk_st hp.stk_scr (hC.atPre hp)
    fun s' hrd hwr hg hf hst => hQ s' ⟨hC.c_le, hrd.trans hC.rd, hwr.trans hC.wr,
      by rw [hg _ (by simp)]; exact hC.ebx, by rw [hg _ (by simp)]; exact hC.esp,
      by rw [hg _ (by simp)]; exact hC.esi, by rw [hg _ (by simp)]; exact hC.ebp,
      hC.frame.trans (hf.sub fun r hr => ?_), fun p hp' => ?_⟩ hg hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have hd : 224 ≤ p.2 ∧ p.2 + 4 ≤ 240 := by
      simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [← hC.saved p hp']
    exact hf.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _)
      (hp.saved_sep hd.1 (by omega)) (by decide)

/-- A full buffer: compress it. -/
theorem fill_full {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hfull : rr s₀ c + tt s₀ c = 128) :
    WP isa (.seq (compressAt 24) (.block [.mov .edi (.imm 0)])) s (Inv s₀ (c + tt s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, hstt, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  have hC : Common s₀ (c + tt s₀ c) s := h.common hp hI
  refine WP.seq (compress_buf hp hC fun s' hC' _ hstate => ?_)
  refine wp_movi fun s'' u => WP.block_nil ?_
  refine ⟨hC'.of_gpr (fun r hr => u.other r ?_) u.mem u.rd u.wr, ?_, fun iv m hm => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [u.gpr]
    show 0 = BitVec.ofNat 32 ((cnt s₀ + (c + tt s₀ c)) % 128)
    rw [show (cnt s₀ + (c + tt s₀ c)) % 128 = 0 by have := rr_eq s₀ c; omega]; rfl
  · rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine repr_append_block (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [u.mem, hstate, hmem, hstt]
    refine congrArg (compress _) (parseBlock_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 128 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hnf : rr s₀ c + tt s₀ c ≠ 128) : Inv s₀ (len s₀) s := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hstt, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine ⟨⟨(Nat.le_refl _), h.rd, h.wr, h.ebx, h.esp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩
  · rw [h.esi]; congr 2; omega
  · rw [h.ebp]; congr 1; omega
  · rw [h.edi]; congr 1; omega
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega, ← take_add_data]
    refine repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hstt]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill =
    .seq (.block [.mov .ecx (.imm 128), .alu .sub .ecx (.reg .edi), .alu .cmp .ebp (.reg .ecx)])
    (.seq (.ite .b (.block [.mov .ecx (.reg .ebp)]) (.block []))
    (.seq (.block [.alu .sub .ebp (.reg .ecx)])
    (.seq (.loop (.block copyBody) .ne)
    (.seq (.block [.alu .cmp .edi (.imm 128)])
      (.ite .e (.seq (compressAt 24) (.block [.mov .edi (.imm 0)])) (.block [])))))) := rfl

/-- The bytes consumed after an iteration that started with `c`. -/
def nextC (s₀ : State) (c : Nat) : Nat := if rr s₀ c + tt s₀ c = 128 then c + tt s₀ c else len s₀

/-- `fill` before the test of whether the buffer is full, and after. -/
def fillPre : Prog isa :=
  .seq (.seq (.seq (.seq (.block [.mov .ecx (.imm 128), .alu .sub .ecx (.reg .edi), .alu .cmp .ebp (.reg .ecx)])
    (.ite .b (.block [.mov .ecx (.reg .ebp)]) (.block [])))
    (.block [.alu .sub .ebp (.reg .ecx)]))
    (.loop (.block copyBody) .ne))
    (.block [.alu .cmp .edi (.imm 128)])

def fillEnd : Prog isa := .ite .e (.seq (compressAt 24) (.block [.mov .edi (.imm 0)])) (.block [])

theorem nextC_gt (s₀ : State) {c : Nat} (hcl : c < len s₀) : c < nextC s₀ c := by
  have := tt_eq s₀ c; have := rr_lt s₀ c
  simp only [nextC]; split <;> omega

theorem pre_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa fillPre s fun s' => AtPre (st s₀) (scr s₀) (esp₀ s₀) 24 s' ∧
      s'.zf = some (decide (rr s₀ c + tt s₀ c = 128)) ∧ WP isa fillEnd s' (Inv s₀ (nextC s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hc := hI.c_le; have hlen := len_lt s₀
  unfold fillPre
  refine WP.seq (WP.seq (WP.seq (WP.seq ?_)))
  -- `ecx := 128 - r`, compared with the bytes left.
  refine (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ f₃ cf₃ _ => WP.block_nil ?_)
  have hI₃ : Inv s₀ c s₃ := ((hI.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_flags f₃
  have hecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (128 - rr s₀ c) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.edi,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, sub_ofNat (by omega)]
  have hecx₃ : s₃.gpr .ecx = BitVec.ofNat 32 (128 - rr s₀ c) := by rw [f₃.gpr, hecx₂]
  have hm₃ : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have hcf : s₃.cf = some (decide (len s₀ - c < 128 - rr s₀ c)) := by
    rw [cf₃, u₂.other _ (by decide), u₁.other _ (by decide), hI.ebp, hecx₂, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega)]
  -- `ecx := min(ecx, len)`
  refine (WP.mono (Q := fun (s₅ : State) => Inv s₀ c s₅ ∧ s₅.gpr .ecx = BitVec.ofNat 32 (tt s₀ c) ∧
    s₅.mem = s.mem) ?_ fun s₅ ⟨hI₅, h8₅, hm₅⟩ => ?_)
  · refine WP.ite (decide (len s₀ - c < 128 - rr s₀ c)) (by show s₃.cf = _; exact hcf)
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov fun s₄ u₄ => WP.block_nil ⟨hI₃.of_upd u₄ (by decide), ?_, by rw [u₄.mem, hm₃]⟩
      rw [u₄.gpr, hI₃.ebp]; congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₃, ?_, hm₃⟩
      rw [hecx₃]; congr 1; omega
  -- `ebp -= ecx`
  refine (wp_sub fun s₆ u₆ _ => WP.block_nil ?_)
  have hC₀ : Copy s₀ c s.mem 0 s₆ := by
    have e : ∀ r, r ≠ .ebp → s₆.gpr r = s₅.gpr r := fun r h => u₆.other r h
    refine ⟨Nat.zero_le _, by rw [u₆.rd, hI₅.rd], by rw [u₆.wr, hI₅.wr],
      by rw [e _ (by decide), hI₅.ebx], by rw [e _ (by decide), hI₅.esp],
      by rw [e _ (by decide), hI₅.esi, Nat.add_zero], ?_,
      by rw [e _ (by decide), hI₅.edi, Nat.add_zero], by rw [e _ (by decide), h8₅, Nat.sub_zero], ?_⟩
    · rw [u₆.gpr, hI₅.ebp, h8₅, sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₆.mem, hm₅, List.take_zero, writeBytes_nil]
  -- Copy the bytes.
  refine (WP.mono (copy_loop_ok hp hI hC₀ (by omega)) fun s₇ hC => ?_)
  -- Is the buffer full?
  refine (wp_cmpi fun s₈ f₈ _ z₈ => WP.block_nil ?_)
  have hC₈ : Copy s₀ c s.mem (tt s₀ c) s₈ :=
    ⟨hC.j_le, by rw [f₈.rd, hC.rd], by rw [f₈.wr, hC.wr], by rw [f₈.gpr, hC.ebx], by rw [f₈.gpr, hC.esp],
      by rw [f₈.gpr, hC.esi], by rw [f₈.gpr, hC.ebp], by rw [f₈.gpr, hC.edi], by rw [f₈.gpr, hC.ecx],
      by rw [f₈.mem, hC.mem]⟩
  have hz : s₈.zf = some (decide (rr s₀ c + tt s₀ c = 128)) := by
    rw [z₈, hC.edi, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, sub_beq (by omega) (by omega)]
  refine ⟨(hC₈.common hp hI).atPre hp, hz,
    WP.ite (decide (rr s₀ c + tt s₀ c = 128)) (by show s₈.zf = _; exact hz) (fun hb => ?_) (fun hb => ?_)⟩
  · simp only [decide_eq_true_eq] at hb
    have e : nextC s₀ c = c + tt s₀ c := by simp only [nextC]; split <;> omega
    rw [e]
    exact fill_full hp hI hC₈ hb
  · simp only [decide_eq_false_iff_not] at hb
    have e : nextC s₀ c = len s₀ := by simp only [nextC]; split <;> omega
    rw [e]
    exact WP.block_nil (fill_done hp hI hC₈ hb)

theorem fill_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa fill s fun s' => ∃ c', c < c' ∧ Inv s₀ c' s' := by
  rw [fill_eq]
  exact WP.assoc (WP.assoc (WP.assoc (WP.assoc (WP.seq (WP.mono (pre_ok hp hI hcl)
    fun _ h => WP.mono h.2.2 fun _ h => ⟨_, nextC_gt s₀ hcl, h⟩)))))

/-! ## One iteration -/

/-- The loop's test: bytes left? -/
theorem test_ok {s₀ : State} {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa (.block [.alu .test .ebp (.reg .ebp)]) s fun s' =>
      Inv s₀ c s' ∧ s'.zf = some (decide (len s₀ - c = 0)) := by
  have hlen := len_lt s₀
  have hc'' := hI.c_le
  refine wp_test fun s'' f'' z'' => WP.block_nil ⟨hI.of_flags f'', ?_⟩
  rw [z'', hI.ebp, BitVec.and_self, ofNat_beq_zero (by omega)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa updateBody s fun s' => ∃ c', c < c' ∧ Inv s₀ c' s' ∧ s'.zf = some (decide (len s₀ - c' = 0)) :=
  WP.seq (WP.mono (fill_ok hp hI hcl) fun _ ⟨c', hc', hI'⟩ =>
    WP.mono (test_ok hI') fun _ h => ⟨c', hc', h⟩)

/-! ## Prologue and epilogue -/

/-- The memory after saving our caller's registers. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 224) (s₀.gpr .ebx)).writeW (addr (scr s₀) 228) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 232) (s₀.gpr .edi)).writeW (addr (scr s₀) 236) (s₀.gpr .ebp)

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d, d + 4 ≤ 272 → (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 224 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 228 (by omega))).writeW (List.mem_singleton_self _) _
    (c 232 (by omega))).writeW (List.mem_singleton_self _) _ (c 236 (by omega))

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 272 → e + 4 ≤ 272 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ 224 236 (by omega) (by omega) (by omega), w _ _ 224 232 (by omega) (by omega) (by omega),
      w _ _ 224 228 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 228 236 (by omega) (by omega) (by omega), w _ _ 228 232 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [w _ _ 232 236 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- The prologue. -/
def proBlock : List Instr :=
  [.mov .eax (.mem (at_ .esp 24)), .store (at_ .eax 224) .ebx, .store (at_ .eax 228) .esi,
   .store (at_ .eax 232) .edi, .store (at_ .eax 236) .ebp,
   .mov .ebx (.mem (at_ .esp 4)), .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 127),
   .mov .esi (.mem (at_ .esp 16)), .mov .ebp (.mem (at_ .esp 20)), .alu .test .ebp (.reg .ebp)]

theorem update_eq : update = .seq (.block proBlock)
    (.seq (.ite .e (.block []) (.loop updateBody .ne)) (.block (.mov .eax (.mem (at_ .esp 24)) :: restore))) :=
  rfl

theorem beq_zero (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  rw [← ofNat_beq_zero x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block proBlock) s₀ fun s => Inv s₀ 0 s ∧ s.zf = some (decide (len s₀ = 0)) := by
  have hsp := hp.sp_fit; have hsc := hp.scr_fit; have hst := hp.st_fit
  have ain : ∀ e, 4 ≤ e → e + 4 ≤ 28 → ∀ t : State, t.rd = s₀.rd → t.wr = s₀.wr →
      InRegions (t.rd ++ t.wr) (addr (esp₀ s₀) e) 4 :=
    fun e h₁ h₂ t hrd hwr => ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩
  have sout : ∀ d, d + 4 ≤ 272 → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (scr s₀) d) 4 :=
    fun d hd t hwr => ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩
  have ard : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (saveMem s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => (saveMem_frame hp).readW (Region.contains_self _ _)
      (by simpa using hp.a_scr.sub_left (hp.arg_sub h₁ h₂)) (by decide)
  unfold proBlock
  refine wp_movm (a := addr (esp₀ s₀) 24) (ea_at _ _ _) (ain 24 (by omega) (by omega) s₀ rfl rfl)
    fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 224) (by rw [ea_at, e₁]) (sout 224 (by omega) _ u₁.wr) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 228) (by rw [ea_at, u₂.gpr, e₁])
    (sout 228 (by omega) _ (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 232) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (sout 232 (by omega) _ (by rw [u₃.wr, u₂.wr, u₁.wr])) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 236) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (sout 236 (by omega) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    rfl
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, sp₅]) (ain 4 (by omega) (by omega) s₅ rd₅ wr₅)
    fun s₆ u₆ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (ain 8 (by omega) (by omega) s₆ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅])) fun s₇ u₇ =>
    wp_andi fun s₈ u₈ => ?_
  have m₈ : s₈.mem = saveMem s₀ := by rw [u₈.mem, u₇.mem, u₆.mem, m₅]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]
  have sp₈ : s₈.gpr .esp = esp₀ s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), sp₅]
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, sp₈]) (ain 16 (by omega) (by omega) s₈ rd₈ wr₈)
    fun s₉ u₉ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, u₉.other _ (by decide), sp₈])
    (ain 20 (by omega) (by omega) s₉ (by rw [u₉.rd, rd₈]) (by rw [u₉.wr, wr₈])) fun s₁₀ u₁₀ =>
    wp_test fun s₁₁ f₁₁ z₁₁ => WP.block_nil ?_
  have m₁₁ : s₁₁.mem = saveMem s₀ := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, m₈]
  have ebp₁₁ : s₁₁.gpr .ebp = arg s₀ 4 := by
    rw [f₁₁.gpr, u₁₀.gpr, u₉.mem, m₈, ard 20 (by omega) (by omega)]; rfl
  refine ⟨⟨⟨Nat.zero_le _, by rw [f₁₁.rd, u₁₀.rd, u₉.rd, rd₈], by rw [f₁₁.wr, u₁₀.wr, u₉.wr, wr₈], ?_,
    by rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), sp₈], ?_, ?_,
    by rw [m₁₁]; exact (saveMem_frame hp).mono (by simp), by rw [m₁₁]; exact saveMem_saved hp⟩, ?_,
    fun iv m hm => ?_⟩, ?_⟩
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, m₅, ard 4 (by omega) (by omega)]; rfl
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, m₈, ard 16 (by omega) (by omega)]
    exact (BitVec.add_zero (dp s₀)).symm
  · rw [ebp₁₁, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.mem, m₅,
      ard 8 (by omega) (by omega), and127, Nat.add_zero, cnt_mod]; rfl
  · rw [List.take_zero, List.append_nil, m₁₁]
    exact repr_congr (fun i hi => frame_bytes (saveMem_frame hp) (R := stR s₀) (by simpa using hp.st_scr)
      (by simp) hi) hm.1
  · rw [z₁₁, BitVec.and_self, beq_zero, ← f₁₁.gpr, ebp₁₁]

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Sha512.updateX86.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 24)) :: restore)) s (Post s₀) := by
  have hsc := hp.scr_fit
  have rin : ∀ d, d + 4 ≤ 272 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hI.rd, hI.wr, hp.wr], hp.scr_in hd⟩
  have sv : ∀ p ∈ saved, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := hI.saved
  refine wp_movm (a := addr (esp₀ s₀) 24) (by rw [ea_at, hI.esp])
    ⟨argR s₀, by simp [hI.rd, hp.rd], hp.arg_in (by omega) (by omega)⟩ fun s₀' u₀ => ?_
  have e₀ : s₀'.gpr .eax = scr s₀ := by
    rw [u₀.gpr, hI.arg hp (by omega) (by omega)]
    rfl
  unfold restore
  simp only [saved, List.map_cons, List.map_nil]
  refine wp_movm (a := addr (scr s₀) 224) (by rw [ea_at, e₀])
    (by rw [u₀.rd, u₀.wr]; exact rin 224 (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 228) (by rw [ea_at, u₁.other _ (by decide), e₀])
    (by rw [u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact rin 228 (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := addr (scr s₀) 232) (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), e₀])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact rin 232 (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) 236)
    (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e₀])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact rin 236 (by omega))
    fun s₄ u₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun iv m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₀.mem]
      exact sv (.ebx, 224) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, u₀.mem]
      exact sv (.esi, 228) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, u₀.mem]
      exact sv (.edi, 232) (by simp [saved])
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, u₀.mem]
      exact sv (.ebp, 236) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        u₀.other _ (by decide), hI.esp]
  · rw [hm₄]
    refine hI.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · have := hI.repr iv m ⟨hm, hc⟩
    rw [List.take_of_length_le (by rw [D_length]), ← hm₄] at this
    exact this

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa update s₀ (Post s₀) := by
  have hlen := len_lt s₀
  rw [update_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) (by show s₁.zf = _; exact hz) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hp hI hcl) fun s' ⟨c', hc, hI', hz'⟩ => ?_
    have hc' := hI'.c_le
    have hz : isa.eval .ne s' = some (decide (len s₀ - c' ≠ 0)) := by
      show s'.zf.map (!·) = _
      rw [hz']
      simp
    by_cases hl : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
      rwa [show c' = len s₀ by omega] at hI'
    · exact .inr ⟨by rw [hz, decide_eq_true hl], len s₀ - c', by omega, c', rfl, by omega, hI'⟩

/-! ## Constant time -/

/-- The initial taint: the stack arguments are public, the words holding
`state` and `scratch` are the base addresses of the writable regions, and the
20 bytes below `esp` are outside them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [192, 272], argLen := 28,
    argBases := [(4, 0), (24, 1)], room := 20 }

theorem wf₀ {s : State} (h : Proof.Sha512.updateX86.pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.st_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha512.updateX86.pre s₁) (h₂ : Proof.Sha512.updateX86.pre s₂)
    (hpub : Proof.Sha512.updateX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, stA, scA, st, scr, ha 0 (by omega), ha 5 (by omega)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    have f₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp₁.sp_fit
    have f₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp₂.sp_fit
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4011 then 0x20 else if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 24⟩]
  wr := [⟨0x1000, 192⟩, ⟨0x3000, 272⟩]

theorem sat_pre : Proof.Sha512.updateX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a3 : arg sat 3 = 0x2000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha512.updateX86, a0, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-! ## Constant time, by relating two runs

The prologue is checked by the taint analysis from the initial taint; in the
loop, `fill` up to the test of whether the buffer is full from the registers
that hold our variables, the call of the compression function by its
contract (`compressAt_rel`); the epilogue reads the stack arguments again
(`argTaint`). How many bytes each iteration consumes depends only on `count`
and `len`, so both runs go through the loop the same number of times, with
the same registers. -/

theorem args_out {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hC : Common s₀ c s) : ArgsOut 6 s := by
  have hs := hp.sp_fit
  refine ⟨by rw [hC.esp]; omega, ?_⟩
  rw [hC.wr, hp.wr, hC.esp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

theorem args_kept {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hC : Common s₀ c s) {i : Nat} (hi : i < 6) :
    arg s i = arg s₀ i := by
  rw [arg_eq, arg_eq, hC.esp]
  exact hC.arg hp (by omega) (by omega)

/-- Where `fill` tests whether the buffer is full. -/
def Mid (s₀ : State) (c : Nat) (s : State) : Prop := AtPre (st s₀) (scr s₀) (esp₀ s₀) 24 s ∧
  s.zf = some (decide (rr s₀ c + tt s₀ c = 128)) ∧ WP isa fillEnd s (Inv s₀ (nextC s₀ c))

section CT
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hesp : s₀.gpr .esp = s₀'.gpr .esp)
  (ha : ∀ i < 6, arg s₀ i = arg s₀' i)

include ha

theorem cnt_eq : cnt s₀ = cnt s₀' := by
  simp only [cnt, countX86, ha 1 (by omega), ha 2 (by omega)]

theorem len_eq : len s₀ = len s₀' := by
  simp only [len, ha 4 (by omega)]

theorem nextC_eq (c : Nat) : nextC s₀' c = nextC s₀ c := by
  unfold nextC tt rr
  rw [cnt_eq ha, len_eq ha]

include hesp in
theorem Inv.agree {c : Nat} {s s' : State} (h : Inv s₀ c s) (h' : Inv s₀' c s') :
    ∀ r ∈ [Reg.esp, .ebx, .esi, .ebp, .edi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp]; exact hesp
  · rw [h.ebx, h'.ebx]; exact ha 0 (by omega)
  · rw [h.esi, h'.esi, dp, dp, ha 3 (by omega)]
  · rw [h.ebp, h'.ebp, len_eq ha]
  · rw [h.edi, h'.edi, cnt_eq ha]

include hp hp' hesp

theorem fill_rel {c : Nat} (hcl : c < len s₀) :
    RelCT isa (fun s₁ s₂ => Inv s₀ c s₁ ∧ Inv s₀' c s₂) fill
      fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂ := by
  have hcl' : c < len s₀' := len_eq ha ▸ hcl
  have e0 : st s₀' = st s₀ := (ha 0 (by omega)).symm
  have e5 : scr s₀' = scr s₀ := (ha 5 (by omega)).symm
  have ez : rr s₀' c + tt s₀' c = rr s₀ c + tt s₀ c := by unfold tt rr; rw [cnt_eq ha, len_eq ha]
  have pre : RelCT isa (fun s₁ s₂ => Inv s₀ c s₁ ∧ Inv s₀' c s₂) fillPre fun s₁ s₂ => Mid s₀ c s₁ ∧ Mid s₀' c s₂ :=
    ((RelCT.taint (A := taint) (τr [.esp, .ebx, .esi, .ebp, .edi])
      (fun _ _ h => agree_regs (Inv.agree hesp ha h.1 h.2)) (c := fillPre) (by taint_decide)).wp
      (F₁ := Mid s₀ c) (F₂ := Mid s₀' c) fun _ _ h => ⟨pre_ok hp h.1 hcl, pre_ok hp' h.2 hcl'⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have hat : ∀ s, Mid s₀' c s → AtPre (st s₀) (scr s₀) (esp₀ s₀) 24 s := fun s h => by
    have := h.1; rwa [e0, e5, esp₀, ← hesp] at this
  have cmp : RelCT isa (fun s₁ s₂ => (Mid s₀ c s₁ ∧ Mid s₀' c s₂) ∧ isa.eval .e s₁ = some true)
      (.seq (compressAt 24) (.block [.mov .edi (.imm 0)]))
      fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂ := by
    have hz : ∀ s₁ s₂, (Mid s₀ c s₁ ∧ Mid s₀' c s₂) ∧ isa.eval .e s₁ = some true → isa.eval .e s₂ = some true :=
      fun s₁ s₂ ⟨⟨m₁, m₂⟩, h⟩ => by
        have e₁ : isa.eval .e s₁ = some (decide (rr s₀ c + tt s₀ c = 128)) := m₁.2.1
        have e₂ : isa.eval .e s₂ = some (decide (rr s₀ c + tt s₀ c = 128)) := by rw [← ez]; exact m₂.2.1
        rw [e₂, ← e₁, h]
    refine RelCT.seq (R := fun s₁ s₂ => WP isa (.block [.mov .edi (.imm 0)]) s₁ (Inv s₀ (nextC s₀ c)) ∧
      WP isa (.block [.mov .edi (.imm 0)]) s₂ (Inv s₀' (nextC s₀' c))) ?_ ?_
    · exact (((compressAt_rel hp.st_fit hp.scr_fit hp.sp_lo hp.st_scr hp.stk_st hp.stk_scr
        ⟨_, by taint_decide⟩).mono (fun _ _ h => ⟨h.1.1.1, hat _ h.1.2⟩) fun _ _ h => h).wp
        fun s₁ s₂ h => ⟨WP.seq_iff.mp (WP.ite_true h.1.1.2.2 h.2),
          WP.seq_iff.mp (WP.ite_true h.1.2.2.2 (hz _ _ h))⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    · refine ((RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp))
        (c := .block [.mov .edi (.imm 0)]) (by taint_decide)).wp fun _ _ h => h).mono (fun _ _ h => h)
        fun _ _ h => ⟨h.2.1, ?_⟩
      rw [← nextC_eq ha]; exact h.2.2
  have fend : RelCT isa (fun s₁ s₂ => Mid s₀ c s₁ ∧ Mid s₀' c s₂) fillEnd
      fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂ := by
    refine RelCT.ite (fun s₁ s₂ h => ?_) cmp (RelCT.nil fun s₁ s₂ ⟨⟨m₁, m₂⟩, hf⟩ => ?_)
    · have e₁ : isa.eval .e s₁ = some (decide (rr s₀ c + tt s₀ c = 128)) := h.1.2.1
      have e₂ : isa.eval .e s₂ = some (decide (rr s₀ c + tt s₀ c = 128)) := by rw [← ez]; exact h.2.2.1
      rw [e₁, e₂]
    · have e₁ : isa.eval .e s₁ = some (decide (rr s₀ c + tt s₀ c = 128)) := m₁.2.1
      have e₂ : isa.eval .e s₂ = some false := by
        have : isa.eval .e s₂ = some (decide (rr s₀ c + tt s₀ c = 128)) := by rw [← ez]; exact m₂.2.1
        rw [this, ← e₁, hf]
      refine ⟨WP.block_nil_iff.mp (WP.ite_false m₁.2.2 hf), ?_⟩
      rw [← nextC_eq ha]; exact WP.block_nil_iff.mp (WP.ite_false m₂.2.2 e₂)
  rw [fill_eq]
  exact RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc (pre.seq fend))))

theorem update_rel (h₀ : Proof.Sha512.updateX86.pre s₀) (h₀' : Proof.Sha512.updateX86.pre s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') update fun _ _ => True := by
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block proBlock) fun s₁ s₂ =>
      (Inv s₀ 0 s₁ ∧ s₁.zf = some (decide (len s₀ = 0))) ∧
      (Inv s₀' 0 s₂ ∧ s₂.zf = some (decide (len s₀' = 0))) :=
    ((RelCT.taint (A := taint) τ₀ (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact agree₀ h₀ h₀' ⟨hesp, ha⟩)
      (c := .block proBlock) (by taint_decide)).wp
      (F₁ := fun (s : State) => Inv s₀ 0 s ∧ s.zf = some (decide (len s₀ = 0)))
      (F₂ := fun (s : State) => Inv s₀' 0 s ∧ s.zf = some (decide (len s₀' = 0)))
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have lp := RelCT.loop (M := isa) (body := updateBody) (c := .ne)
    (Q := fun s₁ s₂ => Inv s₀ (len s₀) s₁ ∧ Inv s₀' (len s₀') s₂)
    (fun n s₁ s₂ => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s₁ ∧ Inv s₀' c s₂) (fun n => RelCT.exists_ fun c => by
      by_cases hcn : c < len s₀ ∧ n = len s₀ - c
      · obtain ⟨hcl, rfl⟩ := hcn
        have hn := nextC_gt s₀ hcl
        have tst : RelCT isa (fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂)
            (.block [.alu .test .ebp (.reg .ebp)]) fun s₁ s₂ =>
            (Inv s₀ (nextC s₀ c) s₁ ∧ s₁.zf = some (decide (len s₀ - nextC s₀ c = 0))) ∧
            (Inv s₀' (nextC s₀ c) s₂ ∧ s₂.zf = some (decide (len s₀' - nextC s₀ c = 0))) :=
          ((RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp))
            (c := .block [.alu .test .ebp (.reg .ebp)]) (by taint_decide)).wp
            (F₁ := fun (s : State) => Inv s₀ (nextC s₀ c) s ∧ s.zf = some (decide (len s₀ - nextC s₀ c = 0)))
            (F₂ := fun (s : State) => Inv s₀' (nextC s₀ c) s ∧ s.zf = some (decide (len s₀' - nextC s₀ c = 0)))
            fun _ _ h => ⟨test_ok h.1, test_ok h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
        refine ((fill_rel hp hp' hesp ha hcl).seq tst).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ h => ?_
        · obtain ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ := h
          have hc' := I₁.c_le
          have e₁ : isa.eval .ne s₁ = some (decide (len s₀ - nextC s₀ c ≠ 0)) := by
            show Option.map (!·) _ = _; rw [z₁]; simp
          have e₂ : isa.eval .ne s₂ = some (decide (len s₀ - nextC s₀ c ≠ 0)) := by
            show Option.map (!·) _ = _; rw [z₂, ← len_eq ha]; simp
          refine ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ⟨len s₀ - nextC s₀ c, by omega, nextC s₀ c, rfl,
            ?_, I₁, I₂⟩⟩
          · have : len s₀ - nextC s₀ c = 0 := by
              rw [e₁] at hf; simpa using hf
            have e : nextC s₀ c = len s₀ := by omega
            rw [e] at I₁ I₂; rw [← len_eq ha]; exact ⟨I₁, I₂⟩
          · rw [e₁] at ht; simp at ht; omega
      · exact RelCT.of_false fun _ _ h => hcn ⟨h.2.1, h.1⟩) (len s₀)
  have ite : RelCT isa (fun s₁ s₂ =>
        (Inv s₀ 0 s₁ ∧ s₁.zf = some (decide (len s₀ = 0))) ∧
        (Inv s₀' 0 s₂ ∧ s₂.zf = some (decide (len s₀' = 0))))
      (.ite .e (.block []) (.loop updateBody .ne))
      fun s₁ s₂ => Inv s₀ (len s₀) s₁ ∧ Inv s₀' (len s₀') s₂ := by
    refine RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.nil fun s₁ s₂ ⟨⟨⟨I₁, z₁⟩, ⟨I₂, _⟩⟩, ht⟩ => ?_)
      (lp.mono (fun s₁ s₂ ⟨⟨⟨I₁, z₁⟩, ⟨I₂, _⟩⟩, hf⟩ => ⟨0, by omega, ?_, I₁, I₂⟩) fun _ _ h => h)
    · show s₁.zf = s₂.zf
      rw [h.1.2, h.2.2, len_eq ha]
    · have : len s₀ = 0 := by
        have : s₁.zf = some true := ht
        rw [z₁] at this; simpa using this
      rw [← len_eq ha, this]; exact ⟨I₁, I₂⟩
    · have : s₁.zf = some false := hf
      rw [z₁] at this; simp at this; omega
  have epi : RelCT isa (fun s₁ s₂ => Inv s₀ (len s₀) s₁ ∧ Inv s₀' (len s₀') s₂)
      (.block (.mov .eax (.mem (at_ .esp 24)) :: restore)) fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint [] (4 + 4 * 6)) (fun _ _ h => agree_argTaint
      (fun r hr => nomatch hr) (by rw [h.1.esp, h.2.esp]; exact hesp)
      (args_out hp h.1.toCommon) (args_out hp' h.2.toCommon)
      fun i hi => by rw [args_kept hp h.1.toCommon hi, args_kept hp' h.2.toCommon hi]; exact ha i hi)
      (by taint_decide)
  rw [update_eq]
  exact pro.seq (ite.seq epi)

end CT

theorem update_verified : Verified X86.target update Proof.Sha512.updateX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨sat, sat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
    exact (update_rel (pre_of h₁) (pre_of h₂) hpub.1 hpub.2 h₁ h₂ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sha512.X86.Stream.Update
