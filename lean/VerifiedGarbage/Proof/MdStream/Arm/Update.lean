import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: `update`

Untrusted: everything here is checked by Lean. The functional correctness of
`update`, for any hash function (`Md`) and any correct compression function
(`CalleeOk`). The same structure as the AArch64 proof
(`VG.Proof.MdStream.AArch64.Update`), with `state` in `r0`, `scratch` in
`r3`, `data` in `r5`, the bytes left in `r6`, the buffered bytes in `r4`, and
whether a block is pending in `r7`. Constant time is proven for each hash
function's code by the taint analysis, calls included, from the initial
taint `τ₀`.
-/

namespace VG.Proof.MdStream.Arm.Update

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (count s₀).toNat
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev len : Nat := (stackArg s₀ 1).toNat
abbrev scr : BitVec 32 := stackArg s₀ 2
abbrev stA : Addr := State.addr (st s₀)
abbrev dA : Addr := State.addr (dp s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev stR : Region := ⟨stA s₀, P.N + 64⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, P.so + 48⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dA s₀) (len s₀)
/-- The buffer. -/
abbrev buf : Addr := stA s₀ + BitVec.ofNat 64 P.N

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md 64 P.N 8) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (stA s₀) m ∧ count s₀ = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR P s₀, scR P s₀]
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  d_st : (dR s₀).Disjoint (stR P s₀)
  d_scr : (dR s₀).Disjoint (scR P s₀)
  a_st : (argR s₀).Disjoint (stR P s₀)
  a_scr : (argR s₀).Disjoint (scR P s₀)
  st_fit : (st s₀).toNat + (P.N + 64) ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + (P.so + 48) ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

section
variable {P : Params} {H : Md 64 P.N 8}

theorem pre_of {s₀ : State} (h : (updK H).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (s₀.gpr .r2).toNat % 64 := by
  simp only [cnt, count]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) :
    cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 32 c
  r6 : s.gpr .r6 = BitVec.ofNat 32 (len s₀ - c)
  frame : Frame [stR P s₀, scR P s₀] s₀.mem s.mem
  saved : Saved P s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md 64 P.N 8) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  r4 : s.gpr .r4 = BitVec.ofNat 32 ((cnt s₀ + c) % 64)
  repr : ∀ iv m, R₀ H s₀ iv m → H.Repr iv s.mem (stA s₀) (m ++ (D s₀).take c)

/-- A whole block is ready at `r1`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending {P : Params} (H : Md 64 P.N 8) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  r4 : s.gpr .r4 = 0
  r7 : s.gpr .r7 = 1
  mod : (cnt s₀ + c) % 64 = 0
  src : s.gpr .r1 = st s₀ + BitVec.ofNat 32 P.N ∨
    ∃ c₀, s.gpr .r1 = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + 64 ≤ len s₀
  repr : ∀ iv m, R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (stA s₀) =
      H.compress (H.stateAt s.mem (stA s₀)) (H.blockAt s.mem (State.addr (s.gpr .r1))) →
    H.Repr iv mem' (stA s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (H : Md 64 P.N 8) (s₀ : State) (s : State) : Prop :=
  Inv H s₀ (len s₀) s ∧ s.gpr .r7 = 0

section
variable {P : Params} {H : Md 64 P.N 8}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common P s₀ c s)
    (hg : ∀ r ∈ [Reg.r0, .r3, .r5, .r6, .lr], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp)]; exact h.r0
  r3 := by rw [hg _ (by simp)]; exact h.r3
  sp := hsp.trans h.sp
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.r0, .r3, .r5, .r6, .lr, .r4], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [_] hr)) hm hrd hwr hsp with
    r4 := by rw [hg _ (by simp)]; exact h.r4
    repr := by rw [hm]; exact h.repr }

theorem Inv.of_upd {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ [Reg.r0, .r3, .r5, .r6, .lr, .r4]) : Inv H s₀ c s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Inv.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s) (u : Fupd s s') :
    Inv H s₀ c s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR P s₀) := by
  have := saved_bound hd p hp; have := hd.so
  exact sub_offset (by omega) (by omega)

/-- The saved registers survive a write to the state. -/
theorem Saved.of_frame (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {m m' : Mem}
    (hs : Saved P s₀ m) (hf : Frame [stR P s₀] m m') : Saved P s₀ m' := by
  intro p hp'
  rw [← hs p hp']
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hd hp')

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (h : Common P s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
    (by have := len_lt s₀; show len s₀ ≤ 2 ^ 64; omega) hi

theorem length_mid (s₀ : State) {iv : H.HV} {m : List Byte} (hm : R₀ H s₀ iv m) {c : Nat} (hc : c ≤ len s₀) :
    (m ++ (D s₀).take c).length % 64 = (cnt s₀ + c) % 64 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing a pending block -/

theorem Pending.compress_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (h : Pending H s₀ c s) :
    WP isa (compressAt name code) s (Inv H s₀ c) := by
  have hst := hp.st_fit; have hdf := hp.d_fit; have hsc := hp.scr_fit
  have := hd.N; have := hd.so
  have eN : Region.Sub ⟨stA s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scA s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  -- The block's address.
  obtain ⟨hfit, hsub, hdisj⟩ : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ [stR P s₀, dR s₀], ∃ off, State.addr (s.gpr .r1) = R.base + BitVec.ofNat 64 off ∧
        off + 64 ≤ R.len) ∧
      Region.Disjoint ⟨State.addr (s.gpr .r1), 64⟩ ⟨stA s₀, P.N⟩ ∧
      Region.Disjoint ⟨State.addr (s.gpr .r1), 64⟩ ⟨scA s₀, P.so⟩ := by
    rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · have ha : State.addr (s.gpr .r1) = stA s₀ + BitVec.ofNat 64 P.N := by rw [h', addr_off (by omega)]
      have hs : Region.Sub ⟨State.addr (s.gpr .r1), 64⟩ (stR P s₀) := ha ▸ sub_offset (by omega) (by omega)
      refine ⟨by rw [h', BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        ⟨stR P s₀, by simp, P.N, ha, by simp⟩, ?_, (hp.st_scr.sub_left hs).sub_right eso⟩
      rw [ha]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · have ha : State.addr (s.gpr .r1) = dA s₀ + BitVec.ofNat 64 c₀ := by rw [h', addr_off (by omega)]
      have hs : Region.Sub ⟨State.addr (s.gpr .r1), 64⟩ (dR s₀) := ha ▸ sub_offset (by omega) (by omega)
      refine ⟨by rw [h', BitVec.toNat_add, BitVec.toNat_ofNat]; omega, ⟨dR s₀, by simp, c₀, ha, hc₀⟩,
        (hp.d_st.sub_left hs).sub_right eN, (hp.d_scr.sub_left hs).sub_right eso⟩
  refine compressAt_ok hf h.r0 h.r3 rfl (by omega) hfit (by omega) ((hp.st_scr.sub_left eN).sub_right eso)
    hdisj.1 hdisj.2 ?_ ?_ fun s' hrd hwr hcs h0 h3 hsp hf' hstate => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, off, ha, hl⟩ := hsub
      refine ⟨R, ?_, off, ha, hl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl <;> simp
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · refine ⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, h0, h3,
      hsp.trans h.sp, by rw [hcs _ (by decide) (by decide)]; exact h.r5,
      by rw [hcs _ (by decide) (by decide)]; exact h.r6,
      h.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR P s₀, by simp, eso⟩
    · rw [← h.saved p hp']
      have := saved_bound hd p hp'
      refine hf'.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ this.1 (by omega_using [this.2, hd.so.2])
    · rw [hcs _ (by decide) (by decide), h.r4, h.mod]; rfl

/-! ## A whole block straight from the data -/

theorem direct_ok {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hr : (cnt s₀ + c) % 64 = 0) (hl : 64 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending H s₀ (c + 64)) := by
  have hd := hp.d_fit
  unfold direct
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ =>
    wp_sub (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₄.gpr .r1 = dp s₀ + BitVec.ofNat 32 c := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r5]
  refine ⟨⟨by omega, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.r0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.r3],
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₄]; exact hI.frame,
    by rw [m₄]; exact hI.saved⟩, ?_, by rw [u₄.gpr], by omega, .inr ⟨c, h1, by omega⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.r5,
      BitVec.add_assoc, BitVec.ofNat_add]
    rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r6,
      show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide), hI.r4, hr]; rfl
  · intro iv m hm mem' hs
    have hmod := length_mid s₀ hm (c := c) (by omega)
    rw [← take_add_data]
    refine H.repr_append_block (by decide) (hI.repr iv m hm)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, m₄, h1, addr_off (by omega)]
    refine congrArg (H.compress _) ?_
    rw [show (m ++ List.take c (D s₀)).drop (64 * ((m ++ List.take c (D s₀)).length / 64)) = [] by
      rw [List.drop_eq_nil_iff]; omega, List.nil_append]
    apply H.parse_congr
    intro k hk
    rw [add_ofNat, hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 64
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (64 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := buf P s₀ + BitVec.ofNat 64 (rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 64 := Nat.mod_lt _ (by omega)
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 64 - rr s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 64 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (64 - rr s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q P s₀ c = stA s₀ + BitVec.ofNat 64 (P.N + rr s₀ c) :=
  add_ofNat _ _ _

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

/-- Byte `k` of the buffer, addressed as `[r0 + k, #N]`. -/
theorem buf_addr {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 64) :
    State.addr (st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 P.N) = buf P s₀ + BitVec.ofNat 64 k := by
  have := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_off (by omega), add_ofNat, Nat.add_comm]

end

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 32 (c + j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (rr s₀ c + j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (tt s₀ c - j)
  r7 : s.gpr .r7 = 0
  mem : s.mem = writeBytes mI (q P s₀ c) ((xs s₀ c).take j)

/-- The copy loop's body. -/
def copyBody (P : Params) : List Instr :=
  [.ldrb .r12 .r5 0, .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 P.N, .dp .add .r5 .r5 (.imm 1),
    .dp .add .r4 .r4 (.imm 1), .subs .r8 .r8 (.imm 1)]

section
variable {P : Params} {H : Md 64 P.N 8}

theorem write_frame (hd : Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR P s₀] mI (writeBytes mI (q P s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c; have := hd.N
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

theorem copy_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {j : Nat} (hj : j < tt s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyBody P)) s fun s' =>
      Copy P s₀ c sI.mem (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (tt s₀ c - (j + 1)) == 0) := by
  have hdf := hp.d_fit
  have hc := hI.c_le
  have hr := rr_lt s₀ c
  have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have := hd.N
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dA s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dA s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame hd s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, add_ofNat]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length s₀ c
  unfold copyBody
  refine wp_ldrb (a := dA s₀ + BitVec.ofNat 64 (c + j)) (by omega)
    (by rw [h.r5, BitVec.add_zero, addr_off (by omega)]) hin
    fun s₁ u₁ => ?_
  refine wp_add (op2_reg _ _) fun s₂ u₂ => wp_strb (a := q P s₀ c + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.r0, h.r4, buf_addr hp (by omega), q,
      add_ofNat, buf]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → r ≠ .r1 → r ≠ .r5 → r ≠ .r4 → r ≠ .r8 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have h8 : s₆.gpr .r8 = BitVec.ofNat 32 (tt s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r8, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega),
      Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r0 (by decide) (by decide) (by decide) (by decide) (by decide), h.r0]
  · rw [g .r3 (by decide) (by decide) (by decide) (by decide) (by decide), h.r3]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r5, BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r6 (by decide) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r4, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [g .r7 (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]
  · have hj' : j < (xs s₀ c).length := by omega
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs s₀ c)).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 32).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]
  · rw [z₆, ← u₆.gpr, h8]

theorem copy_loop_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block (copyBody P)) .ne) s (Copy P s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy P s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hd hp hI hj hc) fun s' ⟨hc', hz'⟩ => ?_
  have hz : isa.eval .ne s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s' = _
    rw [eval_ne, hz', ofNat_beq_zero (by have := tt_le' s₀ c; omega)]
    simp
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI) :
    let mem := writeBytes sI.mem (q P s₀ c) (xs s₀ c)
    Frame [stR P s₀, scR P s₀] s₀.mem mem ∧ Saved P s₀ mem ∧
      H.stateAt mem (stA s₀) = H.stateAt sI.mem (stA s₀) ∧
      bytesAt mem (buf P s₀) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (buf P s₀) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c; have := hd.N
  have hxs := xs_length s₀ c
  have hf : Frame [stR P s₀] sI.mem mem := by
    have := write_frame hd s₀ c sI.mem (tt s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), Saved.of_frame hd hp hI.saved hf, ?_, ?_⟩
  · apply H.stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- A full buffer: compress it. -/
theorem fill_pending (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt s₀ c) s) (hfull : rr s₀ c + tt s₀ c = 64) :
    WP isa (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N)), .mov .r4 (.imm 0), .mov .r7 (.imm 1)]) s
      (Pending H s₀ (c + tt s₀ c)) := by
  have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have hst := hp.st_fit
  have := hd.N
  obtain ⟨hfr, hsv, hstt, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine wp_add (op2_imm hd.enc) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r7 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .r1 = st s₀ + BitVec.ofNat 32 P.N := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r0]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr], by rw [u₃.gpr], by omega, .inl hx1, ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r0 (by decide) (by decide) (by decide), h.r0]
  · rw [g .r3 (by decide) (by decide) (by decide), h.r3]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .r5 (by decide) (by decide) (by decide), h.r5]
  · rw [g .r6 (by decide) (by decide) (by decide), h.r6, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine H.repr_append_block (by decide) (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hstt, hx1, addr_off (by omega)]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 64 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt s₀ c) s) (hnf : rr s₀ c + tt s₀ c ≠ 64) : Done H s₀ s := by
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hstt, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.r0, h.r3, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.r7⟩
  · rw [h.r5]; congr 2; omega_using [htl, hc]
  · rw [h.r6]; congr 1; omega_using [htl]
  · rw [h.r4]; congr 1; omega_using [htl, hc, hrr, hr, ht', hnf]
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega_using [htl, hc], ← take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hstt]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill P =
    .seq (.block [.mov .r8 (.imm 64), .dp .sub .r8 .r8 (.reg .r4), .mov .r12 (.shifted .r6 .lsr 6),
      .cmp .r12 (.imm 0)])
    (.seq (.ite .eq
        (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr 6), .cmp .r12 (.imm 0)])
          (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
        (.block []))
    (.seq (.block [.dp .sub .r6 .r6 (.reg .r8)])
    (.seq (.loop (.block (copyBody P)) .ne)
    (.seq (.block [.cmp .r4 (.imm 64)])
      (.ite .eq (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N)), .mov .r4 (.imm 0), .mov .r7 (.imm 1)])
        (.block [])))))) := rfl

theorem fill_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hcl : c < len s₀) (h7 : s.gpr .r7 = 0) :
    WP isa (fill P) s fun s' => (∃ c', c < c' ∧ Pending H s₀ c' s') ∨ Done H s₀ s' := by
  have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hlen := len_lt s₀
  rw [fill_eq]
  -- `r8 := 64 - r; r12 := len >> 6`
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have hI₄ : Inv H s₀ c s₄ :=
    ((((hI.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide))).of_flags f₄
  have h8₄ : s₄.gpr .r8 = BitVec.ofNat 32 (64 - rr s₀ c) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r4,
      show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, sub_ofNat (by omega)]
  have h7₄ : s₄.gpr .r7 = 0 := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h7]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hz₄ : s₄.z = decide ((len s₀ - c) / 64 = 0) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r6, shr6 (by omega), cmp0 (by omega)]
  -- `r8 := min(r8, len)`
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => Inv H s₀ c s₅ ∧ s₅.gpr .r8 = BitVec.ofNat 32 (tt s₀ c) ∧
    s₅.gpr .r7 = 0 ∧ s₅.mem = s.mem) ?_ fun s₅ ⟨hI₅, h8₅, h7₅, hm₅⟩ => ?_)
  · refine WP.ite (decide ((len s₀ - c) / 64 = 0))
      (by show VG.Arm.eval .eq s₄ = _; rw [eval_eq, hz₄]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_add (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ =>
        wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_)
      have hI₈ : Inv H s₀ c s₈ := ((hI₄.of_upd u₆ (by decide)).of_upd u₇ (by decide)).of_flags f₈
      have hz₈ : s₈.z = decide ((len s₀ - c + rr s₀ c) / 64 = 0) := by
        rw [z₈, u₇.gpr, u₆.gpr, hI₄.r6, hI₄.r4, ← BitVec.ofNat_add, shr6 (by omega), cmp0 (by omega)]
      have e₈ : ∀ r, r ≠ .r12 → s₈.gpr r = s₄.gpr r := fun r h => by rw [f₈.gpr, u₇.other r h, u₆.other r h]
      have hm₈ : s₈.mem = s.mem := by rw [f₈.mem, u₇.mem, u₆.mem, hm₄]
      refine WP.ite (decide ((len s₀ - c + rr s₀ c) / 64 = 0))
        (by show VG.Arm.eval .eq s₈ = _; rw [eval_eq, hz₈]) (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine wp_mov (op2_reg _ _) fun s₉ u₉ => WP.block_nil ⟨hI₈.of_upd u₉ (by decide), ?_,
          by rw [u₉.other _ (by decide), e₈ _ (by decide), h7₄], by rw [u₉.mem, hm₈]⟩
        rw [u₉.gpr, hI₈.r6]; congr 1; omega
      · simp only [decide_eq_false_iff_not] at hb'
        refine WP.block_nil ⟨hI₈, ?_, by rw [e₈ _ (by decide), h7₄], hm₈⟩
        rw [e₈ _ (by decide), h8₄]; congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₄, ?_, h7₄, hm₄⟩
      rw [h8₄]; congr 1; omega
  -- `r6 -= r8`
  refine WP.seq (wp_sub (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_)
  have hC₀ : Copy P s₀ c s.mem 0 s₆ := by
    have e : ∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r := fun r h => u₆.other r h
    refine ⟨Nat.zero_le _, by rw [u₆.rd, hI₅.rd], by rw [u₆.wr, hI₅.wr],
      by rw [e _ (by decide), hI₅.r0], by rw [e _ (by decide), hI₅.r3],
      by rw [u₆.sp, hI₅.sp], by rw [e _ (by decide), hI₅.r5, Nat.add_zero], ?_,
      by rw [e _ (by decide), hI₅.r4, Nat.add_zero], by rw [e _ (by decide), h8₅, Nat.sub_zero],
      by rw [e _ (by decide), h7₅], ?_⟩
    · rw [u₆.gpr, hI₅.r6, h8₅, sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₆.mem, hm₅, List.take_zero, writeBytes_nil]
  -- Copy the bytes.
  refine WP.seq (WP.mono (copy_loop_ok hd hp hI hC₀ (by omega)) fun s₇ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_)
  have hC₈ : Copy P s₀ c s.mem (tt s₀ c) s₈ :=
    ⟨hC.j_le, by rw [f₈.rd, hC.rd], by rw [f₈.wr, hC.wr], by rw [f₈.gpr, hC.r0], by rw [f₈.gpr, hC.r3],
      by rw [f₈.sp, hC.sp], by rw [f₈.gpr, hC.r5], by rw [f₈.gpr, hC.r6],
      by rw [f₈.gpr, hC.r4], by rw [f₈.gpr, hC.r8], by rw [f₈.gpr, hC.r7], by rw [f₈.mem, hC.mem]⟩
  have hz : VG.Arm.eval .eq s₈ = some (decide (rr s₀ c + tt s₀ c = 64)) := by
    rw [eval_eq, z₈, hC.r4, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, sub_beq (by omega) (by omega)]
  refine WP.ite (decide (rr s₀ c + tt s₀ c = 64)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hd hp hI hC₈ hb) fun s' h => .inl ⟨c + tt s₀ c, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hd hp hI hC₈ hb))

/-! ## One iteration -/

theorem body_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s) (hcl : c < len s₀) :
    WP isa (updateBody P name code) s fun s' => ∃ c', c < c' ∧ Inv H s₀ c' s' ∧ s'.z = decide (len s₀ - c' = 0) := by
  have hlen := len_lt s₀; have hr := rr_lt s₀ c
  unfold updateBody
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hI₂ : Inv H s₀ c s₂ := (hI.of_upd u₁ (by decide)).of_flags f₂
  have h7₂ : s₂.gpr .r7 = 0 := by rw [f₂.gpr, u₁.gpr]
  have hz₂ : s₂.z = decide (rr s₀ c = 0) := by
    rw [z₂, u₁.other _ (by decide), hI.r4, cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun s' => (∃ c', c < c' ∧ Pending H s₀ c' s') ∨ Done H s₀ s') ?_
    fun s' h => ?_)
  · refine WP.ite (decide (rr s₀ c = 0)) (by show VG.Arm.eval .eq s₂ = _; rw [eval_eq, hz₂])
      (fun hb => ?_) (fun _ => fill_ok hd hp hI₂ hcl h7₂)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ =>
      WP.block_nil ?_)
    have hI₄ : Inv H s₀ c s₄ := (hI₂.of_upd u₃ (by decide)).of_flags f₄
    have h7₄ : s₄.gpr .r7 = 0 := by rw [f₄.gpr, u₃.other _ (by decide), h7₂]
    have hz₄ : s₄.z = decide ((len s₀ - c) / 64 = 0) := by
      rw [z₄, u₃.gpr, hI₂.r6, shr6 (by omega), cmp0 (by omega)]
    refine WP.ite (decide ((len s₀ - c) / 64 = 0)) (by show VG.Arm.eval .eq s₄ = _; rw [eval_eq, hz₄])
      (fun _ => fill_ok hd hp hI₄ hcl h7₄) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not] at hb'
    exact WP.mono (direct_ok hp hI₄ hb (by omega)) fun s' h => .inl ⟨c + 64, by omega, h⟩
  · refine WP.seq (WP.mono (Q := fun (s' : State) => ∃ c', c < c' ∧ Inv H s₀ c' s') ?_ ?_)
    · refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
      rcases h with ⟨c', hc', hP⟩ | ⟨hD, h7⟩
      · have hP₅ : Pending H s₀ c' s₅ :=
          { hP.toCommon.of_gpr (fun r _ => by rw [f₅.gpr]) f₅.mem f₅.rd f₅.wr f₅.sp with
            r4 := by rw [f₅.gpr, hP.r4]
            r7 := by rw [f₅.gpr, hP.r7]
            mod := hP.mod
            src := by rw [f₅.gpr]; exact hP.src
            repr := by rw [f₅.mem, f₅.gpr]; exact hP.repr }
        refine WP.ite false (by show VG.Arm.eval .eq s₅ = _; rw [eval_eq, z₅, hP.r7]; rfl)
          (fun h => by cases h) fun _ => WP.mono (hP₅.compress_ok hd hf hp) fun s'' h => ⟨c', hc', h⟩
      · refine WP.ite true (by show VG.Arm.eval .eq s₅ = _; rw [eval_eq, z₅, h7]; rfl)
          (fun _ => WP.block_nil ⟨len s₀, hcl, hD.of_flags f₅⟩) fun h => by cases h
    · intro s' ⟨c', hc', hI'⟩
      refine wp_cmp (op2_imm (by decide)) fun s'' f'' z'' => WP.block_nil ⟨c', hc', hI'.of_flags f'', ?_⟩
      rw [z'', hI'.r6, cmp0 (by omega)]

end

/-! ## Prologue and epilogue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [.mov .r3 (.reg .r12), .dp .and .r4 .r2 (.imm 63), .ldrSp .r5 0, .ldrSp .r6 4, .cmp .r6 (.imm 0)]

section
variable {P : Params} {H : Md 64 P.N 8}

theorem update_eq (name : String) (code : Prog isa) : update P name code =
    .seq (.block (([.ldrSp .r12 8] : List Instr) ++ save P .r12 ++ prologue))
    (.seq (.ite .eq (.block []) (.loop (updateBody P name code) .ne)) (.block (restore P))) := rfl

/-- The stack arguments, word by word. -/
theorem argAddr_eq {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_off (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 3) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre P s₀) {k : Nat} (hk : k < 3) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact sub_offset (by omega) (by omega)

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (.block (([.ldrSp .r12 8] : List Instr) ++ save P .r12 ++ prologue)) s₀
      fun s => Inv H s₀ 0 s ∧ s.z = decide (len s₀ = 0) := by
  have hsc := hp.scr_fit; have := hd.so; have := hd.N
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok hd (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_offset (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The stack arguments are unchanged by the save.
  have hframe : Frame [scR P s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact saveMem_frame _ _ _ (by omega) _ fun p hp' => by have := saved_bound hd p hp'; omega
  have harg : ∀ k, k < 3 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp hk))) (by decide)
  unfold prologue
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_and (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide)
    (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide))
    fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  have mm : s₇.mem = s₂.mem := by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r12] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₇.gpr, u₆.other r hr.2.2.2.1, u₅.other r hr.2.2.1, u₄.other r hr.2.1, u₃.other r hr.1, g₂,
      u₁.other r hr.2.2.2.2]
  have h6' : s₆.gpr .r6 = stackArg s₀ 1 := by
    rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
  have h6 : s₇.gpr .r6 = stackArg s₀ 1 := by rw [f₇.gpr, h6']
  refine ⟨⟨⟨Nat.zero_le _, by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr], g _ (by decide), ?_,
    by rw [f₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, harg 0 (by decide)]; simp
  · rw [h6]; simp
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, saveMem_saved hd _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂,
      u₁.other _ (by decide), and63, Nat.add_zero, cnt_mod]
  · intro iv m hm
    rw [List.take_zero, List.append_nil, mm]
    exact H.repr_congr (by decide) (fun i hi => frame_bytes hframe (R := stR P s₀)
      (by simpa using hp.st_scr) (by show P.N + 64 ≤ 2 ^ 64; omega) hi) hm.1
  · rw [z₇, h6']
    have := cmp0 (a := len s₀) (len_lt s₀)
    simpa using this

theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (hI : Inv H s₀ (len s₀) s) :
    WP isa (.block (restore P)) s fun s' => abiPreserved s₀ s' ∧ (updK H).post s₀ s' := by
  have := hd.so
  refine restore_ok hd hI.r3 hp.scr_fit
    (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset (by omega) (by omega)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨⟨preserved_of hs, by rw [hsp, hI.sp]⟩, fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (Nat.le_of_eq (D_length _)), ← hmem] at this

theorem correct (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updK H).post s₀ s' := by
  have hlen := len_lt s₀
  rw [update_eq]
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv H s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hd hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv H s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hd hf hp hI hcl) fun s' ⟨c', hc, hI', hz'⟩ => ?_
    have hc' := hI'.c_le
    have hz : isa.eval .ne s' = some (decide (len s₀ - c' ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [eval_ne, hz']
      simp
    by_cases hl : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
      rwa [show c' = len s₀ by omega] at hI'
    · exact .inr ⟨by rw [hz, decide_eq_true hl], len s₀ - c', by omega, c', rfl, by omega, hI'⟩

end

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 12 bytes of stack arguments are public, the
third one pointing at the scratch space. -/
def τ₀ (P : Params) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [P.N + 64, P.so + 48], bases := [(.r0, 0)],
    argLen := 12, argBases := [(8, 1)] }

section
variable {P : Params} {H : Md 64 P.N 8}

theorem wf₀ {s : State} (h : (updK H).pre s) : VG.Arm.Taint.Wf (τ₀ P) s := by
  have hp := pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 12⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨Nat.le_refl 12, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : (updK H).pre s₁) (h₂ : (updK H).pre s₂)
    (hpub : (updK H).pub s₁ s₂) : VG.Arm.Taint.Agree (τ₀ P) s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1, a2⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stA, scA, st, scr, p0, a2]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

end

/-- A state satisfying the precondition (with no data, and the scratch space at 0). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0x4000, 12⟩]
  wr := [⟨0x1000, P.N + 64⟩, ⟨0, P.so + 48⟩]

/-- `update` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code). -/
theorem verified {P : Params} {H : Md 64 P.N 8} (hd : Dims P) {name : String} {code : Prog isa}
    (hf : CalleeOk H code) (hct : ConstantTime isa (updK H).pre (updK H).pub (update P name code)) :
    Verified Arm.target (update P name code) (updK H) := by
  have := hd.N; have := hd.so
  refine ⟨fun s hs => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hf (pre_of hs)
    exact ⟨t, s', he, h⟩
  · have e : ∀ k, stackArg (sat P) k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat P, ?_⟩
    simp only [updK, e]
    refine ⟨by simp [sat, stackArgAddr, State.addr], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [sat, stackArgAddr, State.addr]
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)).symm
    iterate 2 exact Offset.disjoint_of_le (by simp) (by simp <;> omega)
    iterate 2 exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    all_goals simp <;> omega

end VG.Proof.MdStream.Arm.Update
