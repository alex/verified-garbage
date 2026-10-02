import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming Merkle–Damgård hash functions on AArch64: `update`

The functional correctness of `update`, for any hash function (`Md`) and any
correct compression function (`CalleeOk`). The same structure as the x86-64
proof (`VG.Proof.MdStream.X86_64.Update`); the loop runs while data is left,
so every iteration consumes at least one byte. Constant time is proven for
each hash function's code by the taint analysis, calls included.
-/

namespace VG.Proof.MdStream.AArch64.Update

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev dp : Addr := s₀.gpr .x2
abbrev len : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR : Region := ⟨st s₀, P.N + P.B⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, P.so + 48⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (len s₀)
/-- The buffer. -/
abbrev buf : Addr := st s₀ + BitVec.ofNat 64 P.N

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .x1 = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR P s₀, scR P s₀]
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  d_st : (dR s₀).Disjoint (stR P s₀)
  d_scr : (dR s₀).Disjoint (scR P s₀)

/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 16, 16⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (P : Params) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR P s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR P s₀)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (updK H).pre s₀) : Pre P s₀ ∧ Stack P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem R₀.length (hd : Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) :
    cnt s₀ % P.B = m.length % P.B := by
  rw [cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 c
  x22 : s.gpr .x22 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR P s₀, scR P s₀] s₀.mem s.mem
  saved : Saved P (scr s₀) s₀.gpr s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 ((cnt s₀ + c) % P.B)
  repr : ∀ iv m, R₀ H s₀ iv m → H.Repr iv s.mem (st s₀) (m ++ (D s₀).take c)

/-- `k ≥ 1` whole blocks are ready at `x1` (the buffer, or the data), and
compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  x23 : s.gpr .x23 = 0
  x10 : s.gpr .x10 = BitVec.ofNat 64 k
  k_pos : 0 < k
  mod : (cnt s₀ + c) % P.B = 0
  src : (s.gpr .x1 = buf P s₀ ∧ k = 1) ∨
    ∃ c₀, s.gpr .x1 = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + P.B * k ≤ len s₀
  repr : ∀ iv m, R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (st s₀) =
      H.compressBlocks (H.stateAt s.mem (st s₀)) s.mem (s.gpr .x1) k →
    H.Repr iv mem' (st s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  Inv H s₀ (len s₀) s ∧ s.gpr .x10 = 0

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common P s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  sp := hsp.trans h.sp
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [_] hr)) hm hrd hwr hsp with
    x23 := by rw [hg _ (by simp)]; exact h.x23
    repr := by rw [hm]; exact h.repr }

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR P s₀) := by
  have := saved_offset hd hp; have := hd.so
  exact sub_offset (by omega) (by omega)

/-- The saved registers survive a write to the state. -/
theorem Saved.of_frame (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {m m' : Mem}
    (hs : Saved P (scr s₀) s₀.gpr m) (hf : Frame [stR P s₀] m m') : Saved P (scr s₀) s₀.gpr m' := by
  intro p hp'
  rw [← hs p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hd hp')

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (h : Common P s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

theorem length_mid (hd : Dims P) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ len s₀) : (m ++ (D s₀).take c).length % P.B = (cnt s₀ + c) % P.B := by
  have := hm.length hd
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← this, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing pending blocks -/

theorem Pending.k_lt (hd : Dims P) {s₀ : State} {c k : Nat} {s : State} (h : Pending H s₀ c k s) :
    k < 2 ^ 64 := by
  have := len_lt s₀; have := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega

theorem Pending.compress_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {c k : Nat} {s : State} (h : Pending H s₀ c k s) :
    WP isa (compressN name code) s (Inv H s₀ c) := by
  have := hd.N; have := hd.so; have := hd.B; have := len_lt s₀
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨s.gpr .x1, P.B * k⟩ (stR P s₀) ∨ Region.Sub ⟨s.gpr .x1, P.B * k⟩ (dR s₀) := by
    rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (off := P.N) (by omega) (by omega))
    · exact .inr (h' ▸ sub_offset (by omega) (by omega))
  have hk : (s.gpr .x10).toNat = k := by rw [h.x10, toNat_ofNat_lt (h.k_lt hd)]
  refine compressWith_ok (setsN_x10 s) hk hf h.x19 h.x20 rfl ((hp.st_scr.sub_left eN).sub_right eso)
    ?_ ?_ ?_ ?_ ?_
  · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega) (by omega))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨stR P s₀, by simp, P.N, h', by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hsp hf' hstate
    have cs : ∀ r, r ∈ preserved → r ≠ .x30 → s'.gpr r = s.gpr r := hcs
    refine ⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide) (by decide)]; exact h.x19,
      by rw [cs _ (by decide) (by decide)]; exact h.x20, hsp.trans h.sp,
      by rw [cs _ (by decide) (by decide)]; exact h.x21,
      by rw [cs _ (by decide) (by decide)]; exact h.x22,
      h.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR P s₀, by simp, eso⟩
    · rw [← h.saved p hp']
      have := saved_offset hd hp'
      refine hf'.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ (by omega) (by omega)
    · rw [cs _ (by decide) (by decide), h.x23, h.mod]; rfl

/-! ## Whole blocks straight from the data -/

theorem direct_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hr : (cnt s₀ + c) % P.B = 0) (hl : P.B ≤ len s₀ - c) :
    WP isa (.block (direct P)) s
      (Pending H s₀ (c + P.B * ((len s₀ - c) / P.B)) ((len s₀ - c) / P.B)) := by
  have hlen := len_lt s₀; have hB := hd.pos; have hc := hI.c_le
  have hdm := Nat.div_add_mod (len s₀ - c) P.B
  have hq1 : 0 < (len s₀ - c) / P.B := Nat.div_pos hl hd.pos
  have hsh := hd.shr (a := len s₀ - c) (by omega)
  have hsl := hd.shl (a := (len s₀ - c) / P.B) (by omega)
  generalize (len s₀ - c) / P.B = q at *
  have hq2 : P.B * q ≤ len s₀ - c := by omega
  unfold direct
  have h63 : lg P < 64 := by have := hd.log; omega
  refine wp_mov fun s₁ u₁ => wp_lsr h63 fun s₂ u₂ => wp_lsl h63 fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x1 → r ≠ .x10 → r ≠ .x9 → r ≠ .x21 → r ≠ .x22 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₅.gpr .x1 = dp s₀ + BitVec.ofNat 64 c := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hI.x21]
  have h10 : s₅.gpr .x10 = BitVec.ofNat 64 q := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hI.x22, hsh]
  have h9 : s₃.gpr .x9 = BitVec.ofNat 64 (P.B * q) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.x22, hsh, hsl]
  have h9' : s₄.gpr .x9 = BitVec.ofNat 64 (P.B * q) := by rw [u₄.other _ (by decide), h9]
  refine ⟨⟨by omega, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.x19],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.x20],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₅]; exact hI.frame,
    by rw [m₅]; exact hI.saved⟩, ?_, h10, hq1, ?_, .inr ⟨c, h1, by omega⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, h9, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x21, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.gpr, h9', u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x22, sub_ofNat (by omega), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.x23, hr]; rfl
  · rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]; exact hr
  · intro iv m hm mem' hs
    have hmod := length_mid hd s₀ hm (c := c) (by omega)
    rw [← take_add_data]
    refine H.repr_append_blocks (n := q) hd.pos (hI.repr iv m hm) (by rw [hmod, hr])
      (by rw [List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, m₅, h1]
    apply H.compressBlocks_eq
    intro j hj
    rw [add_ofNat, hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - rr P s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := buf P s₀ + BitVec.ofNat 64 (rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt P s₀ c)
end

theorem rr_lt (hd : Dims P) (s₀ : State) (c : Nat) : rr P s₀ c < P.B := Nat.mod_lt _ hd.pos
theorem tt_le (s₀ : State) (c : Nat) : tt P s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt P s₀ c ≤ P.B - rr P s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr P s₀ c = (cnt s₀ + c) % P.B := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt P s₀ c = min (P.B - rr P s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q P s₀ c = st s₀ + BitVec.ofNat 64 (P.N + rr P s₀ c) :=
  add_ofNat _ _ _

theorem xs_length (s₀ : State) (c : Nat) : (xs P s₀ c).length = tt P s₀ c := by
  have := tt_le (P := P) s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

end

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 (c + j)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (len s₀ - c - tt P s₀ c)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr P s₀ c + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (tt P s₀ c - j)
  x10 : s.gpr .x10 = 0
  mem : s.mem = writeBytes mI (q P s₀ c) ((xs P s₀ c).take j)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem write_frame (hd : Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt P s₀ c) :
    Frame [stR P s₀] mI (writeBytes mI (q P s₀ c) ((xs P s₀ c).take j)) := by
  have := tt_le' (P := P) s₀ c; have := rr_lt hd s₀ c; have := hd.N; have := hd.B
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

theorem copy_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {j : Nat} (hj : j < tt P s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyBody P)) s fun s' =>
      Copy P s₀ c sI.mem (j + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (tt P s₀ c - (j + 1)) := by
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt hd s₀ c
  have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have := hd.N; have := hd.B
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dp s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame hd s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, add_ofNat]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length (P := P) s₀ c
  unfold copyBody
  refine wp_ldrb (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by omega) (by rw [h.x21]; simp) hin
    fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_strb (a := q P s₀ c + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.x19, h.x23, q, buf]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
    wp_subImm (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x21 → r ≠ .x23 → r ≠ .x11 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hx11 : s₆.gpr .x11 = BitVec.ofNat 64 (tt P s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x11, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx11⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide), h.x20]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x10 (by decide) (by decide) (by decide) (by decide) (by decide), h.x10]
  · have hj' : j < (xs P s₀ c).length := by omega
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs P s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 64).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]

theorem copy_loop_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {j₀ : Nat} {s : State} (h : Copy P s₀ c sI.mem j₀ s) (ht : j₀ < tt P s₀ c) :
    WP isa (.loop (.block (copyBody P)) (.nonzero .x .x11)) s (Copy P s₀ c sI.mem (tt P s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt P s₀ c - j ∧ j < tt P s₀ c ∧ Copy P s₀ c sI.mem j s)
    ?_ (tt P s₀ c - j₀) s ⟨j₀, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hd hp hI hj hc) fun s' ⟨hc', h11⟩ => ?_
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (tt P s₀ c - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, h11, bne, ofNat_beq_zero (by have := tt_le' (P := P) s₀ c; have := hd.B; omega)]
    simp
  by_cases hl : tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = tt P s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

theorem Copy.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {j : Nat} {s s' : State} (h : Copy P s₀ c mI j s)
    (hg : ∀ r, r ≠ .x13 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Copy P s₀ c mI j s' :=
  ⟨h.j_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hg _ (by decide), h.x19],
    by rw [hg _ (by decide), h.x20], hsp.trans h.sp, by rw [hg _ (by decide), h.x21],
    by rw [hg _ (by decide), h.x22], by rw [hg _ (by decide), h.x23],
    by rw [hg _ (by decide), h.x11], by rw [hg _ (by decide), h.x10], by rw [hm, h.mem]⟩

theorem xs_chunk (s₀ : State) (c : Nat) {j : Nat} (hj : j + 8 ≤ tt P s₀ c) :
    ((xs P s₀ c).drop j).take 8 = (List.range 8).map fun k => (D s₀).getD (c + j + k) 0 := by
  have ht := tt_le (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range, hxs]; omega
  · intro k h1 h2
    have hk : k < 8 := by simpa using h2
    simp only [xs, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, Nat.add_assoc]
    rw [List.getElem?_eq_getElem (by rw [D_length]; omega), Option.getD_some]

theorem copy_word_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State}
    (hI : Inv H s₀ c sI) {j : Nat} (hj : j + 8 ≤ tt P s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyWordBody P)) s fun s' =>
      Copy P s₀ c sI.mem (j + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((tt P s₀ c - (j + 8)) / 8) := by
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt hd s₀ c
  have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have := hd.N; have := hd.B
  -- The bytes read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 8 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : ∀ k, k < 8 →
      s.mem (dp s₀ + BitVec.ofNat 64 (c + j) + BitVec.ofNat 64 k) = (D s₀).getD (c + j + k) 0 := by
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame hd s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j + k < len s₀; omega)
  -- The bytes written.
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 8 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length (P := P) s₀ c
  unfold copyWordBody
  rw [List.cons_append, List.nil_append]
  refine wp_ldr (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by decide) (by rw [h.x21]; simp) hin
    fun s₁ u₁ => ?_
  refine storeWord_ok (by omega) (a := q P s₀ c + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  · rw [u₁.other _ (by decide), u₁.other _ (by decide), h.x19, h.x23, q, buf]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
    wp_subImm (by decide) fun s₆ u₆ => wp_lsr (by decide) fun s₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x21 → r ≠ .x23 → r ≠ .x11 → r ≠ .x13 →
      s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 => by
    rw [u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃ r h2, u₁.other r h1]
  have hx11₆ : s₆.gpr .x11 = BitVec.ofNat 64 (tt P s₀ c - (j + 8)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      u₁.other _ (by decide), h.x11, sub_ofNat (by omega), Nat.sub_sub]
  have hx11 : s₇.gpr .x11 = BitVec.ofNat 64 (tt P s₀ c - (j + 8)) := by
    rw [u₇.other _ (by decide), hx11₆]
  have hx13 : s₇.gpr .x13 = BitVec.ofNat 64 ((tt P s₀ c - (j + 8)) / 8) := by
    rw [u₇.gpr, hx11₆, ofNat_shr (by omega)]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx13⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x20]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₁.sp, h.sp]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide),
      u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide),
      u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x10]
  · have hl : (List.take j (xs P s₀ c)).length = j := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have hw : (List.range 8).map (fun k => (s.mem.readW (dp s₀ + BitVec.ofNat 64 (c + j)) 64).extractLsb' (8 * k) 8) =
        ((xs P s₀ c).drop j).take 8 := by
      rw [xs_chunk s₀ c hj]
      refine List.map_congr_left fun k hk => ?_
      have hk' : k < 8 := List.mem_range.mp hk
      rw [extractLsb'_readW _ _ hk', hbyte k hk']
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₁.mem, u₁.gpr, writeW_eq_writeBytes, hw, h.mem,
      show q P s₀ c + BitVec.ofNat 64 j = q P s₀ c + BitVec.ofNat 64 (List.take j (xs P s₀ c)).length by
        rw [hl],
      VG.WriteBytes.writeBytes_append _ _ _ _ (by simp only [List.length_take, List.length_drop]; omega),
      ← List.take_add]

theorem copy_words_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State}
    (hI : Inv H s₀ c sI) {s : State} (h : Copy P s₀ c sI.mem 0 s)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 (tt P s₀ c / 8)) :
    WP isa (.ite (.zero .x .x13) (.block []) (.loop (.block (copyWordBody P)) (.nonzero .x .x13))) s
      (Copy P s₀ c sI.mem (8 * (tt P s₀ c / 8))) := by
  have ht' := tt_le' (P := P) s₀ c; have := hd.B
  have hz : eval (.zero .x .x13) s = some (decide (tt P s₀ c / 8 = 0)) := by
    rw [eval_zero, h13, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (tt P s₀ c / 8 = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [hb]; exact h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun n s => ∃ i, n = tt P s₀ c / 8 - i ∧ i < tt P s₀ c / 8 ∧ Copy P s₀ c sI.mem (8 * i) s)
      ?_ (tt P s₀ c / 8) s ⟨0, rfl, by omega, h⟩
    rintro n s ⟨i, rfl, hi, hC⟩
    refine WP.mono (copy_word_step hd hp hI (by omega) hC) fun s' ⟨hC', h13'⟩ => ?_
    have hz' : isa.eval (.nonzero .x .x13) s' = some (decide (tt P s₀ c / 8 - (i + 1) ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x13) s' = _
      rw [eval_nonzero, h13', show (tt P s₀ c - (8 * i + 8)) / 8 = tt P s₀ c / 8 - (i + 1) by omega,
        bne, ofNat_beq_zero (by omega)]
      simp
    rw [show 8 * i + 8 = 8 * (i + 1) by omega] at hC'
    by_cases hl : tt P s₀ c / 8 - (i + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show i + 1 = tt P s₀ c / 8 by omega] at hC'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, i + 1, rfl, by omega, hC'⟩

theorem copy_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem 0 s) : WP isa (copy P) s (Copy P s₀ c sI.mem (tt P s₀ c)) := by
  have ht' := tt_le' (P := P) s₀ c; have := hd.B
  unfold copy
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hC₁ : Copy P s₀ c sI.mem 0 s₁ := h.of_gpr u₁.other u₁.mem u₁.rd u₁.wr u₁.sp
  have h13 : s₁.gpr .x13 = BitVec.ofNat 64 (tt P s₀ c / 8) := by
    rw [u₁.gpr, h.x11, Nat.sub_zero, ofNat_shr (by omega)]
  refine WP.seq (WP.mono (copy_words_ok hd hp hI hC₁ h13) fun s₂ hC₂ => ?_)
  have hz : eval (.zero .x .x11) s₂ = some (decide (tt P s₀ c - 8 * (tt P s₀ c / 8) = 0)) := by
    rw [eval_zero, hC₂.x11, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (tt P s₀ c - 8 * (tt P s₀ c / 8) = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rwa [show 8 * (tt P s₀ c / 8) = tt P s₀ c by omega] at hC₂)
  · simp only [decide_eq_false_iff_not] at hb
    exact copy_loop_ok hd hp hI hC₂ (by omega)

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI) :
    let mem := writeBytes sI.mem (q P s₀ c) (xs P s₀ c)
    Frame [stR P s₀, scR P s₀] s₀.mem mem ∧ Saved P (scr s₀) s₀.gpr mem ∧
      H.stateAt mem (st s₀) = H.stateAt sI.mem (st s₀) ∧
      bytesAt mem (buf P s₀) (rr P s₀ c + tt P s₀ c) = bytesAt sI.mem (buf P s₀) (rr P s₀ c) ++ xs P s₀ c := by
  intro mem
  have hr := rr_lt hd s₀ c; have ht' := tt_le' (P := P) s₀ c; have := hd.N; have := hd.B
  have hxs := xs_length (P := P) s₀ c
  have hf : Frame [stR P s₀] sI.mem mem := by
    have := write_frame hd s₀ c sI.mem (tt P s₀ c) (Nat.le_refl _)
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
    {s : State} (h : Copy P s₀ c sI.mem (tt P s₀ c) s) (hfull : rr P s₀ c + tt P s₀ c = P.B) :
    WP isa (.block [.addImm .x .x1 .x19 P.N, .movz .x .x23 0 0, .movz .x .x10 1 0]) s
      (Pending H s₀ (c + tt P s₀ c) 1) := by
  have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have hc := hI.c_le
  have := hd.N; have := hd.B
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine wp_addImm (by omega) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x1 → r ≠ .x23 → r ≠ .x10 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .x1 = buf P s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x19]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr]; rfl, by rw [u₃.gpr]; rfl, Nat.one_pos,
    by rw [← Nat.add_assoc]; exact Md.add_mod_of_eq hfull, .inl ⟨hx1, rfl⟩,
    ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide), h.x20]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .x21 (by decide) (by decide) (by decide), h.x21]
  · rw [g .x22 (by decide) (by decide) (by decide), h.x22, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← take_add_data]
    have hmod := length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr P s₀ c + tt P s₀ c = P.B from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt P s₀ c) s) (hnf : rr P s₀ c + tt P s₀ c ≠ P.B) : Done H s₀ s := by
  have hr := rr_lt hd s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have hc := hI.c_le
  have htl : tt P s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.x19, h.x20, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.x10⟩
  · rw [h.x21]; congr 2; omega_using [htl, hc]
  · rw [h.x22]; congr 1; omega_using [htl]
  · rw [h.x23, show cnt s₀ + len s₀ = cnt s₀ + c + tt P s₀ c by omega_using [htl, hc],
      Md.add_mod_of_lt (by omega_using [hr, ht', hnf, hrr])]
  · have hmod := length_mid hd s₀ hm hc
    rw [show len s₀ = c + tt P s₀ c by omega_using [htl, hc], ← take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hcl : c < len s₀) (h10 : s.gpr .x10 = 0) :
    WP isa (fill P) s fun s' => (∃ c' k, c < c' ∧ Pending H s₀ c' k s') ∨ Done H s₀ s' := by
  have ht' := tt_le' (P := P) s₀ c; have hr := rr_lt hd s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have ne : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], r ≠ .x9 ∧ r ≠ .x11 := by decide
  have hlen := len_lt s₀
  have hB := hd.B
  have h63 : lg P < 64 := by have := hd.log; omega
  unfold fill
  -- `x11 := B - r; x9 := len >> log₂ B`
  refine WP.seq (wp_movz fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr h63 fun s₃ u₃ => WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .x9 → r ≠ .x11 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  have hI₃ : Inv H s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  have h11₃ : s₃.gpr .x11 = BitVec.ofNat 64 (P.B - rr P s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23, hd.movB, sub_ofNat (by omega)]
  have h9₃ : s₃.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c) / P.B) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22, hd.shr (by omega)]
  -- `x11 := min(x11, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv H s₀ c s₄ ∧ s₄.gpr .x11 = BitVec.ofNat 64 (tt P s₀ c) ∧
    s₄.gpr .x10 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have h10₃ : s₃.gpr .x10 = 0 := by rw [e₃ _ (by decide) (by decide), h10]
    refine WP.ite (decide ((len s₀ - c) / P.B = 0))
      (by show VG.AArch64.eval (.zero .x .x9) s₃ = _
          rw [eval_zero, h9₃, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq, Nat.div_eq_zero_iff_lt hd.pos] at hb
      refine WP.seq (wp_add fun s₅ u₅ => wp_lsr h63 fun s₆ u₆ => WP.block_nil ?_)
      have e₆ : ∀ r, r ≠ .x9 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      have hI₆ : Inv H s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem])
        (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr]) (by rw [u₆.sp, u₅.sp])
      have h9₆ : s₆.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c + rr P s₀ c) / P.B) := by
        rw [u₆.gpr, u₅.gpr, hI₃.x22, hI₃.x23, ← BitVec.ofNat_add, hd.shr (by omega)]
      refine WP.ite (decide ((len s₀ - c + rr P s₀ c) / P.B = 0))
        (by show VG.AArch64.eval (.zero .x .x9) s₆ = _
            rw [eval_zero, h9₆, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))])
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq, Nat.div_eq_zero_iff_lt hd.pos] at hb'
        refine wp_mov fun s₇ u₇ => WP.block_nil ⟨hI₆.of_gpr (fun r hr => u₇.other r (ne r hr).2)
          u₇.mem u₇.rd u₇.wr u₇.sp,
          ?_, by rw [u₇.other _ (by decide), e₆ _ (by decide), h10₃], by rw [u₇.mem, u₆.mem, u₅.mem, hm₃]⟩
        rw [u₇.gpr, hI₆.x22]; congr 1; omega
      · simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb'
        refine WP.block_nil ⟨hI₆, ?_, by rw [e₆ _ (by decide), h10₃], by rw [u₆.mem, u₅.mem, hm₃]⟩
        rw [e₆ _ (by decide), h11₃]; congr 1; omega
    · simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb
      refine WP.block_nil ⟨hI₃, ?_, h10₃, hm₃⟩
      rw [h11₃]; congr 1; omega
  -- `x22 -= x11`
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hC₀ : Copy P s₀ c s.mem 0 s₅ := by
    have e : ∀ r, r ≠ .x22 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
    refine ⟨Nat.zero_le _, by rw [u₅.rd, hI₄.rd], by rw [u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.x19], by rw [e _ (by decide), hI₄.x20], by rw [u₅.sp, hI₄.sp],
      by rw [e _ (by decide), hI₄.x21, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.x23, Nat.add_zero],
      by rw [e _ (by decide), h11₄, Nat.sub_zero], by rw [e _ (by decide), h10₄], ?_⟩
    · rw [u₅.gpr, hI₄.x22, h11₄, sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₅.mem, hm₄, List.take_zero, writeBytes_nil]
  -- Copy the data.
  refine WP.seq (WP.mono (copy_ok hd hp hI hC₀) fun s₆ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (wp_subImm (by omega) fun s₇ u₇ => WP.block_nil ?_)
  have hC₇ : Copy P s₀ c s.mem (tt P s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.x19],
      by rw [u₇.other _ (by decide), hC.x20], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.x21],
      by rw [u₇.other _ (by decide), hC.x22], by rw [u₇.other _ (by decide), hC.x23],
      by rw [u₇.other _ (by decide), hC.x11], by rw [u₇.other _ (by decide), hC.x10],
      by rw [u₇.mem, hC.mem]⟩
  have hz : eval (.zero .x .x9) s₇ = some (decide (rr P s₀ c + tt P s₀ c = P.B)) := by
    rw [eval_zero, u₇.gpr, hC.x23, sub_beq (by omega) (by omega)]
  refine WP.ite (decide (rr P s₀ c + tt P s₀ c = P.B)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hd hp hI hC₇ hb) fun s' h => .inl ⟨c + tt P s₀ c, 1, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hd hp hI hC₇ hb))

/-! ## One iteration -/

theorem body_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s) (hcl : c < len s₀) :
    WP isa (updateBody P name code) s fun s' => ∃ c', c < c' ∧ Inv H s₀ c' s' := by
  have hlen := len_lt s₀; have hr := rr_lt hd s₀ c; have hB := hd.B
  have h63 : lg P < 64 := by have := hd.log; omega
  have ne : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], r ≠ .x10 ∧ r ≠ .x9 := by decide
  unfold updateBody
  refine WP.seq (wp_movz fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ : Inv H s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  have h10₁ : s₁.gpr .x10 = 0 := by rw [u₁.gpr]; rfl
  refine WP.seq (WP.mono (Q := fun s' => (∃ c' k, c < c' ∧ Pending H s₀ c' k s') ∨ Done H s₀ s') ?_
    fun s' h => ?_)
  · refine WP.ite (decide (rr P s₀ c = 0))
      (by show VG.AArch64.eval (.zero .x .x23) s₁ = _; rw [eval_zero, hI₁.x23, ofNat_beq_zero (by have := rr_eq (P := P) s₀ c; omega)])
      (fun hb => ?_) (fun _ => fill_ok hd hp hI₁ hcl h10₁)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_lsr h63 fun s₂ u₂ => WP.block_nil ?_)
    have hI₂ : Inv H s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    have h10₂ : s₂.gpr .x10 = 0 := by rw [u₂.other _ (by decide), h10₁]
    refine WP.ite (decide ((len s₀ - c) / P.B = 0))
      (by show VG.AArch64.eval (.zero .x .x9) s₂ = _
          rw [eval_zero, u₂.gpr, hI₁.x22, hd.shr (by omega),
            ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))])
      (fun _ => fill_ok hd hp hI₂ hcl h10₂) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb'
    have hq := Nat.mul_pos hd.pos (Nat.div_pos (Nat.le_of_not_lt hb') hd.pos)
    exact WP.mono (direct_ok hd hp hI₂ hb (by omega)) fun s' h => .inl ⟨_, _, by omega, h⟩
  · rcases h with ⟨c', k, hc', hP⟩ | ⟨hD, h10⟩
    · refine WP.ite false (by
        show VG.AArch64.eval (.zero .x .x10) s' = _
        rw [eval_zero, hP.x10, ofNat_beq_zero (hP.k_lt hd), decide_eq_false (Nat.pos_iff_ne_zero.mp hP.k_pos)])
        (fun h => by cases h) fun _ => WP.mono (hP.compress_ok hd hf hp) fun s'' h => ⟨c', hc', h⟩
    · refine WP.ite true (by show VG.AArch64.eval (.zero .x .x10) s' = _; rw [eval_zero, h10]; rfl)
        (fun _ => WP.block_nil ⟨len s₀, hcl, hD⟩) fun h => by cases h

/-! ## Prologue and epilogue -/

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (.block (updateStart P)) s₀ (Inv H s₀ 0) := by
  have := hd.N; have := hd.B; have := hd.so
  refine save_ok hd (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hp.wr], contains_offset hd₂ (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_movz fun s₆ u₆ => wp_and fun s₇ u₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = saveMem P s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun iv m hm => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [hm₇]; exact (saveMem_frame hd _ _ _).mono (by simp)
  · rw [hm₇]; exact saveMem_saved hd _ _ _
  · rw [u₇.gpr, u₆.gpr, u₆.other .x1 (by decide), u₅.other .x1 (by decide), u₄.other .x1 (by decide),
      u₃.other .x1 (by decide), u₂.other .x1 (by decide), g₁, hd.and, Nat.add_zero]
  · rw [List.take_zero, List.append_nil, hm₇]
    exact H.repr_congr hd.pos (fun i hi => frame_bytes (saveMem_frame hd s₀.mem (scr s₀) s₀.gpr)
      (R := stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega) hi) hm.1

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md P.B P.N P.L) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ (updK H).post s₀ s'

theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (hI : Inv H s₀ (len s₀) s) :
    WP isa (.block (restore P)) s (Post P H s₀) := by
  have := hd.so
  refine restore_ok hd (scr := scr s₀) hI.x20
    (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, hI.sp], fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (Nat.le_of_eq (D_length _)), ← hmem] at this

/-- `update` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (updateMain P name code), dstOf i ≠ some r) {s₀ : State}
    (hp : Pre P s₀) :
    WP isa (updateMain P name code) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ (updK H).post s₀ s' := by
  have hlen := len_lt s₀
  refine WP.mono (WP.gprs (Q := Post P H s₀) ?_ hu) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨preserved_of hsv hu, hsp, hpost⟩
  unfold updateMain
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv H s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hd hp hI₂)
  refine WP.ite (decide (len s₀ = 0))
    (by show VG.AArch64.eval (.zero .x .x22) s₁ = _
        rw [eval_zero, hI.x22, Nat.sub_zero, ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv H s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hd hf hp hI hcl) fun s' ⟨c', hc, hI'⟩ => ?_
    have hc' := hI'.c_le
    have hz : isa.eval (.nonzero .x .x22) s' = some (decide (len s₀ - c' ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x22) s' = _
      rw [eval_nonzero, hI'.x22, bne, ofNat_beq_zero (by omega)]
      simp
    by_cases hl : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
      rwa [show c' = len s₀ by omega] at hI'
    · exact .inr ⟨by rw [hz]; simp [hl], len s₀ - c', by omega, c', rfl, by omega, hI'⟩

/-- The state `updateMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (updateMain P name code), dstOf i ≠ some r)
    (hn : 16 * (updateMain P name code).aarch64Depth + 16 < 2 ^ 64) {s₀ : State} (hp : Pre P s₀)
    (hs : Stack P s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updK H).post s₀ s' := by
  apply WP.withPreservedV (hc := update_keepsV hf.keepsV)
  have hpi : Pre P (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hd hf hu hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
    hn
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun iv m hm hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes hs.d (len_lt s₀) hi
      have := hpost iv m (H.repr_congr hd.pos (fun i hi => write_frame_bytes (R := stR P s₀) hs.st
        (by have := hd.N; have := hd.B; show P.N + P.B < 2 ^ 64; omega) hi) hm) hc
      rw [e] at this
      exact this

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x3000, P.so + 48⟩]

/-- `update` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code), never writes `untouched`, and
fits its frames in the address space. -/
theorem verified (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hct : ConstantTime isa (updK H).pre (updK H).pub (update P name code))
    (hu : ((instrs (updateMain P name code)).all fun i => untouched.all fun r => dstOf i != some r) = true)
    (hn : 16 * (updateMain P name code).aarch64Depth + 16 < 2 ^ 64) :
    Verified AArch64.target (update P name code) (updK H) := by
  have := hd.N; have := hd.B; have := hd.so
  have hu' : ∀ r ∈ untouched, ∀ i ∈ instrs (updateMain P name code), dstOf i ≠ some r := by
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp hu i hi) r hr
    simpa using this
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hf hu' hn (pre_of hs').1 (pre_of hs').2
    exact ⟨t, s', he, h⟩
  · refine ⟨sat P, rfl, rfl, ?_, ?_, ?_, by simp only [sat]; decide, ?_, ?_, ?_⟩
    all_goals try simp only [sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact Offset.disjoint_of_le (by simp) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

/-- The initial taint agrees on the public arguments. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (updK H).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

end

end VG.Proof.MdStream.AArch64.Update
