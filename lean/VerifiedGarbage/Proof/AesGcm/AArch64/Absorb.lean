import VerifiedGarbage.Proof.AesGcm.AArch64.Loops

/-!
# AES-GCM on AArch64: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`x24` bytes at `x23` into GHASH, with the accumulator at `St + yo` and the
`x25` buffered bytes at `St + 32`: it fills the buffer (`absSeg1_ok`) and
absorbs it if full (`absCall1_ok`, a call of `vg_ghash` on one block or
none), absorbs whole blocks (`absSeg2_ok`, `absCall2_ok`) and buffers the
rest (`absTail_ok`), by the steps of `Proof/Gcm/Stream.lean`; `absorb_ok`
puts them together. The pieces are proven separately, between the calls, so
that the proof of constant time can use them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
state and `W`. -/
structure DataOk (St W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  st : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace DataOk

variable {St W : Addr} {s : State} {D : Addr} {n : Nat} (h : DataOk St W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataOk St W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : DataOk St W s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  st := h.st.sub_left (Offset.sub_base D (by omega))
  w := h.w.sub_left (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : DataOk St W s D k where
  rd := covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)

end DataOk

/-- The regions `absorb` writes. -/
abbrev absFrame (St W : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨St + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- The bytes `absorb` takes into the buffer first. -/
abbrev headLen (o n : Nat) : Nat := min (16 - o) n

/-- Whether the buffer is then full: the blocks of the first call. -/
abbrev headBlocks (o n : Nat) : Nat := if o + headLen o n = 16 then 1 else 0

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`x23`, `x24`, `x25` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (x : List Byte) (D : Addr)
    (n o : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = D
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  ho : x.length % 16 = o
  data : DataOk St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Before the first call: the buffer filled, from `m₀`. -/
structure Abs1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (D : Addr) (n o : Nat)
    (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 (headLen o n)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - headLen o n)
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  data : DataOk St W s D n
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32)
    (W + BitVec.ofNat 64 512) (headBlocks o n)
  buf : bytesAt s.mem (St + BitVec.ofNat 64 32) (o + headLen o n) =
    bytesAt m₀ (St + BitVec.ofNat 64 32) o ++ bytesAt m₀ D (headLen o n)
  frame : Frame [⟨St + BitVec.ofNat 64 (32 + o), headLen o n⟩] m₀ s.mem

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (x : List Byte)
    (D : Addr) (n o : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  data : DataOk St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame St W yo) m₀ s.mem

/-- Before the second call: the whole blocks from byte `j` on. -/
structure Abs3 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (x : List Byte)
    (D : Addr) (n o : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16))
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16)))
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  data : DataOk St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame St W yo) m₀ s.mem
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) (D + BitVec.ofNat 64 j)
    (W + BitVec.ofNat 64 512) ((n - j) / 16)

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (yo : Nat) (H : Block) (x₀ x : List Byte)
    (o : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 o
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (absFrame St W yo) m₀ s.mem

section
variable {Ctx St W : Addr} (L : Lay Ctx St W) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk St W s D n) :
    ∀ r ∈ absFrame St W yo, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))

/-- The hash subkey is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ absFrame St W yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

/-- The call of `vg_ghash` on the accumulator, from a state whose registers
are its arguments. -/
theorem ghCall_of {SP : Addr} {s : State} (he : Env Ctx St W SP s) {P : Addr} {nb : Nat}
    (h0 : s.gpr .x0 = Ctx + BitVec.ofNat 64 240) (h1 : s.gpr .x1 = St + BitVec.ofNat 64 yo)
    (h2 : s.gpr .x2 = P) (h3 : s.gpr .x3 = BitVec.ofNat 64 nb) (h4 : s.gpr .x4 = W + BitVec.ofNat 64 512)
    (hn : 16 * nb < 2 ^ 64)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * nb⟩)
    (hpw : (⟨P, 16 * nb⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 256⟩)
    (hpr : Covers [⟨P, 16 * nb⟩] (s.rd ++ s.wr)) :
    GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) nb :=
  ⟨h0, h1, h2, h3, h4, hn, L.ctx_st (by decide) (by omega), L.ctx_w (by decide) (by decide),
    hpy, L.st_w (by omega) (.inr ⟨by decide, by decide⟩), hpw,
    covers_cons (he.perm.ctxC (by decide)) (covers_cons hpr (covers_cons
      (covers_left (he.perm.stC (by omega))) (covers_left (he.perm.wC (by decide))))),
    covers_cons (he.perm.stC (by omega)) (he.perm.wC (by decide))⟩

omit L hyo in
/-- What a call of `vg_ghash` from an environment leaves. -/
theorem GhPost.env {SP : Addr} {s s' : State} {H' Y D S : Addr} {nb : Nat}
    (h : GhPost s H' Y D S nb s') (he : Env Ctx St W SP s) : Env Ctx St W SP s' :=
  he.of_saved h.saved h.sp h.rd h.wr

end

theorem ghArgs_eq (yo : Nat) (rest : List Instr) :
    ghArgs yo ++ rest = ptr .x0 .x21 240 :: ptr .x1 .x20 yo :: ptr .x4 .x19 scrO :: rest := rfl

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer. -/
theorem absSeg1_ok {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat} {s : State}
    (h : AbsIn Ctx St W SP k H x D n o s) :
    WP isa (absSeg1 yo) s (Abs1 Ctx St W SP k yo H D n o s.mem) := by
  have ho : o < 16 := by rw [← h.ho]; exact Nat.mod_lt _ (by decide)
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (minK_ok s h.x25 h.x24 ho hn') fun s₁ ⟨x10₁, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  have hk1 : headLen o n ≤ n := Nat.min_le_right _ _
  have hk16 : o + headLen o n ≤ 16 := by have := Nat.min_le_left (16 - o) n; simp only [headLen]; omega
  have r₁ : Regs minRegs s s₁ := ⟨g₁, m₁, sp₁, rd₁, wr₁⟩
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, r₂⟩ : ∃ s₂, runBlock isa
      [.add .x .x11 .x20 .x25, ptr .x11 .x11 32, mov .x12 .x23, mov .x13 .x10] s₁ = some s₂ ∧
      s₂.gpr .x11 = St + BitVec.ofNat 64 (32 + o) ∧ s₂.gpr .x12 = D ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (headLen o n) ∧ Regs [.x11, .x12, .x13] s₁ s₂ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, g₁ .x20 (by decide), g₁ .x25 (by decide), he.x20, h.x25, add_ofNat_assoc,
        Nat.add_comm]
    · simp [gpr_write, g₁ .x23 (by decide), h.x23]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hlp : LoopPre s₂ D (St + BitVec.ofNat 64 (32 + o)) (headLen o n) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [r₂.rd, r₂.wr, r₁.rd, r₁.wr]; exact (h.data.take hk1).rd
    · rw [r₂.wr, r₁.wr]; exact he.perm.stC (by omega)
    · exact (h.data.take hk1).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (copy_ok s₂ x12₂ x11₂ x13₂ hlp) fun s₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  rw [r₂.mem, r₁.mem] at m₃
  have hdk := length_bytesAt s.mem D (headLen o n)
  -- The block after the copy.
  have gg₃ : ∀ r, r ∉ minRegs ++ [.x11, .x12, .x13] ++ loopRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (List.mem_append_right _ h)), (r₁.comp r₂).others r
      (fun h => hr (List.mem_append_left _ h))]
  obtain ⟨s₄, run₄, x23₄, x24₄, x9₄, r₄⟩ : ∃ s₄, runBlock isa
      [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .add .x .x9 .x25 .x10, .subImm .x .x9 .x9 16] s₃ =
        some s₄ ∧
      s₄.gpr .x23 = D + BitVec.ofNat 64 (headLen o n) ∧ s₄.gpr .x24 = BitVec.ofNat 64 (n - headLen o n) ∧
      s₄.gpr .x9 = BitVec.ofNat 64 (o + headLen o n) - BitVec.ofNat 64 16 ∧ Regs [.x23, .x24, .x9] s₃ s₄ := by
    have e10 : s₃.gpr .x10 = BitVec.ofNat 64 (headLen o n) := by
      rw [g₃ _ (by decide), r₂.others _ (by decide), x10₁]
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, e10, gg₃ .x23 (by decide), h.x23]
    · simp [gpr_write, e10, gg₃ .x24 (by decide), h.x24, ofNat_sub hk1 hn']
    · simp [gpr_write, e10, gg₃ .x25 (by decide), h.x25, ofNat_add_ofNat]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have ev : isa.eval (.zero .x .x9) s₄ = some (decide (o + headLen o n = 16)) := by
    show some (s₄.read .x .x9 == 0) = _
    rw [State.read, x9₄, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .x3 = BitVec.ofNat 64 (headBlocks o n) ∧ Regs [.x3] s₄ s₅)
    (WP.ite (decide (o + headLen o n = 16)) ev (fun ht => ?_) (fun hf => ?_)) fun s₅ ⟨x3₅, r₅⟩ => ?_)
  · have h16 : o + headLen o n = 16 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, headBlocks, h16], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h16 : o + headLen o n ≠ 16 := by simpa using hf
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, headBlocks, h16], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have gg₅ : ∀ r, r ∉ minRegs ++ [.x11, .x12, .x13] ++ loopRegs ++ [.x23, .x24, .x9, .x3] →
      s₅.gpr r = s.gpr r := fun r hr => by
    rw [r₅.others r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; simp [h])),
      r₄.others r (fun h => hr (List.mem_append_right _ (List.mem_append_left _ h))),
      gg₃ r (fun h => hr (List.mem_append_left _ h))]
  obtain ⟨s₆, run₆, x0₆, x1₆, x4₆, x2₆, r₆⟩ : ∃ s₆, runBlock isa (ghArgs yo ++ [ptr .x2 .x20 32]) s₅ = some s₆ ∧
      s₆.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₆.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₆.gpr .x4 = W + BitVec.ofNat 64 512 ∧ s₆.gpr .x2 = St + BitVec.ofNat 64 32 ∧
      Regs [.x0, .x1, .x4, .x2] s₅ s₆ := by
    have hyo' : yo < 4096 := by omega
    refine ⟨_, by rw [ghArgs_eq]; arun [hyo'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, gg₅ .x21 (by decide), he.x21]
    · simp [gpr_write, gg₅ .x20 (by decide), he.x20]
    · simp [gpr_write, gg₅ .x19 (by decide), he.x19]
    · simp [gpr_write, gg₅ .x20 (by decide), he.x20]
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have ggA : ∀ r, r ∉ minRegs ++ [.x11, .x12, .x13] ++ loopRegs ++ [.x23, .x24, .x9, .x3] ++
      [.x0, .x1, .x4, .x2] → s₆.gpr r = s.gpr r := fun r hr => by
    rw [r₆.others r (fun h => hr (List.mem_append_right _ h)), gg₅ r (fun h => hr (List.mem_append_left _ h))]
  have hm₆ : s₆.mem = writeBytes s.mem (St + BitVec.ofNat 64 (32 + o)) (bytesAt s.mem D (headLen o n)) := by
    rw [r₆.mem, r₅.mem, r₄.mem, m₃]
  have hsp₆ : s₆.sp = s.sp := by rw [r₆.sp, r₅.sp, r₄.sp, sp₃, r₂.sp, r₁.sp]
  have hrd₆ : s₆.rd = s.rd := by rw [r₆.rd, r₅.rd, r₄.rd, rd₃, r₂.rd, r₁.rd]
  have hwr₆ : s₆.wr = s.wr := by rw [r₆.wr, r₅.wr, r₄.wr, wr₃, r₂.wr, r₁.wr]
  have he₆ : Env Ctx St W SP s₆ := he.keep (fun r hr => ggA r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp₆ hrd₆ hwr₆
  have hnf : headBlocks o n ≤ 1 := by simp only [headBlocks]; split <;> omega
  refine ⟨he₆, h.kept.of_eq fun r hr => ggA r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [r₆.others _ (by decide), r₅.others _ (by decide), x23₄],
    by rw [r₆.others _ (by decide), r₅.others _ (by decide), x24₄],
    by rw [ggA _ (by decide), h.x25], h.data.of_eq hrd₆ hwr₆, ?_, ?_, ?_⟩
  · refine ghCall_of L hyo he₆ x0₆ x1₆ x2₆ (by rw [r₆.others _ (by decide), x3₅]) x4₆ (by omega)
      (L.st_st (.inl (by omega)) (by omega) (by omega))
      (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (covers_left (he₆.perm.stC (by omega)))
  · rw [hm₆, show St + BitVec.ofNat 64 (32 + o) = St + BitVec.ofNat 64 32 + BitVec.ofNat 64 o from
      (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (St + BitVec.ofNat 64 32) o (bytesAt s.mem D (headLen o n))
      (by rw [hdk]; omega)
    rwa [hdk] at this
  · rw [hm₆]; exact writeBytes_frame' _ hdk

omit L hyo in
theorem blocksAt_zero (m : Mem) (p : Addr) : blocksAt m p 0 = [] := rfl

omit L hyo in
theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

omit L hyo in
theorem frame_absFrame_buf {m m' : Mem} {o k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (absFrame St W yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem frame_absFrame_gh {m m' : Mem}
    (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩] m m') :
    Frame (absFrame St W yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The ghash frame keeps the hash subkey. -/
theorem hH_gh {s s' : State} {D : Addr} {nb : Nat}
    (g : GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) D (W + BitVec.ofNat 64 512) nb s') :
    blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame g.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.ctx_st (by decide) (by omega)
    · exact L.ctx_w (by decide) (by decide)

/-- The first call: the buffer absorbed if it is full. -/
theorem absCall1_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {s : State} (h : Abs1 Ctx St W SP k yo H D n o m₀ s) (hx : x.length % 16 = o)
    (hH₀ : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (ghCall v.callees) s (AbsMid Ctx St W SP k yo H x D n o m₀ (headLen o n)) := by
  have ho : o < 16 := by rw [← hx]; exact Nat.mod_lt _ (by decide)
  have hk1 : headLen o n ≤ n := Nat.min_le_right _ _
  have hk16 : o + headLen o n ≤ 16 := by have := Nat.min_le_left (16 - o) n; simp only [headLen]; omega
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hlen := length_bytesAt m₀ D (headLen o n)
  have hHs : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), hH₀]
  have hY : blockAt s.mem (St + BitVec.ofNat 64 yo) = blockAt m₀ (St + BitVec.ofNat 64 yo) :=
    blockAt_frame h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)
  have gout := g.out
  rw [hHs, hY] at gout
  refine ⟨g.env h.env, h.kept.of_saved g.saved, hk1, by rw [g.saved _ (by decide) (by decide), h.x23],
    by rw [g.saved _ (by decide) (by decide), h.x24], by rw [g.saved _ (by decide) (by decide), h.x25],
    h.data.of_eq g.rd g.wr, by rw [hH_gh L hyo g, hHs], fun ha => ?_, ?_,
    (frame_absFrame_buf h.frame hk16).trans (frame_absFrame_gh g.frame)⟩
  · by_cases h16 : o + headLen o n = 16
    · rw [show headBlocks o n = 1 by simp [headBlocks, h16], blocksAt_one] at gout
      refine Proof.Gcm.absorb_complete ha (by rw [hlen, hx]; exact h16)
        (B := bytesAt s.mem (St + BitVec.ofNat 64 32) 16) ?_ gout
      rw [← h16, h.buf, ← hx, ha.2]
    · rw [show headBlocks o n = 0 by simp [headBlocks, h16], blocksAt_zero] at gout
      refine Proof.Gcm.absorb_fill ha (by rw [hlen, hx]; omega) gout ?_
      rw [hlen, hx, bytesAt_frame g.frame (fun r hr => ?_) (by omega), h.buf]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.st_st (.inr (by omega)) (by omega) (by omega)
      · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · by_cases h16 : o + headLen o n = 16
    · exact .inr (by omega)
    · exact .inl (by simp only [headLen] at h16 ⊢; omega)

/-- Before the second call: the arguments for the whole blocks. -/
theorem absSeg2_ok {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : AbsMid Ctx St W SP k yo H x D n o m₀ j s) :
    WP isa (.block (absSeg2 yo)) s (Abs3 Ctx St W SP k yo H x D n o m₀ j) := by
  have hn' := h.data.lt
  have he := h.env
  have hyo' : yo < 4096 := by omega
  have hdj := (h.data.drop h.le).take (k := 16 * ((n - j) / 16)) (by omega)
  obtain ⟨s₁, run₁, x3₁, x2₁, x0₁, x1₁, x4₁, x23₁, x24₁, r₁⟩ : ∃ s₁, runBlock isa (absSeg2 yo) s = some s₁ ∧
      s₁.gpr .x3 = BitVec.ofNat 64 ((n - j) / 16) ∧ s₁.gpr .x2 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ s₁.gpr .x1 = St + BitVec.ofNat 64 yo ∧
      s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      s₁.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s₁.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      Regs [.x3, .x2, .x0, .x1, .x4, .x9, .x23, .x24] s s₁ := by
    refine ⟨_, by simp only [absSeg2, ghArgs]; arun [hyo'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, h.x24, lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega)]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, h.x23, h.x24, lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), lsl4_ofNat,
        add_ofNat_assoc]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h.x24, BitVec.setWidth_eq,
        lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega), lsl4_ofNat]
      rw [ofNat_sub (by omega) (by omega)]
      congr 1
      omega
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ := he.of_regs r₁
  refine ⟨he₁, h.kept.of_others r₁.others, h.le, x23₁, x24₁, by rw [r₁.others _ (by decide)]; exact h.x25,
    h.data.of_eq r₁.rd r₁.wr, by rw [r₁.mem]; exact h.hH, fun ha => by rw [r₁.mem]; exact h.abs ha, h.whole,
    by rw [r₁.mem]; exact h.frame, ?_⟩
  exact ghCall_of L hyo he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by have := hdj.lt; omega)
    (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide)))
    (by rw [r₁.rd, r₁.wr]; exact hdj.rd)

/-- The second call: the whole blocks absorbed. -/
theorem absCall2_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : Abs3 Ctx St W SP k yo H x D n o m₀ j s) :
    WP isa (ghCall v.callees) s fun s' =>
      AbsMid Ctx St W SP k yo H x D n o m₀ (j + 16 * ((n - j) / 16)) s' ∧ n - (j + 16 * ((n - j) / 16)) < 16 := by
  have hm := h
  have hn' := hm.data.lt
  have hle := hm.le
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have hdata : bytesAt s.mem D n = bytesAt m₀ D n :=
    bytesAt_frame hm.frame (data_absFrame hyo hm.data) (by omega)
  refine ⟨⟨g.env hm.env, hm.kept.of_saved g.saved, by omega, ?_, ?_, ?_, hm.data.of_eq g.rd g.wr,
    by rw [hH_gh L hyo g, hm.hH], fun ha => ?_, ?_, hm.frame.trans (frame_absFrame_gh g.frame)⟩, by omega⟩
  · rw [g.saved _ (by decide) (by decide), hm.x23]
  · rw [g.saved _ (by decide) (by decide), hm.x24]
  · rw [g.saved _ (by decide) (by decide), hm.x25]
  · have hb : ∀ (m m' : Mem) (_ : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩] m m')
        (q : Nat), q ≤ 16 → bytesAt m' (St + BitVec.ofNat 64 32) q = bytesAt m (St + BitVec.ofNat 64 32) q :=
      fun m m' hf q hq => bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.st_st (.inr (by omega)) (by omega) (by omega)
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (by omega)
    have gout := g.out
    rw [hm.hH] at gout
    by_cases h0 : (n - j) / 16 = 0
    · rw [h0, blocksAt_zero, Proof.Gcm.ghashFrom_nil] at gout
      rw [h0, Nat.mul_zero, Nat.add_zero]
      exact (hm.abs ha).congr gout (hb _ _ g.frame _ (Nat.le_of_lt (Nat.mod_lt _ (by decide))))
    · have hw : (x.length + j) % 16 = 0 := hm.whole.resolve_left (by omega)
      have ex : x ++ bytesAt m₀ D (j + 16 * ((n - j) / 16)) =
          (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * ((n - j) / 16)) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (hm.abs ha) (by simp [length_bytesAt]; omega)
        (by simp [length_bytesAt]) ?_
      rw [gout, Proof.Gcm.blocksAt_eq]
      refine congrArg (fun l => ghashFrom H (blockAt s.mem (St + BitVec.ofNat 64 yo)) (Spec.Gcm.blocks l)) ?_
      have e₁ := congrArg (fun l => (l.drop j).take (16 * ((n - j) / 16))) hdata
      simp only [bytesAt_drop _ _ hle, bytesAt_take _ _ (show 16 * ((n - j) / 16) ≤ n - j by omega)] at e₁
      exact e₁
  · by_cases h0 : (n - j) / 16 = 0
    · rw [h0, Nat.mul_zero, Nat.add_zero]; exact hm.whole
    · have hw : (x.length + j) % 16 = 0 := hm.whole.resolve_left (by omega)
      exact .inr (by omega)

/-- The last bytes, buffered. -/
theorem absTail_ok {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : AbsMid Ctx St W SP k yo H x D n o m₀ j s) (hj : n - j < 16) :
    WP isa absTail s (AbsOut Ctx St W SP k yo H x (x ++ bytesAt m₀ D n) o m₀) := by
  have hn' := h.data.lt
  have he := h.env
  have hdj := h.data.drop h.le
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, r₁⟩ : ∃ s₁, runBlock isa [ptr .x11 .x20 32, mov .x12 .x23, mov .x13 .x24] s =
      some s₁ ∧ s₁.gpr .x11 = St + BitVec.ofNat 64 32 ∧ s₁.gpr .x12 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ Regs [.x11, .x12, .x13] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, he.x20]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 32) (n - j) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [r₁.rd, r₁.wr]; exact hdj.rd
    · rw [r₁.wr]; exact he.perm.stC (by omega)
    · exact hdj.st.sub_right (Lay.stSub (by omega))
  refine WP.mono (copy_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [r₁.mem] at m₂
  have hlen := length_bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j)
  have fw : Frame [⟨St + BitVec.ofNat 64 32, n - j⟩] s.mem s₂.mem := by rw [m₂]; exact writeBytes_frame' _ hlen
  have gg : ∀ r, r ∉ [Reg.x11, .x12, .x13] ++ loopRegs → s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r (fun h' => hr (List.mem_append_right _ h')), r₁.others r (fun h' => hr (List.mem_append_left _ h'))]
  refine ⟨he.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) (by rw [sp₂, r₁.sp]) (by rw [rd₂, r₁.rd]) (by rw [wr₂, r₁.wr]),
    h.kept.of_eq fun r hr => gg r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x25], fun ha => ?_, ?_⟩
  · have ed : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
      have e₁ := congrArg (fun l => l.drop j)
        (bytesAt_frame h.frame (data_absFrame hyo h.data) (by omega) : bytesAt s.mem D n = bytesAt m₀ D n)
      simpa only [bytesAt_drop _ _ h.le] using e₁
    have ex : x ++ bytesAt m₀ D n = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
      rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' h.le]
    rw [ex, ← ed]
    by_cases h0 : n - j = 0
    · rw [m₂, h0]
      simp only [bytesAt, List.range_zero, List.map_nil, writeBytes_nil, List.append_nil]
      exact h.abs ha
    · have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · exact blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)
      · rw [m₂]; exact bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
  · exact h.frame.trans ((fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

/-- `absorb yo`. -/
theorem absorb_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {x : List Byte} {D : Addr} {n o : Nat}
    {s : State} (h : AbsIn Ctx St W SP k H x D n o s) :
    WP isa (absorb v.callees yo) s (AbsOut Ctx St W SP k yo H x (x ++ bytesAt s.mem D n) o s.mem) :=
  WP.seq (WP.mono (absSeg1_ok L hyo h) fun _ h₁ =>
  WP.seq (WP.mono (absCall1_ok L hyo v h₁ h.ho h.hH) fun _ h₂ =>
  WP.seq (WP.mono (absSeg2_ok L hyo h₂) fun _ h₃ =>
  WP.seq (WP.mono (absCall2_ok L hyo v h₃) fun _ ⟨h₄, hlt⟩ => absTail_ok L hyo h₄ hlt))))

end

end VG.Proof.AesGcm.AArch64
