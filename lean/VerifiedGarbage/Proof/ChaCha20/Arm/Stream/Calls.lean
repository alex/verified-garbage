import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Bytes
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# Streaming ChaCha20 on ARMv7: the entry state and the calls

Untrusted: everything here is checked by Lean. The contract of `apply`, what
its precondition gives, and the calls of `vg_chacha20_block` and
`vg_chacha20_xor`, from their proofs of correctness (with `WP.call` and
`WP.callCalls`), as ChaCha20-Poly1305 makes them. A call (`bl`) stores
nothing in memory, so the callee changes memory only within the regions it
may write.
-/

namespace VG.Proof.ChaCha20

open VG.Arm
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- ARMv7 contract for `vg_chacha20_apply(state = r0, data = r1, len = r2) -> r0`.
The return address is in `lr`, which the code saves in the state, so no
stack is used. -/
def applyArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 768⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    (s.gpr .r0).toNat + 768 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem (State.addr (s.gpr .r0)) = keyAt s.mem (State.addr (s.gpr .r0)) ∧
      if (s.gpr .r2).toNat ≤ leftAt s.mem (State.addr (s.gpr .r0)) then
        s'.gpr .r0 = 1 ∧
          bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
              ((restAt s.mem (State.addr (s.gpr .r0))).take (s.gpr .r2).toNat) ∧
          restAt s'.mem (State.addr (s.gpr .r0)) = (restAt s.mem (State.addr (s.gpr .r0))).drop (s.gpr .r2).toNat
      else
        s'.gpr .r0 = 0 ∧
          bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
            bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat ∧
          restAt s'.mem (State.addr (s.gpr .r0)) = restAt s.mem (State.addr (s.gpr .r0))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.sp = s₂.sp ∧ [leftAt s₁.mem (State.addr (s₁.gpr .r0))] = [leftAt s₂.mem (State.addr (s₂.gpr .r0))]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (addr_off)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt keystream serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev ST : BitVec 32 := s₀.gpr .r0
abbrev DP : BitVec 32 := s₀.gpr .r1
abbrev L : Nat := (s₀.gpr .r2).toNat
abbrev st : Addr := State.addr (ST s₀)
abbrev dp : Addr := State.addr (DP s₀)
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_fit : (ST s₀).toNat + 768 ≤ 2 ^ 32
  d_fit : (DP s₀).toNat + L s₀ ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyArm.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace APre
variable {s₀ : State} (hp : APre s₀)
include hp

theorem eaS {d : Nat} (hd : d < 768) : State.addr (ST s₀ + BitVec.ofNat 32 d) = st s₀ + BitVec.ofNat 64 d :=
  addr_off (by have := hp.st_fit; omega)

theorem sNat {d : Nat} (hd : d < 768) : (ST s₀ + BitVec.ofNat 32 d).toNat = (ST s₀).toNat + d := by
  have := hp.st_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem eaD {d : Nat} (hd : d < L s₀) : State.addr (DP s₀ + BitVec.ofNat 32 d) = dp s₀ + BitVec.ofNat 64 d :=
  addr_off (by have := hp.d_fit; omega)

theorem dNat {d : Nat} (hd : d < L s₀) : (DP s₀ + BitVec.ofNat 32 d).toNat = (DP s₀).toNat + d := by
  have := hp.d_fit
  have := L_lt s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem w_st {d n : Nat} (h : d + n ≤ 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem r_st {d n : Nat} (h : d + n ≤ 768) : InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

end APre

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < L s₀) :
    InRegions s₀.wr (dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## The calls -/

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `lr`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem block_noCalls : Impl.ChaCha20.Arm.block.noCalls = true := by lit_decide
theorem xor_noFrames : Impl.ChaCha20.Arm.Xor.xor.noFrames = true := by lit_decide

theorem block_call {s : State} {S B : BitVec 32} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = B)
    (hdj : (⟨State.addr B, 256⟩ : Region).Disjoint ⟨State.addr S, 64⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hB : B.toNat + 256 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr S, 64⟩] ++ [⟨State.addr B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr B, 256⟩] s s' →
      stateAt s'.mem (State.addr B) = Spec.ChaCha20.block (stateAt s.mem (State.addr S)) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockArm) Proof.ChaCha20.Arm.block_correct
    (rd := [⟨State.addr S, 64⟩]) (wr := [⟨State.addr B, 256⟩]) ?_ hc hw ?_ block_noCalls
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hS, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-- `vg_chacha20_xor`'s contract, with what its proof shows of `r0` and `r1`
on return. -/
def xorK : Contract isa :=
  { Proof.ChaCha20.xorArm with
    post := fun s s' => Proof.ChaCha20.xorArm.post s s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r3 }

theorem xor_call {s : State} {S D B : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = D)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (h3 : s.gpr .r3 = B) (hn : n < 2 ^ 32)
    (hSD : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hSB : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hDB : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32) (hB : B.toNat + 320 ≤ 2 ^ 32)
    (hc : Covers ([] ++ [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s s' →
      bytesAt s'.mem (State.addr D) n =
        List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr D) n) (keystream (stateAt s.mem (State.addr S)) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.callCalls (k := xorK) (fun s hs => Proof.ChaCha20.Arm.Xor.xor_regs s hs)
    (rd := []) (wr := [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) ?_ hc hw ?_
    xor_noFrames
  · simp only [xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hS, hD, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      h0, h1, h2, hn'] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost.1

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)

end VG.Proof.ChaCha20.Arm.Stream
