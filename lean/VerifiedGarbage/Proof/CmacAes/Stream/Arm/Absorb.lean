import VerifiedGarbage.Proof.CmacAes.Stream.Arm.AbsorbBlocks

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_mov wp_ldrSp saveMem saveList_ok saveMem_frame
  readW_writeW_save)
open VG.Proof.CmacAes.Arm (saveMem_congr)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : BitVec 32) (L R : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = D
  a1 : (stackArg s₀ 1).toNat = L
  a2 : stackArg s₀ 2 = S
  r1 : (s₀.gpr .r1).toNat = R
  rd : s₀.rd = [⟨State.addr D, L⟩, ⟨stackArgAddr s₀ 0, 12⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩]
  st_d : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr D, L⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  d_s : (⟨State.addr D, L⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  a_st : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr St, 304⟩
  a_s : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (blw16 s₀).Disjoint ⟨State.addr St, 304⟩
  b_d : (blw16 s₀).Disjoint ⟨State.addr D, L⟩
  b_s : (blw16 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fD : D.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 12 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbArm.pre s₀) :
    APre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩

section
variable {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 32 := by rw [← hp.a1]; exact BitVec.isLt _

theorem APre.a1' : stackArg s₀ 1 = BitVec.ofNat 32 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.a1, toNat_ofNat32 hp.lt])

theorem APre.r1' : s₀.gpr .r1 = BitVec.ofNat 32 R :=
  BitVec.eq_of_toNat_eq (by rw [hp.r1, toNat_ofNat32 (by rcases hp.rounds with h | h | h <;> omega)])

theorem APre.argAddr {k : Nat} (hk : k < 3) : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.spf
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem APre.arg_sub {k : Nat} (hk : k < 3) : Region.Sub ⟨stackArgAddr s₀ k, 4⟩ ⟨stackArgAddr s₀ 0, 12⟩ := by
  rw [hp.argAddr hk]; exact Offset.sub_base _ (by omega)

theorem APre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨⟨stackArgAddr s₀ 0, 12⟩, by rw [hp.rd]; simp, ?_⟩
  rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega) (by omega)

/-- Offsets in the state. -/
theorem APre.aS {k : Nat} (hk : k < 304) : State.addr (St + BitVec.ofNat 32 k) = State.addr St + BitVec.ofNat 64 k :=
  addr_add (by have := hp.fSt; omega)

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) :
    Covers [⟨State.addr St + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr St, 304⟩, by simp, d, rfl, h⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) :
    Covers [⟨State.addr S + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr S, 2304⟩, by simp, d, rfl, h⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) :
    Covers [⟨State.addr D + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, L⟩, by simp, d, rfl, h⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : BitVec 32} {n : Nat} (hr0 : s.gpr .r0 = St) (hr1 : s.gpr .r1 = s₀.gpr .r1)
    (hr2 : s.gpr .r2 = St + BitVec.ofNat 32 272) (hr3 : s.gpr .r3 = Dd) (hr9 : s.gpr .r9 = BitVec.ofNat 32 n)
    (hr10 : s.gpr .r10 = S) (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hn : 16 * n < 2 ^ 32)
    (hdc : (⟨State.addr Dd, 16 * n⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨State.addr Dd, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2304⟩)
    (hbd : (blw16 s₀).Disjoint ⟨State.addr Dd, 16 * n⟩) (hfD : Dd.toNat + 16 * n ≤ 2 ^ 32)
    (hcov : Covers [⟨State.addr Dd, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    UArgs s St (St + BitVec.ofNat 32 272) Dd S R n := by
  have hw := hp.fSt
  have a272 := hp.aS (k := 272) (by decide)
  have c272 : Region.Sub ⟨State.addr St + BitVec.ofNat 64 272, 16⟩ ⟨State.addr St, 304⟩ :=
    Offset.sub_base _ (by decide)
  have hb : blw16 s = blw16 s₀ := by rw [blw16, hsp]
  exact
  { r0 := hr0, r2 := hr2, r3 := hr3, r9 := hr9, r10 := hr10, rounds := hp.rounds, hn := hn
    r1 := by rw [hr1]; exact hp.r1'
    hsp := by rw [hsp]; exact hp.sp
    wc := by rw [a272]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [a272]; exact hdc
    ds := hds.sub_right (Region.sub_prefix (by decide))
    cs := by rw [a272]; exact (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    bw := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bd := by rw [hb]; exact hbd
    bc := by rw [hb, a272]; exact hp.b_st.sub_right c272
    bs := by rw [hb]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fC := by rw [toNat_add_ofNat (by omega)]; omega
    fD := hfD
    fS := by have := hp.fS; omega
    reads := by
      rw [hrd, hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Covers.right (hp.inSt (d := 0) (n := 240) (by decide)) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩
      · exact hcov a k ⟨_, List.mem_singleton_self _, hc⟩
    writes := by
      rw [hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a272] at hc; exact hp.inSt (d := 272) (n := 16) (by decide) a k ⟨_, List.mem_singleton_self _, hc⟩
      · exact hp.inS (d := 0) (n := 2176) (by decide) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩ }

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2208 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem save_eq : save = .ldrSp .r12 8 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    [mov .r4 .r0, mov .r5 .r1, .ldrSp .r6 0, .ldrSp .r7 4, mov .r10 .r12]) := rfl

/-- The memory after saving the registers. -/
def aMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr saved

set_option simprocs false in
theorem aMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [aMem, saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem aMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (aMem s₀ S) :=
  saveMem_frame _ _ _ (by decide) saved fun p hp => by have := saved_bound p hp; omega

/-- What the saves leave. -/
structure ASave (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r2 : s.gpr .r2 = s₀.gpr .r2
  r3 : s.gpr .r3 = s₀.gpr .r3
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 32 L
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = aMem s₀ S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa (.block save) s₀ (ASave s₀ St D S L) := by
  have hS := hp.fS
  rw [save_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S := by rw [u₁.gpr]; exact hp.a2
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = aMem s₀ S := by
    rw [m₂, u₁.mem, h12, aMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  have arg (k : Nat) (hk : k < 3) : (aMem s₀ S).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k :=
    (aMem_frame s₀ S).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.sub_left (hp.arg_sub hk)) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have mm : ∀ {t : State}, t.mem = s₂.mem → t.mem = aMem s₀ S := fun h => h.trans hm₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other, hp.r0]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, hm₂, arg 0 (by decide), hp.a0]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂, arg 1 (by decide), hp.a1']
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, h12]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : BitVec 32) (c L : Nat) : Mem :=
  writeBytes (aMem s₀ S) (State.addr (St + BitVec.ofNat 32 (288 + held c)))
    (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : BitVec 32) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 32 272) (St + BitVec.ofNat 32 288) S R (b1Of (countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (countArm s₀).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (countArm s₀).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hL := hp.lt
  have hw := hp.fSt
  have hD := hp.fD
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (save_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp (c := c) hcl (by rw [h₁.r3, h₁.r2, count_eq, hc]))
    fun s₂ ⟨r0₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (held_le c) hL r0₂ (by rw [g₂ _ (by decide) (by decide), h₁.r7])
    (by rw [g₂ _ (by decide) (by decide), h₁.r4])) fun s₃ ⟨r1₃, r2₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c d, g₂ r a d]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  refine WP.seq (WP.mono (copy_wp (p := D) (c := St + BitVec.ofNat 32 (288 + held c)) (L := fOf c L) (x := L)
    hfL hL (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r6]) r2₃ (by rw [r1₃]; rfl)
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r7]) fun hpos => ?_) fun s₄ h₄ => ?_)
  · have hlt : 288 + held c < 304 := by unfold fOf at hpos; omega
    have aDst' : State.addr (St + BitVec.ofNat 32 (288 + held c)) = State.addr St + BitVec.ofNat 64 (288 + held c) :=
      hp.aS hlt
    exact
    { fp := by omega
      fc := by rw [toNat_add_ofNat (by omega)]; omega
      hr := by
        rw [rd₃', wr₃']
        have := hp.inD (d := 0) (n := fOf c L) (by omega)
        rwa [BitVec.add_zero] at this
      hw := by rw [wr₃', aDst']; exact hp.inSt (by omega)
      hd := by
        rw [aDst']
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Region.sub_prefix hfL) }
  have g' (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) (e : r ≠ .r6) (f : r ≠ .r7) :
      s₄.gpr r = s₁.gpr r := by rw [h₄.other r b c e f d, g r a b c d]
  refine WP.mono (chain1_wp (x := leftOf c L) (by unfold leftOf; omega) (by rw [h₄.r7]; rfl)
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4])) fun s₅ h₅ => ?_
  obtain ⟨r9₅, r0₅, r1₅, r2₅, r3₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (e : r ≠ .r9) (f : r ≠ .r12) (i : r ≠ .r6)
      (j : r ≠ .r7) : s₅.gpr r = s₁.gpr r := by rw [g₅ r a b c d e, g' r a b c f i j]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  have hsp : s₅.sp = s₀.sp := by rw [sp₅, h₄.sp, sp₃, sp₂, h₁.sp]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega
  have a288 := hp.aS (k := 288) (by decide)
  have c288 : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 288), 16 * b1Of c L⟩ ⟨State.addr St, 304⟩ := by
    rw [a288]; exact Offset.sub_base _ (by omega)
  subst hc
  refine ⟨hp.uargs (Dd := St + BitVec.ofNat 32 288) r0₅ (by rw [r1₅, h₄.other _ (by decide) (by decide) (by decide)
      (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide), h₁.r5]) r2₅ r3₅
      (by rw [r9₅, b1Of, leftOf]) (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h₁.r10]) hsp hrd hwr (by omega)
      (by rw [a288]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288))
      (hp.b_st.sub_right c288) (by rw [toNat_add_ofNat (by omega)]; omega)
      (Covers.right (by rw [a288]; exact hp.inSt (by omega))), ?_, ?_, ?_, ?_, ?_, hsp, ?_, ?_, hrd, hwr⟩
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4]
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r5]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₄.r6]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₄.r7]; rfl
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r10]
  · intro r hr a b c d e f
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k r this.1 this.2.1 this.2.2.1 this.2.2.2.1 e this.2.2.2.2 c d, h₁.keep r hr a b c d f]
  · rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]

end VG.Proof.CmacAes.Stream.Arm
