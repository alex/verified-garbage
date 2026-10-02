import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbBlocks

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` up to the first call

Untrusted: everything here is checked by Lean. The code saves the
registers, computes the bytes held back `h`, copies `f = min(len, 16 - h)`
bytes after them, and sets up the first call of `vg_cmac_aes_update`, which
chains the block held back if data is left (`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x3 : s₀.gpr .x3 = D
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbAArch64.pre s₀) :
    APre s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.x4]; exact BitVec.isLt _

theorem APre.x4' : s₀.gpr .x4 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.x4

theorem APre.x1' : s₀.gpr .x1 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.x1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hx2 : s.gpr .x2 = St + BitVec.ofNat 64 272) (hx3 : s.gpr .x3 = Dd)
    (hx4 : s.gpr .x4 = BitVec.ofNat 64 n) (hx5 : s.gpr .x5 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { x0 := hx0, x2 := hx2, x3 := hx3, x4 := hx4, x5 := hx5, rounds := hp.rounds, hn := hn
    x1 := by rw [hx1]; exact hp.x1'
    wc := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapD := hwrap
    wrapS := by have := hp.wS; omega
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .x2).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .x2).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .x2 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x2₁, g₁, sp₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.x5 fun d _ h => hp.inS (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [x2₁, hdx])) fun s₂ ⟨x9₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂ (by rw [g₂ _ (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g₂ _ (by decide) (by decide), x19₁, hp.x0]) (by rw [g₂ _ (by decide) (by decide), x21₁, hp.x3]))
    fun s₃ ⟨x8₃, x10₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega) x7₃ x6₃ x8₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) (e : r ≠ .x10) (f : r ≠ .x11) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a b c d, g₃ r a b c e f, g₂ r d e]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x21₁, hp.x3])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x10₃])
    (by rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x19₁, hp.x0])
    (by rw [g .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x23₁]))
    fun s₅ h₅ => ?_
  obtain ⟨x21₅, x22₅, x4₅, x0₅, x1₅, x2₅, x3₅, x5₅, sv₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x21) (b : r ≠ .x22) : s₅.gpr r = s₁.gpr r := by
    have hcc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have hc := hcc r hr
    rw [sv₅ r hr a b, g r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs x0₅
      (by rw [x1₅, g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x20₁]) x2₅ x3₅
      (by rw [x4₅, b1Of, leftOf]) x5₅ hrd hwr (by omega)
      (Offset.disjoint St (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩,
    by rw [k .x19 (by simp [preserved]) (by decide) (by decide), x19₁, hp.x0],
    by rw [k .x20 (by simp [preserved]) (by decide) (by decide), x20₁],
    x21₅, by rw [x22₅]; rfl, by rw [k .x23 (by simp [preserved]) (by decide) (by decide), x23₁],
    fun r hr a b c d e => by rw [k r hr c d, g₁ r a b c d e],
    by rw [sp₅, h₄.sp, sp₃, sp₂, sp₁], m₀, hrd, hwr⟩

end VG.Proof.CmacAes.Stream.AArch64
