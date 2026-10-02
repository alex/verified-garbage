import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbBlocks

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = D
  r8 : (s₀.gpr .r8).toNat = L
  r9 : s₀.gpr .r9 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, L⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, L⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbX86_64.pre s₀) :
    APre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r8]; exact BitVec.isLt _

theorem APre.r8' : s₀.gpr .r8 = BitVec.ofNat 64 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.r8, toNat_ofNat hp.lt])

theorem APre.rsi' : s₀.gpr .rsi = BitVec.ofNat 64 R := rsi_ofNat hp.rsi hp.rounds

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hrdi : s.gpr .rdi = St)
    (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdx : s.gpr .rdx = St + BitVec.ofNat 64 272) (hrcx : s.gpr .rcx = Dd)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (hr9 : s.gpr .r9 = S) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩)
    (hstk : (below (s₀.gpr .rsp) 16).Disjoint ⟨Dd, 16 * n⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { rdi := hrdi, rdx := hrdx, rcx := hrcx, r8 := hr8, r9 := hr9, rounds := hp.rounds, hn := hn
    rsi := by rw [hrsi]; exact hp.rsi'
    wc := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    stkW := by rw [hsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkD := by rw [hsp]; exact hstk
    stkC := by rw [hsp]; exact hp.stk_st.sub_right c272
    stkS := by rw [hsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
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
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .rdx).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .rdx).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .rdx = BitVec.ofNat 64 c := BitVec.eq_of_toNat_eq (by rw [hc, toNat_ofNat hcl])
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r13₁, r14₁, r15₁, rdx₁, rsp₁, zf₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.r9 fun d _ h => hp.inS (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [rdx₁, hdx]) (by rw [zf₁, rdx₁])) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) hL ax₂ (by rw [g₂ _ (by decide), r14₁, hp.r8'])
    (by rw [g₂ _ (by decide), rbx₁, hp.rdi])) fun s₃ ⟨cx₃, dx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c, g₂ r a]
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (L := fOf c L) (by omega)
    (by rw [g _ (by decide) (by decide) (by decide), r13₁, hp.rcx]) dx₃ cx₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega))
    (fun i hi => by
      rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  have g' (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) (d : r ≠ .r10) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a d, g r a b c]
  refine WP.mono (chain1_wp hfL hL (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r13₁, hp.rcx])
    (by rw [h₄.other _ (by decide) (by decide), cx₃])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r14₁, hp.r8'])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), rbx₁, hp.rdi])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r15₁])) fun s₅ h₅ => ?_
  obtain ⟨r13₅, r14₅, r8₅, rdi₅, rsi₅, rdx₅, rcx₅, r9₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r13) (b : r ≠ .r14) : s₅.gpr r = s₁.gpr r := by
    rw [sv₅ r hr a b, g' r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hsp : s₅.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rsp₁]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs rdi₅ (by rw [rsi₅, g' _ (by decide) (by decide) (by decide) (by decide), rbp₁]) rdx₅ rcx₅
      (by rw [r8₅, b1Of, leftOf]) r9₅ hsp hrd hwr (by omega)
      (Offset.disjoint St (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (hp.stk_st.sub_right c288) (by rw [toNat_add_lt St hw (by decide)]; omega)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩,
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbx₁, hp.rdi],
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbp₁],
    r13₅, by rw [r14₅]; rfl, by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), r15₁], hsp, m₀, hrd,
    hwr⟩

end VG.Proof.CmacAes.Stream.X86_64
