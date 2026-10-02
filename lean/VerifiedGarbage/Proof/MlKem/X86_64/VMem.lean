import VerifiedGarbage.Proof.MlKem.X86_64.VLanes
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.MlKem.X86_64.Ntt

/-!
# ML-KEM on x86-64: polynomials as words in the working space

A polynomial stored as 256 words (`S16`), 16-byte loads of eight of its
coefficients (`lanes_load`) and stores of them (`s16_write2`), and the table
of the zetas as words (`T16`), from which `vzeta` loads the zetas of up to
four blocks (`vzeta_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The address of word `i` of the array at `p`. -/
abbrev wAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (2 * i)

/-- Word `i` of the array at `p`. -/
def wordAt (m : Mem) (p : Addr) (i : Nat) : BitVec 16 := m.readW (wAddr p i) 16

/-- The polynomial `F` as 256 words at `p`. -/
def S16 (m : Mem) (p : Addr) (F : Poly) : Prop := ∀ i < 256, (wordAt m p i).toNat = (F[i]!).val

/-- The 512 bytes of a polynomial as words. -/
abbrev sR (p : Addr) : Region := ⟨p, 512⟩

theorem wAddr_add (p : Addr) (j e : Nat) : wAddr p j + BitVec.ofNat 64 (2 * e) = wAddr p (j + e) := by
  rw [wAddr, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem lanes_load {m : Mem} {p : Addr} {F : Poly} (h : S16 m p F) {j : Nat} (hj : j + 8 ≤ 256) :
    Lanes (m.readW (wAddr p j) 128) (fun e => F[j + e]!) := fun e he => by
  rw [word_readW _ _ he, wAddr_add]; exact h _ (by omega)

/-- Word `i` after storing `x` at word `j`. -/
theorem wordAt_write128 (m : Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    wordAt (m.writeW (wAddr p j) x) p i = if j ≤ i ∧ i < j + 8 then word x (i - j) else wordAt m p i := by
  split
  · rename_i h
    rw [wordAt, show wAddr p i = wAddr p j + BitVec.ofNat 64 (2 * (i - j)) by
      rw [wAddr_add, show j + (i - j) = i by omega]]
    exact readW_writeW128_16 _ _ _ (by omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Two vectors stored into the words of a polynomial, with the lanes `a` and `b`. -/
theorem s16_write2 {m : Mem} {p : Addr} {P R : Poly} (hP : S16 m p P) {j j' : Nat}
    (hj : j + 8 ≤ 256) (hj' : j' + 8 ≤ 256) (hsep : j + 8 ≤ j' ∨ j' + 8 ≤ j) {x y : BitVec 128}
    {a b : Nat → Zq} (hx : Lanes x a) (hy : Lanes y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 8 then a (i - j)
      else if j' ≤ i ∧ i < j' + 8 then b (i - j') else P[i]!) :
    S16 ((m.writeW (wAddr p j) x).writeW (wAddr p j') y) p R := fun i hi => by
  rw [wordAt_write128 _ _ hj' _ hi, wordAt_write128 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact hy _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact hx _ (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact hP i hi

theorem sR_contains (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) : (sR p).Contains (wAddr p j) 16 :=
  Offset.contains_base p (by omega) (by omega)

theorem frame_write2 {m m' : Mem} {p : Addr} (hf : Frame [sR p] m m') {j j' : Nat} (hj : j + 8 ≤ 256)
    (hj' : j' + 8 ≤ 256) (x y : BitVec 128) :
    Frame [sR p] m ((m'.writeW (wAddr p j) x).writeW (wAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (sR_contains p hj)).writeW (List.mem_singleton_self _) y
    (sR_contains p hj')

/-! ## The table of zetas -/

/-- The 128 words `ζ^BitRev7(k) · 2¹⁶ mod q` at `p`. -/
def T16 (m : Mem) (p : Addr) : Prop := ∀ k < 128, (wordAt m p k).toNat = (zeta k).val * 65536 % 3329

/-- Writes to the polynomial's words, 256 bytes above the table, keep it. -/
theorem T16.frame {m m' : Mem} {p : Addr} (h : T16 m p) (hf : Frame [sR (p + BitVec.ofNat 64 256)] m m') :
    T16 m' p := fun k hk => by
  rw [wordAt, hf.readW (r := ⟨p, 256⟩) (Offset.contains_base p (by omega) (by omega))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint p (by omega) (by omega))
    (by decide)]
  exact h k hk

/-- The doubleword that `pshufd` with `o` puts in place `j`. -/
def sel (o : BitVec 8) (j : Nat) : Nat := (o.extractLsb' (2 * j) 2).toNat

theorem sel_lt (o : BitVec 8) (j : Nat) : sel o j < 4 := by unfold sel; exact BitVec.isLt _

theorem word_shufDwords (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 8) :
    word (shufDwords a o) i = word a (2 * sel o (i / 2) + i % 2) := by
  have hs := sel_lt o (i / 2)
  rw [word_eq_dword _ hi, dword_shufDwords _ _ (by omega)]
  change BitVec.extractLsb' _ 16 (dword a (sel o (i / 2))) = _
  generalize sel o (i / 2) = t at *
  rw [word_eq_dword _ (show 2 * t + i % 2 < 8 by omega), show (2 * t + i % 2) / 2 = t by omega,
    show (2 * t + i % 2) % 2 = i % 2 by omega]

/-- The zetas that `vzeta o` leaves in `xmm13`, from the words at `wAddr zP k`. -/
theorem zeta_lanes (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 128) {m : Mem}
    (ht : T16 m zP) :
    ZLanes (shufDwords (XBinOp.eval .punpcklwd (m.readW (wAddr zP k) 128) (m.readW (wAddr zP k) 128)) o)
      (fun i => zeta (k + sel o (i / 2))) := fun i hi => by
  dsimp only
  have hs := sel_lt o (i / 2)
  have hk' := hk (i / 2) (by omega)
  rw [word_shufDwords _ _ hi]
  generalize sel o (i / 2) = t at *
  rw [word_punpcklwd _ _ (by omega), ite_self, show (2 * t + i % 2) / 2 = t by omega,
    word_readW _ _ (by omega), wAddr_add]
  exact ht _ hk'

theorem vzeta_ok (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 128) {s : State}
    (h8 : s.gpr .r8 = wAddr zP k) (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : T16 s.mem zP) :
    WP isa (.block (vzeta o)) s fun s' =>
      ZLanes (s'.xmm .xmm13) (fun i => zeta (k + sel o (i / 2))) ∧ XOnly [.xmm13] s s' := by
  simp only [vzeta, xb]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128, ea_at,
    add_ofNat_zero, h8, hin, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, by xonly⟩
  simp only [xmm_setXmm, ite_true]
  have hs := sel_lt o (i / 2)
  have hk' := hk (i / 2) (by omega)
  rw [word_shufDwords _ _ hi]
  generalize sel o (i / 2) = t at *
  rw [word_punpcklwd _ _ (by omega), ite_self, show (2 * t + i % 2) / 2 = t by omega,
    word_readW _ _ (by omega), wAddr_add]
  exact ht _ hk'

end VG.Proof.MlKem.X86_64
