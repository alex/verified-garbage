import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table
import VerifiedGarbage.Proof.MlKem.X86_64.VMem
import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

/-!
# ML-DSA on x86-64: four coefficients at a time in memory

Untrusted: everything here is checked by Lean. 16-byte loads of four
coefficients of a stored polynomial (`dlanes_load`) and stores of them
(`polyIs_write2`), and the table of the zetas in Montgomery form
(`Tab zmTab`), from which `vzeta` loads the zetas of up to four blocks
(`vzeta_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly xmm_setXmm ifp ifn sel sel_lt add_ofNat_zero)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)

theorem dlanes_load {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat} (hj : j + 4 ≤ 256) :
    DLanes (m.readW (coeffAddr p j) 128) (fun e => F[j + e]!) := fun e he => by
  rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq]
  exact polyIs_toNat h (by rw [n_eq]; omega)

/-- Coefficient `i` after storing `x` at coefficient `j`. -/
theorem coeffAt_write128 (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i = if j ≤ i ∧ i < j + 4 then dword x (i - j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega]]
    exact readW_writeW128 _ _ _ (by omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Two vectors stored into a polynomial, with the lanes `a` and `b`. -/
theorem polyIs_write2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) (hsep : j + 4 ≤ j' ∨ j' + 4 ≤ j) {x y : BitVec 128}
    {a b : Nat → Zq} (hx : DLanes x a) (hy : DLanes y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 4 then a (i - j)
      else if j' ≤ i ∧ i < j' + 4 then b (i - j') else P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) p R := polyIs_of_toNat fun i hi => by
  rw [n_eq] at hi
  rw [coeffAt_write128 _ _ hj' _ hi, coeffAt_write128 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 4
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact hy _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact hx _ (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact polyIs_toNat hP (by rw [n_eq]; exact hi)

theorem pR_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) : (pR p).Contains (coeffAddr p j) 16 :=
  Offset.contains_base p (by omega) (by omega)

theorem frame_write2 {m m' : Mem} {p : Addr} (hf : Frame [pR p] m m') {j j' : Nat} (hj : j + 4 ≤ 256)
    (hj' : j' + 4 ≤ 256) (x y : BitVec 128) :
    Frame [pR p] m ((m'.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (pR_contains p hj)).writeW (List.mem_singleton_self _) y
    (pR_contains p hj')

/-! ## The table of zetas -/

theorem zmTab_lt (k : Nat) : zmTab k < q := Nat.mod_lt _ (by decide)

theorem zmTab_eq (k : Nat) : zmTab k = (zetas k).val * 2 ^ 32 % q := by
  rw [zmTab, ← zetaNat_eq, zetaNat, Nat.mod_mul_mod]

/-- The zeta at index `k` of the table. -/
theorem tab_zeta {m : Mem} {zP : Addr} (ht : Tab zmTab m zP 256) {k : Nat} (hk : k < 256) :
    (m.readW (coeffAddr zP k) 32).toNat = (zetas k).val * 2 ^ 32 % q := by
  rw [← coeffAt_eq, ht k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (zmTab_lt k) (by decide)),
    zmTab_eq]

theorem dword_shufDwords_sel (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (shufDwords a o) i = dword a (sel o i) := dword_shufDwords a o hi

theorem vzeta_ok (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 256) {s : State}
    (h8 : s.gpr .r8 = coeffAddr zP k) (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16)
    (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block (vzeta o)) s fun s' =>
      ZLanes (s'.xmm .xmm13) (fun i => zetas (k + sel o i)) ∧ ZOdd (s'.xmm .xmm13) (s'.xmm .xmm12) ∧
        XOnly [.xmm13, .xmm12] s s' := by
  simp only [vzeta]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128, ea_atD,
    add_ofNat_zero, h8, hin, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun j hj => ?_, by xonly⟩
  · simp only [xmm_setXmm, ite_true, ite_false, reduceCtorEq]
    have hs := sel_lt o i
    rw [dword_shufDwords_sel _ _ hi, dword_readW _ _ hs, coeffAddr_add]
    exact tab_zeta ht (hk i hi)
  · simp only [xmm_setXmm, ite_true, ite_false, reduceCtorEq]
    rw [dword_shufDwords _ _ (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

end VG.Proof.MlDsa.X86_64.Arith
