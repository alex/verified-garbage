import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps

/-!
# ECDSA on x86-64: where the ladder's and the powers' slots are

The slots of `c.ladderCfg`, `c.powP` and `c.powN` are numbered slots `c.sl i`
for distinct `i`, so they are apart as `ladder_ok` and `pow_ok` need
(`ladLay`, `powLayP`, `powLayN`): each fact is one about the numbers `i`,
which `decide` checks.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- `x` and `y`, `k` and `k'` bytes long, are apart. -/
abbrev Apart (x k y k' : Nat) : Prop := x + k ≤ y ∨ y + k' ≤ x

theorem sl_mem_map (hn : 0 < c.n) {i : Nat} {l : List Nat} : c.sl i ∈ l.map c.sl ↔ i ∈ l := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact sl_inj c hn e ▸ hj
  · exact List.mem_map_of_mem

theorem map_sl_disj (hn : 0 < c.n) {l₁ l₂ : List Nat} (h : ∀ i ∈ l₁, i ∉ l₂) :
    ∀ x ∈ l₁.map c.sl, x ∉ l₂.map c.sl := by
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi ((sl_mem_map hn).mp hx')

theorem map_sl_nodup (hn : 0 < c.n) {l : List Nat} (h : l.Nodup) : (l.map c.sl).Nodup :=
  List.Pairwise.map c.sl (fun _ _ hab e => hab (sl_inj c hn e)) h

/-- Numbered slots, apart from the modulus's and the temporary area. -/
theorem lay_map (hc : CfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  have hn := hc.n0
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le c hc.n7 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

/-- A numbered slot below the tables is apart from them. -/
theorem sl_below_bits (c : Cfg) {i : Nat} (hi : i < 45) (j t : Nat) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  have := sl_lt c hi
  rw [sl_eq c 45] at this
  rw [bitsAt_eq]
  omega

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd, by rw [hw, hr]; exact map_sl_disj hn hd⟩

theorem ladLay (hc : CfgOk c) : LadLay c.ladderCfg size := by
  have hn := hc.n0
  have h7 := hc.n7
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, GX, GY, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 31 by omega⟩, bitsAt_le c h7 (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, GX, GY, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c (i := TMP) (by decide) 0 0)

theorem powLay_of (hc : CfgOk c) {jm : Nat} (hjm : jm ∉ [ACC, PT, TMP]) (minv : BitVec 64)
    {base one j : Nat} (hj : j < 3) (hb : base ∉ [ACC, PT, TMP]) (hb45 : base < 45) (ho : one ≠ ACC)
    (ho45 : one < 45) :
    PowLay ⟨⟨c.n, c.sl jm, c.sl TMP, minv⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one, bitsAt c.n j,
      64 * c.n⟩ size := by
  have hn := hc.n0
  have h7 := hc.n7
  have hw : ∀ i, i ∉ [ACC, PT, TMP] →
      ∀ w ∈ powW ⟨⟨c.n, c.sl jm, c.sl TMP, minv⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one,
        bitsAt c.n j, 64 * c.n⟩, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rcases hw with rfl | rfl | rfl
    · exact sl_apart c hi.1
    · exact sl_apart c hi.2.1
    · exact sl_apart c hi.2.2
  refine ⟨sl_le c h7 (by decide), sl_le c h7 (by decide), sl_le c h7 hb45, sl_le c h7 ho45,
    bitsAt_le c h7 hj, ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 31 by omega⟩,
    sl_apart c (by decide), sl_apart c (by decide), sl_apart c (Ne.symm ho), hw base hb, ?_,
    hw jm hjm⟩
  intro w hw'
  simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl <;> exact Or.inr (sl_below_bits c (by decide) j 0)

theorem powLayP (hc : CfgOk c) : PowLay c.powP size :=
  powLay_of hc (jm := MP) (by decide) _ (j := 1) (by decide) (base := RZ) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide)

theorem powLayN (hc : CfgOk c) : PowLay c.powN size :=
  powLay_of hc (jm := MN) (by decide) _ (j := 2) (by decide) (base := KM) (by decide) (by decide)
    (one := ONEN) (by decide) (by decide)

end VG.Proof.Ecdsa.X86_64
