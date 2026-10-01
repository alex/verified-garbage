import VerifiedGarbage.Proof.MlKem.AArch64.NttVec

/-!
# ML-KEM on AArch64: `vg_mlkem_add` and `vg_mlkem_sub`

Untrusted: everything here is checked by Lean. Both are `mapLoop` around an
arithmetic step; the loop is proven once for any step that computes a
function `F` of the two coefficients (`OpSpec`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem

/-- The contract the proofs are written against (and verified callers use);
the artifacts' are the shared contracts of `Spec/`, which imply it.
AArch64 contract for `f = x0, g = x1` (both `[u32; 256]`): if the
polynomials at `f` and `g` are reduced, `f` becomes `op (f, g)`, reduced.
The code may read `g` and read and write `f`, which do not overlap. -/
def accAArch64 (op : Poly → Poly → Poly) : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 1024⟩] ∧ s.wr = [⟨s.gpr .x0, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 1024⟩ ∧
    Reduced s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1)
  post s s' :=
    PolyIs s'.mem (s.gpr .x0) (op (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem

/-- `op` computes `F a b` in the lanes of `v2` from those of `v0 = a` and
`v1 = b`, with `q` in the lanes of `v16`, changing only `v2` and `v3`. -/
def VOpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (A B : Nat → Nat), (∀ e < 4, A e < q) →
    (∀ e < 4, B e < q) → Lanes (s.v .v0) A → Lanes (s.v .v1) B → Lanes (s.v .v16) (fun _ => 3329) →
    (∀ s', VChg [.v2, .v3] s s' → Lanes (s'.v .v2) (fun e => F (A e) (B e)) → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem vaddOp_spec : VOpSpec vaddOp fun a b => condSub (a + b) := by
  intro is s Q A B hA hB lA lB hq k
  have q_ : q = 3329 := rfl
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ := lanes_add lA lB
  rw [← h₁.v] at l₁
  refine vcsub_ok (by decide) (by rw [h₁.get .v16]; exact hq) (f := fun e => (A e + B e) % 2 ^ 32) l₁
    (fun e he => by have := hA e he; have := hB e he; omega) fun s₂ h₂ l₂ =>
    k s₂ (h₁.chg.trans h₂ |>.mono) (l₂.congr fun e he => ?_)
  have := hA e he; have := hB e he
  simp only [condSub]; split <;> omega

theorem vsubOp_spec : VOpSpec vsubOp fun a b => condSub (a + q - b) := by
  intro is s Q A B hA hB lA lB hq k
  have q_ : q = 3329 := rfl
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => wp_vop (d := .v3) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg |>.mono) ?_
  have l₁ := lanes_sub lA lB
  rw [← h₁.v] at l₁
  have q₁ : Lanes (s₁.v .v16) fun _ => 3329 := by rw [h₁.get .v16]; exact hq
  have l₂ := lanes_add l₁ q₁
  rw [← h₂.v] at l₂
  have a₂ : Lanes (s₂.v .v2) fun e => (2 ^ 32 - B e + A e) % 2 ^ 32 := by rw [h₂.get .v2]; exact l₁
  have l₃ := lanes_umin a₂ l₂
  rw [← h₃.v] at l₃
  refine l₃.congr fun e he => ?_
  have := hA e he; have := hB e he
  show min _ _ = _
  simp only [condSub]; split <;> omega

/-! ## The loop -/

section
variable (F : Nat → Nat → Nat) (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev gP : Addr := s₀.gpr .x1

/-- The new value of coefficient `i`. -/
def newC (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (F (coeffAt s₀.mem (fP s₀) i).toNat (coeffAt s₀.mem (gP s₀) i).toNat)

end

structure AccPre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (gP s₀)]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (polyRegion (fP s₀)).Disjoint (polyRegion (gP s₀))
  f : Reduced s₀.mem (fP s₀)
  g : Reduced s₀.mem (gP s₀)

/-- After `k` vectors of four coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = coeffAddr (fP s₀) (4 * k)
  x1 : s.gpr .x1 = coeffAddr (gP s₀) (4 * k)
  x10 : (s.gpr .x10).toNat = 64 - k
  q16 : Lanes (s.v .v16) fun _ => 3329
  f : CoeffsUpTo s.mem (fP s₀) (4 * k) (newC F s₀) (coeffAt s₀.mem (fP s₀))
  g : ∀ i < 256, coeffAt s.mem (gP s₀) i = coeffAt s₀.mem (gP s₀) i

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : VOpSpec op F) {s₀ : State}
    (hp : AccPre s₀) {k : Nat} (hk : k < 64) {s : State} (h : MapInv F s₀ k s) :
    WP isa (.block (vmapBody op)) s fun s' =>
      MapInv F s₀ (k + 1) s' ∧ ((s'.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 64) := by
  show WP isa (.block (.ldrq .v0 .x0 0 :: .ldrq .v1 .x1 0 :: (op ++
    (.strq .v2 .x0 0 :: ([.addImm .x .x0 .x0 16, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1] ++
      []))))) s _
  have hj : 4 * k + 4 ≤ 256 := by omega
  refine wp_ldrq (a := coeffAddr (fP s₀) (4 * k)) (by decide) (by rw [h.x0, ptr_zero]) ?_
    fun s₁ h₁ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd_wr (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  refine wp_ldrq (a := coeffAddr (gP s₀) (4 * k)) (by decide) (by rw [h₁.gpr, h.x1, ptr_zero]) ?_
    fun s₂ h₂ => ?_
  · rw [h₁.rd, h₁.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  have lA : Lanes (s₂.v .v0) fun e => (coeffAt s₀.mem (fP s₀) (4 * k + e)).toNat := by
    rw [h₂.get .v0, h₁.v]
    exact lanes_coeffs fun e he => by rw [h.f _ (by omega), ite_eq_right (by omega)]
  have lB : Lanes (s₂.v .v1) fun e => (coeffAt s₀.mem (gP s₀) (4 * k + e)).toNat := by
    rw [h₂.v, h₁.mem]
    exact lanes_coeffs fun e he => by rw [h.g _ (by omega)]
  have q₂ : Lanes (s₂.v .v16) fun _ => 3329 := by rw [h₂.get .v16, h₁.get .v16]; exact h.q16
  refine hop _ s₂ _ _ _ (fun e _ => hp.f _ (by rw [n_eq]; omega))
    (fun e _ => hp.g _ (by rw [n_eq]; omega)) lA lB q₂ fun s₃ h₃ l₃ => ?_
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_strq (a := coeffAddr (fP s₀) (4 * k)) (by decide) (by rw [g₃, h.x0, ptr_zero]) ?_
    fun s₄ h₄ => ?_
  · rw [h₃.wr, h₂.wr, h₁.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x0, .x1, .x10] s₄ w' ∧ w'.mem = s₄.mem ∧
      w'.gpr .x0 = s₄.gpr .x0 + BitVec.ofNat 64 16 ∧ w'.gpr .x1 = s₄.gpr .x1 + BitVec.ofNat 64 16 ∧
      w'.gpr .x10 = s₄.gpr .x10 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
      wp_subImm (by decide) fun s₇ h₇ e₇ => wp_nil ⟨((h₅.keep.trans h₆.keep).trans h₇.keep).mono,
        by rw [h₇.mem, h₆.mem, h₅.mem], by rw [h₇.get .x0, h₆.get .x0, e₅],
        by rw [h₇.get .x1, e₆, h₅.get .x1], by rw [e₇, h₆.get .x10, h₅.get .x10]⟩))
    fun s' ⟨⟨k', m', e0, e1, e10⟩, hv⟩ => ?_
  have g₄ : s₄.gpr = s.gpr := by rw [h₄.gpr, g₃]
  have c10 : (s₄.gpr .x10).toNat = 64 - k := by rw [g₄, h.x10]
  have v10 : (s'.gpr .x10).toNat = 64 - (k + 1) := by
    rw [e10, toNat_sub_n (by rw [c10]; simp; omega), c10]; simp; omega
  have mm : s'.mem = s.mem.write (coeffAddr (fP s₀) (4 * k)) 16 (s₃.v .v2) := by
    rw [m', h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have k₄ := ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans k')
  refine ⟨⟨by rw [k₄.rd, h.rd], by rw [k₄.wr, h.wr], by rw [k₄.sp, h.sp], ?_, ?_, v10, ?_, ?_,
    fun i hi => ?_⟩, by rw [v10]; omega⟩
  · rw [e0, g₄, h.x0, coeffAddr_step, show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [e1, g₄, h.x1, coeffAddr_step, show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [hv, h₄.v, h₃.get .v16, h₂.get .v16, h₁.get .v16]; exact h.q16
  · rw [mm, show 4 * (k + 1) = 4 * k + 4 by omega]
    refine CoeffsUpTo.write16 h.f hj fun e he => BitVec.eq_of_toNat_eq ?_
    rw [l₃ e he, newC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (l₃.lt he)]
  · rw [mm, coeffAt_frame (frame16 (Frame.refl _ _) hj _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.disj.symm) hi, h.g i hi]

theorem map_loop {op : List Instr} {F : Nat → Nat → Nat} (hop : VOpSpec op F) {s₀ : State}
    (hp : AccPre s₀) : WP isa (vmapLoop op) s₀ (MapInv F s₀ 64) := by
  refine WP.seq ?_
  show WP isa (.block ([Instr.movz .x .x9 3329 0] ++ (.vop (.dup .s4 .v16 .x9) ::
    ([.movz .x .x10 64 0] ++ [])))) s₀ _
  refine wp_scalar (by decide) (P := fun s₁ => Keep [.x9] s₀ s₁ ∧ s₁.mem = s₀.mem ∧
      (s₁.gpr .x9).toNat = 3329)
    (wp_movz fun s₁ h₁ e₁ => wp_nil ⟨h₁.keep, h₁.mem, by rw [e₁]; rfl⟩) fun s₁ ⟨k₁, m₁, e9⟩ _ => ?_
  refine wp_vop (d := .v16) rfl fun s₂ h₂ => ?_
  refine wp_scalar (by decide) (P := fun s₃ => Keep [.x10] s₂ s₃ ∧ s₃.mem = s₂.mem ∧
      (s₃.gpr .x10).toNat = 64)
    (wp_movz fun s₃ h₃ e₃ => wp_nil ⟨h₃.keep, h₃.mem, by rw [e₃]; rfl⟩) fun s₃ ⟨k₃, m₃, e10⟩ hv₃ =>
    wp_nil ?_
  refine count_loop (by decide) (MapInv F s₀) (fun k hk s h => map_step hop hp hk h) ?_
  have k₃ := (k₁.trans h₂.keep).trans k₃
  have m : s₃.mem = s₀.mem := by rw [m₃, h₂.mem, m₁]
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, coeffAddr]; exact (BitVec.add_zero _).symm,
    by rw [k₃.get .x1, coeffAddr]; exact (BitVec.add_zero _).symm, by rw [e10], ?_, fun i hi => ?_,
    fun i hi => by rw [m]⟩
  · rw [hv₃, h₂.v]
    exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e9]
  · rw [m, ite_eq_right (by omega)]

theorem map_correct {op : List Instr} {F : Nat → Nat → Nat} (hop : VOpSpec op F)
    {G : Poly → Poly → Poly}
    (hG : ∀ P R : Poly, ∀ i < n, ((G P R)[i]!).val = F (P[i]!).val (R[i]!).val)
    (hpres : (vmapLoop op).allInstrs (keeps (RegSet.ofList preserved)) = true)
    (s : State) (hs : (accAArch64 G).pre s)
    (hv : (vmapLoop op).allInstrs keepsV = true := by decide +kernel) :
    ∃ t s', Exec isa (vmapLoop op) s t s' ∧ abiPreserved s s' ∧ (accAArch64 G).post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hp : AccPre s := ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨t, s', he, hI⟩ := map_loop (F := F) hop hp
  refine ⟨t, s', he, abi_of rfl hpres he hv, ?_⟩
  show PolyIs s'.mem (fP s) (G (polyAt s.mem (fP s)) (polyAt s.mem (gP s)))
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [hI.f i hi, ite_eq_left (by rw [n_eq] at hi; omega), newC, hG _ _ i hi, polyAt_val hp.f hi,
    polyAt_val hp.g hi]

theorem map_ct {op : List Instr} {G : Poly → Poly → Poly}
    (h : (Taint.check taint (Taint.ofRegs [.x0, .x1]) (vmapLoop op)
      (Taint.hintOf taint (Taint.ofRegs [.x0, .x1]) (vmapLoop op))).isSome = true) :
    ConstantTime isa (accAArch64 G).pre (accAArch64 G).pub (vmapLoop op) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ h
  intro s₁ s₂ _ _ ⟨h0, h1, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

/-! ## `add` and `sub` -/

/-- A state satisfying the preconditions: two polynomials of zeros. -/
def accSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_correct : ∀ s, (accAArch64 Spec.MlKem.add).pre s →
    ∃ t s', Exec isa Impl.MlKem.AArch64.add s t s' ∧ abiPreserved s s' ∧
      (accAArch64 Spec.MlKem.add).post s s' :=
  map_correct vaddOp_spec (fun P R i hi => by rw [add_get _ _ hi, val_add]) (by decide +kernel)

theorem sub_correct : ∀ s, (accAArch64 Spec.MlKem.sub).pre s →
    ∃ t s', Exec isa Impl.MlKem.AArch64.sub s t s' ∧ abiPreserved s s' ∧
      (accAArch64 Spec.MlKem.sub).post s s' :=
  map_correct vsubOp_spec (fun P R i hi => by rw [sub_get _ _ hi, val_sub]) (by decide +kernel)

theorem add_verified :
    Verified AArch64.target Impl.MlKem.AArch64.add (Spec.MlKem.addContract AArch64.abi) :=
  Verified.of_correct add_correct (map_ct (by taint_decide)) (by
    mlkem_implies [Spec.MlKem.addContract, Spec.MlKem.accSig, accAArch64, AArch64.abi,
      AArch64.argRegs] [accSat] using accSat)

theorem sub_verified :
    Verified AArch64.target Impl.MlKem.AArch64.sub (Spec.MlKem.subContract AArch64.abi) :=
  Verified.of_correct sub_correct (map_ct (by taint_decide)) (by
    mlkem_implies [Spec.MlKem.subContract, Spec.MlKem.accSig, accAArch64, AArch64.abi,
      AArch64.argRegs] [accSat] using accSat)

end VG.Proof.MlKem.AArch64
