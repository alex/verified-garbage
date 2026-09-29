import VerifiedGarbage.Proof.MlKem.AArch64.Common

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

/-- `op` computes `F a b` in `x11` from `x11 = a` and `x12 = b`, with
`x9 = q`, changing only `x11`–`x13`. -/
def OpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (a b : Nat), a < q → b < q →
    (s.gpr .x11).toNat = a → (s.gpr .x12).toNat = b → (s.gpr .x9).toNat = q →
    (∀ s', Only [.x11, .x12, .x13] s s' → (s'.gpr .x11).toNat = F a b → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem addOp_spec : OpSpec addOp fun a b => condSub (a + b) := by
  intro is s Q a b ha hb h11 h12 h9 k
  have hq : q = 3329 := rfl
  refine wp_add fun s₁ h₁ e₁ => csub_ok (x := a + b) (by decide) (by decide) (by decide)
    (by omega) ?_ (by rw [h₁.get .x9]; exact h9) fun s₂ h₂ e₂ => k s₂ (h₁.trans h₂ |>.mono) e₂
  rw [e₁, toNat_add_n (by rw [h11, h12]; omega), h11, h12]

theorem subOp_spec : OpSpec subOp fun a b => condSub (a + q - b) := by
  intro is s Q a b ha hb h11 h12 h9 k
  have hq : q = 3329 := rfl
  refine wp_add fun s₁ h₁ e₁ => wp_sub fun s₂ h₂ e₂ =>
    csub_ok (x := a + q - b) (by decide) (by decide) (by decide) (by omega) ?_
      (by rw [h₂.get .x9, h₁.get .x9]; exact h9)
      fun s₃ h₃ e₃ => k s₃ ((h₁.trans h₂).trans h₃ |>.mono) e₃
  have v₁ : (s₁.gpr .x11).toNat = a + q := by
    rw [e₁, toNat_add_n (by rw [h11, h9]; omega), h11, h9]
  rw [e₂, toNat_sub_n (by rw [v₁, h₁.get .x12, h12]; omega), v₁, h₁.get .x12, h12]

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

/-- After `k` coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = fP s₀ + BitVec.ofNat 64 (4 * k)
  x1 : s.gpr .x1 = gP s₀ + BitVec.ofNat 64 (4 * k)
  x9 : (s.gpr .x9).toNat = q
  x10 : (s.gpr .x10).toNat = 256 - k
  f : ∀ i < 256, coeffAt s.mem (fP s₀) i = if i < k then newC F s₀ i else coeffAt s₀.mem (fP s₀) i
  g : ∀ i < 256, coeffAt s.mem (gP s₀) i = coeffAt s₀.mem (gP s₀) i

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F) {s₀ : State} (hp : AccPre s₀) {k : Nat} (hk : k < 256)
    {s : State} (h : MapInv F s₀ k s) :
    WP isa (.block (mapBody op)) s fun s' =>
      MapInv F s₀ (k + 1) s' ∧ ((s'.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 256) := by
  rw [show mapBody op = .ldr .w .x11 .x0 0 :: .ldr .w .x12 .x1 0 :: (op ++
    ([.str .w .x11 .x0 0, .addImm .x .x0 .x0 4, .addImm .x .x1 .x1 4, .subImm .x .x10 .x10 1] :
      List Instr)) from rfl]
  have hk' : k < n := hk
  refine wp_ldrw (a := coeffAddr (fP s₀) k) (by decide) (by rw [h.x0, ptr_zero]) ?_
    fun s₁ h₁ e₁ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd_wr (in_regions (List.mem_singleton_self _) (coeff_contains _ hk'))
  refine wp_ldrw (a := coeffAddr (gP s₀) k) (by decide) (by rw [h₁.get .x1, h.x1, ptr_zero]) ?_
    fun s₂ h₂ e₂ => ?_
  · rw [h₁.rd, h₁.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (coeff_contains _ hk'))
  have ca : coeffAt s.mem (fP s₀) k = coeffAt s₀.mem (fP s₀) k := by
    rw [h.f k hk, ite_eq_right (Nat.lt_irrefl k)]
  have ha : (coeffAt s₀.mem (fP s₀) k).toNat < q := hp.f k hk'
  have hb : (coeffAt s₀.mem (gP s₀) k).toNat < q := hp.g k hk'
  have v₁₁ : (s₂.gpr .x11).toNat = (coeffAt s₀.mem (fP s₀) k).toNat := by
    rw [h₂.get .x11, e₁, toNat_readW32, ← coeffAt_eq, ca]
  have v₁₂ : (s₂.gpr .x12).toNat = (coeffAt s₀.mem (gP s₀) k).toNat := by
    rw [e₂, toNat_readW32, h₁.mem, ← coeffAt_eq, h.g k hk]
  refine hop _ s₂ _ _ _ ha hb v₁₁ v₁₂ (by rw [h₂.get .x9, h₁.get .x9, h.x9]) fun s₃ h₃ e₃ => ?_
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  refine wp_strw (a := coeffAddr (fP s₀) k) (by decide) (by rw [k₃.get .x0, h.x0, ptr_zero]) ?_
    fun s₄ h₄ => wp_addImm (by decide) fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
    wp_subImm (by decide) fun s₇ h₇ e₇ => wp_nil ?_
  · rw [k₃.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (coeff_contains _ hk')
  have k₇ := (((k₃.trans h₄.keep).trans h₅.keep).trans h₆.keep).trans h₇.keep
  have m₃ : s₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have m₇ : s₇.mem = s.mem.writeW (coeffAddr (fP s₀) k) (newC F s₀ k) := by
    rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, m₃, setWidth32_of_toNat e₃]
    rfl
  have c10 : (s₆.gpr .x10).toNat = 256 - k := by
    rw [h₆.get .x10, h₅.get .x10, h₄.gpr, k₃.get .x10, h.x10]
  have v10 : (s₇.gpr .x10).toNat = 256 - (k + 1) := by
    rw [e₇, toNat_sub_n (by rw [c10]; simp; omega), c10]
    simp
    omega
  refine ⟨⟨by rw [k₇.rd, h.rd], by rw [k₇.wr, h.wr], by rw [k₇.sp, h.sp], ?_, ?_,
    by rw [k₇.get .x9, h.x9], v10, fun i hi => ?_, fun i hi => ?_⟩, by rw [v10]; omega⟩
  · rw [h₇.get .x0, h₆.get .x0, e₅, h₄.gpr, k₃.get .x0, h.x0, ptr_next]
  · rw [h₇.get .x1, e₆, h₅.get .x1, h₄.gpr, k₃.get .x1, h.x1, ptr_next]
  · rw [m₇, coeffAt_writeW _ _ (show i < n from hi) hk']
    by_cases e : k = i
    · subst e; simp
    · rw [ite_eq_right e, h.f i hi]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega)]
      · rw [ite_eq_right hik, ite_eq_right (by omega)]
  · rw [m₇, coeffAt_writeW_sep _ _ _ (hp.disj.symm.sep (coeff_contains _ (show i < n from hi))
      (coeff_contains _ hk')), h.g i hi]

theorem map_loop {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F) {s₀ : State}
    (hp : AccPre s₀) : WP isa (mapLoop op) s₀ (MapInv F s₀ 256) := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => wp_nil ?_)
  refine count_loop (by decide) (MapInv F s₀) (fun k hk s h => map_step hop hp hk h) ?_
  have k₂ := h₁.keep.trans h₂.keep
  have m₂ : s₂.mem = s₀.mem := by rw [h₂.mem, h₁.mem]
  refine ⟨k₂.rd, k₂.wr, k₂.sp, by rw [k₂.get .x0, Nat.mul_zero, ptr_zero],
    by rw [k₂.get .x1, Nat.mul_zero, ptr_zero], by rw [h₂.get .x9, e₁, toNat_imm]; rfl,
    by rw [e₂, toNat_imm]; rfl, fun i hi => ?_, fun i hi => by rw [m₂]⟩
  rw [m₂, ite_eq_right (Nat.not_lt_zero i)]

theorem map_correct {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F)
    {G : Poly → Poly → Poly}
    (hG : ∀ P R : Poly, ∀ i < n, ((G P R)[i]!).val = F (P[i]!).val (R[i]!).val)
    (hpres : (mapLoop op).allInstrs (keeps (RegSet.ofList preserved)) = true)
    (s : State) (hs : (accAArch64 G).pre s) :
    ∃ t s', Exec isa (mapLoop op) s t s' ∧ abiPreserved s s' ∧ (accAArch64 G).post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hp : AccPre s := ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨t, s', he, hI⟩ := map_loop (F := F) hop hp
  refine ⟨t, s', he, abi_of rfl hpres he, ?_⟩
  show PolyIs s'.mem (fP s) (G (polyAt s.mem (fP s)) (polyAt s.mem (gP s)))
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [hI.f i hi, ite_eq_left hi, newC, hG _ _ i hi, polyAt_val hp.f hi, polyAt_val hp.g hi]

theorem map_ct {op : List Instr} {G : Poly → Poly → Poly}
    (h : (Taint.check taint (Taint.ofRegs [.x0, .x1]) (mapLoop op)
      (Taint.hintOf taint (Taint.ofRegs [.x0, .x1]) (mapLoop op))).isSome = true) :
    ConstantTime isa (accAArch64 G).pre (accAArch64 G).pub (mapLoop op) := by
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
  map_correct addOp_spec (fun P R i hi => by rw [add_get _ _ hi, val_add]) (by decide +kernel)

theorem sub_correct : ∀ s, (accAArch64 Spec.MlKem.sub).pre s →
    ∃ t s', Exec isa Impl.MlKem.AArch64.sub s t s' ∧ abiPreserved s s' ∧
      (accAArch64 Spec.MlKem.sub).post s s' :=
  map_correct subOp_spec (fun P R i hi => by rw [sub_get _ _ hi, val_sub]) (by decide +kernel)

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
