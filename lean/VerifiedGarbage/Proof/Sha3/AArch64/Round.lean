import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Sha3.AArch64.Wp

/-!
# Keccak-f[1600] on AArch64: one round

Untrusted: everything here is checked by Lean. One round (`round`) from the
state at `x0` to the state at `x1`, lane by lane (`Proof.Sha3.out`), and the
swap of `x0` and `x1` after it. The same structure as the x86-64 proof
(`VG.Proof.Sha3.X86_64`).
-/

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha3 (C D B out)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## Registers -/

/-- The pointers, which a round only moves between each other. -/
def ptrRegs : List Reg := [.x0, .x1, .x2, .x3]

theorem creg_inj : ∀ x < 5, ∀ x' < 5, creg x = creg x' → x = x' := by decide
theorem dreg_inj : ∀ x < 5, ∀ x' < 5, dreg x = dreg x' → x = x' := by decide
theorem creg_dreg : ∀ x < 5, ∀ x' < 5, creg x ≠ dreg x' := by decide
theorem creg_ptr : ∀ x < 5, ∀ r ∈ ptrRegs, creg x ≠ r := by decide
theorem dreg_ptr : ∀ x < 5, ∀ r ∈ ptrRegs, dreg x ≠ r := by decide
theorem T_ptr : ∀ r ∈ ptrRegs, T ≠ r := by decide
theorem R_ptr : ∀ r ∈ ptrRegs, R ≠ r := by decide
theorem T_creg : ∀ x < 5, T ≠ creg x := by decide
theorem T_dreg : ∀ x < 5, T ≠ dreg x := by decide
theorem R_creg : ∀ x < 5, R ≠ creg x := by decide
theorem R_dreg : ∀ x < 5, R ≠ dreg x := by decide
theorem R_T : R ≠ T := by decide

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : creg x' ≠ creg x :=
  fun e => h (creg_inj x' hx' x hx e)

theorem dreg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : dreg x' ≠ dreg x :=
  fun e => h (dreg_inj x' hx' x hx e)

/-! ## Addresses -/

theorem lane_off {i : Nat} (hi : i < 25) : 8 * i % 8 = 0 ∧ 8 * i < 4096 * 8 := ⟨by omega, by omega⟩

/-! ## What a phase changes -/

/-- `s'` is `s` with at most the registers `d` and `e` changed. -/
structure Chg (s s' : State) (d e : Reg) : Prop where
  other : ∀ r, r ≠ d → r ≠ e → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- What a phase of the round keeps. -/
structure Keeps (s s' : State) : Prop where
  ptrs : ∀ r ∈ ptrRegs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.ptrs r hr).trans (h₁.ptrs r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Keeps.ofUpd {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v)
    (hd : ∀ r ∈ ptrRegs, d ≠ r) : Keeps s s' :=
  ⟨fun r hr => h.other r (hd r hr).symm, h.rd, h.wr, h.sp⟩

theorem Keeps.ofChg {s s' : State} {d e : Reg} (h : Chg s s' d e)
    (hd : ∀ r ∈ ptrRegs, d ≠ r) (he : ∀ r ∈ ptrRegs, e ≠ r) : Keeps s s' :=
  ⟨fun r hr => h.other r (hd r hr).symm (he r hr).symm, h.rd, h.wr, h.sp⟩

/-! ## θ -/

/-- `ldr T, [x0, #8k]; eor c, c, T`. -/
theorem ldx_ok {c : Reg} (hc : c ≠ T) {k : Nat} (hk : k < 25) {s : State} {src : Addr}
    {rest : List Instr} {Q : State → Prop} (h0 : s.gpr .x0 = src)
    (hin : InRegions (s.rd ++ s.wr) (laneAddr src k) 8)
    (cont : ∀ s', Chg s s' c T → s'.gpr c = s.gpr c ^^^ s.mem.readW (laneAddr src k) 64 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr .x T .x0 (8 * k) :: .logic .eor .x c c T :: rest)) s Q := by
  refine wp_ldr (lane_off hk) (by rw [h0]) hin fun s₁ u₁ => wp_eor fun s₂ u₂ => cont s₂ ?_ ?_
  · exact ⟨fun r h h' => by rw [u₂.other r h, u₁.other r h'], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  · rw [u₂.gpr, u₁.other _ hc, u₁.gpr]

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (src : Addr) (A : KState)
    (hx0 : s.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr src i) 8)
    (hA : Lanes s.mem src A) :
    WP isa (.block (column x)) s fun s' => s'.gpr (creg x) = C A x ∧ Chg s s' (creg x) T := by
  have hc : creg x ≠ T := (T_creg x hx).symm
  have c0 : creg x ≠ .x0 := creg_ptr x hx .x0 (by decide)
  have T0 : T ≠ .x0 := T_ptr .x0 (by decide)
  have hv : ∀ k (hk : k < 25), s.mem.readW (laneAddr src k) 64 = A[k]! := fun k hk => by
    rw [hA k hk]; simp [hk]
  unfold column
  refine wp_ldr (lane_off (by omega : x < 25)) (by rw [hx0]) (hin x (by omega)) fun s₁ u₁ => ?_
  have e₁ : ∀ t : State, Chg s₁ t (creg x) T → Chg s t (creg x) T ∧ t.gpr .x0 = src ∧
      InRegions (t.rd ++ t.wr) = InRegions (s.rd ++ s.wr) ∧ t.mem = s.mem := fun t h =>
    ⟨⟨fun r h' h'' => by rw [h.other r h' h'', u₁.other r h'], by rw [h.mem, u₁.mem],
      by rw [h.rd, u₁.rd], by rw [h.wr, u₁.wr], by rw [h.sp, u₁.sp]⟩,
      by rw [h.other _ (Ne.symm c0) (Ne.symm T0), u₁.other _ (Ne.symm c0), hx0],
      by rw [h.rd, h.wr, u₁.rd, u₁.wr], by rw [h.mem, u₁.mem]⟩
  have c₁ : Chg s₁ s₁ (creg x) T := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨-, a₁, i₁, m₁⟩ := e₁ s₁ c₁
  refine ldx_ok hc (k := x + 5) (by omega) a₁ (by rw [i₁]; exact hin _ (by omega)) fun s₂ h₂ v₂ => ?_
  have c₂ : Chg s₁ s₂ (creg x) T := h₂
  obtain ⟨-, a₂, i₂, m₂⟩ := e₁ s₂ c₂
  refine ldx_ok hc (k := x + 10) (by omega) a₂ (by rw [i₂]; exact hin _ (by omega)) fun s₃ h₃ v₃ => ?_
  have c₃ : Chg s₁ s₃ (creg x) T :=
    ⟨fun r h h' => by rw [h₃.other r h h', h₂.other r h h'], by rw [h₃.mem, h₂.mem],
      by rw [h₃.rd, h₂.rd], by rw [h₃.wr, h₂.wr], by rw [h₃.sp, h₂.sp]⟩
  obtain ⟨-, a₃, i₃, m₃⟩ := e₁ s₃ c₃
  refine ldx_ok hc (k := x + 15) (by omega) a₃ (by rw [i₃]; exact hin _ (by omega)) fun s₄ h₄ v₄ => ?_
  have c₄ : Chg s₁ s₄ (creg x) T :=
    ⟨fun r h h' => by rw [h₄.other r h h', c₃.other r h h'], by rw [h₄.mem, c₃.mem],
      by rw [h₄.rd, c₃.rd], by rw [h₄.wr, c₃.wr], by rw [h₄.sp, c₃.sp]⟩
  obtain ⟨-, a₄, i₄, m₄⟩ := e₁ s₄ c₄
  refine ldx_ok hc (k := x + 20) (by omega) a₄ (by rw [i₄]; exact hin _ (by omega)) fun s₅ h₅ v₅ => wp_nil ?_
  have c₅ : Chg s₁ s₅ (creg x) T :=
    ⟨fun r h h' => by rw [h₅.other r h h', c₄.other r h h'], by rw [h₅.mem, c₄.mem],
      by rw [h₅.rd, c₄.rd], by rw [h₅.wr, c₄.wr], by rw [h₅.sp, c₄.sp]⟩
  refine ⟨?_, (e₁ s₅ c₅).1⟩
  rw [v₅, v₄, v₃, v₂, u₁.gpr]
  simp only [m₄, m₃, m₂, m₁]
  rw [hv x (by omega), hv _ (by omega),
    hv _ (by omega), hv _ (by omega), hv _ (by omega)]
  rfl

/-- After the first `k` columns. -/
def ColInv (s₀ : State) (A : KState) (k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ ∀ x < k, s.gpr (creg x) = C A x

theorem columns_ok (s₀ : State) (src : Addr) (A : KState)
    (hx0 : s₀.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr src i) 8)
    (hA : Lanes s₀.mem src A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ A) (fun x s hx ⟨hk, hm, hc⟩ => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, rfl, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx s src A ((hk.ptrs .x0 (by decide)).trans hx0)
    (by rw [hk.rd, hk.wr]; exact hin) (by rw [hm]; exact hA)) fun s' ⟨hv, h⟩ => ?_
  refine ⟨hk.trans (Keeps.ofChg h (creg_ptr x hx) T_ptr), h.mem.trans hm, fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact hv
  · rw [h.other _ (creg_ne hx (by omega) e) (T_creg x' (by omega)).symm, hc x' (by omega)]

/-! ## D -/

theorem dcol_ok (x : Nat) (hx : x < 5) (s : State) (A : KState)
    (hc : ∀ x' < 5, s.gpr (creg x') = C A x') :
    WP isa (.block (dcol x)) s fun s' => Upd s s' (dreg x) (D A x) := by
  unfold dcol
  refine wp_ror (by decide) fun s₁ h₁ => wp_eor fun s₂ h₂ => wp_nil ?_
  have u := h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr, h₂.sp⟩
  refine ⟨?_, u.other, u.mem, u.rd, u.wr, u.sp⟩
  rw [h₂.gpr, h₁.gpr, h₁.other _ (creg_dreg _ (Nat.mod_lt _ (by omega)) x hx),
    hc _ (Nat.mod_lt _ (by omega)), hc _ (Nat.mod_lt _ (by omega))]
  rfl

/-- After the first `k` of the `D[x]`. -/
def DInv (s₀ : State) (A : KState) (k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ (∀ x < 5, s.gpr (creg x) = C A x) ∧ ∀ x < k, s.gpr (dreg x) = D A x

theorem dcols_ok (s₀ : State) (A : KState) (hc : ∀ x < 5, s₀.gpr (creg x) = C A x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ A) (fun x s hx ⟨hk, hm, hcs, hd⟩ => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, rfl, hc, fun _ h => absurd h (by omega)⟩
  refine WP.mono (dcol_ok x hx s A hcs) fun s' h => ?_
  refine ⟨hk.trans (Keeps.ofUpd h (dreg_ptr x hx)), h.mem.trans hm, fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [h.other _ (creg_dreg x' hx' x hx), hcs x' hx']
  · by_cases e : x' = x
    · subst e; exact h.gpr
    · rw [h.other _ (dreg_ne hx (by omega) e), hd x' (by omega)]

/-! ## A plane -/

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) (s : State) (src : Addr) (A : KState)
    (hx0 : s.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr src i) 8)
    (hA : ∀ i < 25, s.mem.readW (laneAddr src i) 64 = A[i]!)
    (hd : ∀ x' < 5, s.gpr (dreg x') = D A x') :
    WP isa (.block (laneB x y)) s fun s' => Upd s s' (creg x) (B A x y) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold laneB
  rw [List.cons_append, List.cons_append]
  refine wp_ldr (lane_off hj) (by rw [hx0]) (hin _ hj) fun s₁ h₁ => wp_eor fun s₂ h₂ => ?_
  have u := h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr, h₂.sp⟩
  have hv : s₂.gpr (creg x) = A[piSrc x y]! ^^^ D A ((x + 3 * y) % 5) := by
    rw [h₂.gpr, h₁.gpr, hA _ hj, h₁.other _ (creg_dreg x hx _ hk).symm, hd _ hk]
  unfold B Proof.Sha3.rotl
  split
  · exact wp_nil ⟨by rw [hv], u.other, u.mem, u.rd, u.wr, u.sp⟩
  · have := Proof.Sha3.rhoOff_lt _ hj
    refine wp_ror (by omega) fun s₃ h₃ => wp_nil ?_
    refine ⟨by rw [h₃.gpr, hv], (u.trans ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr, h₃.sp⟩).other,
      by rw [h₃.mem, u.mem], by rw [h₃.rd, u.rd], by rw [h₃.wr, u.wr], by rw [h₃.sp, u.sp]⟩

/-- After the first `k` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (A : KState) (y k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ (∀ x < 5, s.gpr (dreg x) = D A x) ∧
    ∀ x < k, s.gpr (creg x) = B A x y

theorem laneBs_ok (y : Nat) (_hy : y < 5) (s₀ : State) (src : Addr) (A : KState)
    (hx0 : s₀.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr src i) 8)
    (hA : ∀ i < 25, s₀.mem.readW (laneAddr src i) 64 = A[i]!)
    (hd : ∀ x < 5, s₀.gpr (dreg x) = D A x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB x y)) s₀ (BInv s₀ A y 5) := by
  refine wp_range_flatMap (M := isa) (BInv s₀ A y) (fun x s hx ⟨hk, hm, hds, hb⟩ => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, rfl, hd, fun _ h => absurd h (by omega)⟩
  refine WP.mono (laneB_ok x y hx _hy s src A ((hk.ptrs .x0 (by decide)).trans hx0)
    (by rw [hk.rd, hk.wr]; exact hin) (by rw [hm]; exact hA) hds) fun s' h => ?_
  refine ⟨hk.trans (Keeps.ofUpd h (creg_ptr x hx)), h.mem.trans hm, fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [h.other _ (creg_dreg x hx x' hx').symm, hds x' hx']
  · by_cases e : x' = x
    · subst e; exact h.gpr
    · rw [h.other _ (creg_ne hx (by omega) e), hb x' (by omega)]

/-- `¬b ∧ c`, as the model computes it without `bic`. -/
theorem andNot (b c : Lane) : (b ^^^ 0xffffffffffffffff) &&& c = (b &&& c) ^^^ c := by
  have e : (0xffffffffffffffff : Lane) = BitVec.allOnes 64 := by decide
  rw [e]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_allOnes]
  cases b[i] <;> cases c[i] <;> rfl

/-- What `chi` leaves: `T` and `R` changed, and lane `(x, y)` of the output
stored. -/
structure ChiPost (s s' : State) (a : Addr) (v : Lane) : Prop where
  other : ∀ r, r ≠ T → r ≠ R → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem.writeW a v

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) (s : State) (dst rcp : Addr) (A : KState)
    (rc : Lane) (hx1 : s.gpr .x1 = dst) (hx2 : s.gpr .x2 = rcp)
    (hout : InRegions s.wr (laneAddr dst (x + 5 * y)) 8) (hrc_in : InRegions (s.rd ++ s.wr) rcp 8)
    (hrc : s.mem.readW rcp 64 = rc) (hb : ∀ x' < 5, s.gpr (creg x') = B A x' y) :
    WP isa (.block (chi x y)) s fun s' => ChiPost s s' (laneAddr dst (x + 5 * y)) (out A rc x y) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have hj : x + 5 * y < 25 := by omega
  unfold chi
  simp only [List.cons_append]
  refine wp_and fun s₁ h₁ => wp_eor fun s₂ h₂ => wp_eor fun s₃ h₃ => ?_
  have u := (h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr, h₂.sp⟩).trans
    ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr, h₃.sp⟩
  have ht : s₃.gpr T = (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^
      B A x y := by
    rw [h₃.gpr, h₂.gpr, h₁.gpr, h₂.other _ (T_creg _ hx).symm, h₁.other _ (T_creg _ hx).symm,
      h₁.other _ (T_creg _ h2).symm, hb _ h1, hb _ h2, hb _ hx, andNot]
  have fin : ∀ s₄ : State, (∀ r, r ≠ T → r ≠ R → s₄.gpr r = s.gpr r) → s₄.gpr T = out A rc x y →
      s₄.mem = s.mem → s₄.rd = s.rd → s₄.wr = s.wr → s₄.sp = s.sp →
      WP isa (.block [.str .x T .x1 (8 * (x + 5 * y))]) s₄ fun s' =>
        ChiPost s s' (laneAddr dst (x + 5 * y)) (out A rc x y) := fun s₄ g₄ v₄ m₄ r₄ w₄ p₄ => by
    refine wp_str (lane_off hj) (by rw [g₄ _ (T_ptr .x1 (by decide)).symm (R_ptr .x1 (by decide)).symm, hx1])
      (by rw [w₄]; exact hout) fun s₅ g₅ => wp_nil ?_
    exact ⟨fun r h h' => by rw [g₅.gpr, g₄ r h h'], by rw [g₅.rd, r₄], by rw [g₅.wr, w₄],
      by rw [g₅.sp, p₄], by rw [g₅.mem, m₄, v₄]⟩
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [and_self, ite_true, List.cons_append, List.nil_append]
    refine wp_ldr (a := rcp) ⟨by decide, by decide⟩
      (by rw [u.other _ (T_ptr .x2 (by decide)).symm, hx2]; exact add_zero' _)
      (by rw [u.rd, u.wr]; exact hrc_in) fun s₄ h₄ => wp_eor fun s₅ h₅ => ?_
    refine fin s₅ (fun r h h' => by rw [h₅.other r h, h₄.other r h', u.other r h]) ?_
      (by rw [h₅.mem, h₄.mem, u.mem]) (by rw [h₅.rd, h₄.rd, u.rd]) (by rw [h₅.wr, h₄.wr, u.wr])
      (by rw [h₅.sp, h₄.sp, u.sp])
    rw [h₅.gpr, h₄.other _ (Ne.symm R_T), h₄.gpr, ht, u.mem, hrc, out]
    simp only [and_self, ite_true]
  · simp only [h0, ite_false, List.nil_append]
    refine fin s₃ (fun r h _ => u.other r h) ?_ u.mem u.rd u.wr u.sp
    rw [ht, out]
    simp only [h0, ite_false]

/-- After `k` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (A : KState) (rc : Lane) (dst : Addr) (y k : Nat) (s : State) : Prop where
  keeps : Keeps s₀ s
  frame : Frame [⟨dst, 200⟩] s₀.mem s.mem
  dregs : ∀ x < 5, s.gpr (dreg x) = D A x
  bregs : ∀ x < 5, s.gpr (creg x) = B A x y
  lanes : ∀ j < 5 * y + k, s.mem.readW (laneAddr dst j) 64 = out A rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) (s₀ : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s₀.rd s₀.wr src dst rcp) (hx1 : s₀.gpr .x1 = dst) (hx2 : s₀.gpr .x2 = rcp)
    (hrc : s₀.mem.readW rcp 64 = rc) (s : State) (hs : ChiInv s₀ A rc dst y 0 s) :
    WP isa (.block ((List.range 5).flatMap fun x => chi x y)) s (ChiInv s₀ A rc dst y 5) := by
  refine wp_range_flatMap (M := isa) (ChiInv s₀ A rc dst y) (fun x s hx hi => ?_) 5 le_rfl s hs
  have hj : x + 5 * y < 25 := by omega
  refine WP.mono (chi_ok x y hx hy s dst rcp A rc ((hi.keeps.ptrs .x1 (by decide)).trans hx1)
    ((hi.keeps.ptrs .x2 (by decide)).trans hx2) (by rw [hi.keeps.wr]; exact he.dst_out _ hj)
    (by rw [hi.keeps.rd, hi.keeps.wr]; exact he.rc_in) (by rw [he.rc_frame hi.frame, hrc]) hi.bregs)
    fun s' hc => ?_
  refine ⟨⟨fun r hr => by rw [hc.other r (T_ptr r hr).symm (R_ptr r hr).symm, hi.keeps.ptrs r hr],
      hc.rd.trans hi.keeps.rd, hc.wr.trans hi.keeps.wr, hc.sp.trans hi.keeps.sp⟩, ?_,
    fun x' hx' => by rw [hc.other _ (T_dreg x' hx').symm (R_dreg x' hx').symm, hi.dregs x' hx'],
    fun x' hx' => by rw [hc.other _ (T_creg x' hx').symm (R_creg x' hx').symm, hi.bregs x' hx'],
    fun j hj' => ?_⟩
  · rw [hc.mem]; exact hi.frame.writeW (List.mem_singleton_self _) _ (lane_contains dst hj)
  · rw [hc.mem]
    by_cases e : j = x + 5 * y
    · subst e
      rw [Mem.readW_writeW_self64, show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega]
    · rw [Mem.readW_writeW_sep (lane_sep dst (by omega) hj e) (by decide)]
      exact hi.lanes j (by omega)

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (A : KState) (rc : Lane) (dst : Addr) (y : Nat) (s : State) : Prop where
  keeps : Keeps s₀ s
  frame : Frame [⟨dst, 200⟩] s₀.mem s.mem
  dregs : ∀ x < 5, s.gpr (dreg x) = D A x
  lanes : ∀ j < 5 * y, s.mem.readW (laneAddr dst j) 64 = out A rc (j % 5) (j / 5)

theorem planes_ok (s₀ : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s₀.rd s₀.wr src dst rcp) (hx0 : s₀.gpr .x0 = src) (hx1 : s₀.gpr .x1 = dst)
    (hx2 : s₀.gpr .x2 = rcp) (hA : Lanes s₀.mem src A) (hrc : s₀.mem.readW rcp 64 = rc)
    (hd : ∀ x < 5, s₀.gpr (dreg x) = D A x) :
    WP isa (.block ((List.range 5).flatMap plane)) s₀ (PInv s₀ A rc dst 5) := by
  refine wp_range_flatMap (M := isa) (PInv s₀ A rc dst) (fun y s hy hi => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, Frame.refl _ _, hd, fun _ h => absurd h (by omega)⟩
  unfold plane
  rw [WP.block_append_iff]
  have hA' : ∀ i < 25, s.mem.readW (laneAddr src i) 64 = A[i]! := fun i hi' => by
    rw [he.src_frame hi.frame hi', hA i hi']; simp [hi']
  refine WP.mono (laneBs_ok y hy s src A ((hi.keeps.ptrs .x0 (by decide)).trans hx0)
    (by rw [hi.keeps.rd, hi.keeps.wr]; exact he.src_in) hA' hi.dregs) fun s₁ ⟨hk, hm, hds, hb⟩ => ?_
  refine WP.mono (chis_ok y hy s₀ src dst rcp A rc he hx1 hx2 hrc s₁
    ⟨hi.keeps.trans hk, by rw [hm]; exact hi.frame, hds, hb, fun j hj => by rw [hm]; exact hi.lanes j hj⟩)
    fun s₂ h₂ => ⟨h₂.keeps, h₂.frame, h₂.dregs, fun j hj => h₂.lanes j (by omega)⟩

/-! ## The round -/

theorem tail_ok (s : State) :
    WP isa (.block [mov T .x0, mov .x0 .x1, mov .x1 T, .addImm .x .x2 .x2 8, .sub .x T .x2 .x3]) s
      fun s' =>
      s'.gpr .x0 = s.gpr .x1 ∧ s'.gpr .x1 = s.gpr .x0 ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 ∧
      s'.gpr .x3 = s.gpr .x3 ∧ s'.gpr T = s.gpr .x2 + BitVec.ofNat 64 8 - s.gpr .x3 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine wp_mov fun s₁ h₁ => wp_mov fun s₂ h₂ => wp_mov fun s₃ h₃ => wp_addImm (by decide)
    fun s₄ h₄ => wp_sub fun s₅ h₅ => wp_nil ?_
  have x2 : s₄.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 := by
    rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  have x3 : s₄.gpr .x3 = s.gpr .x3 := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  refine ⟨?_, ?_, by rw [h₅.other _ (by decide), x2], by rw [h₅.other _ (by decide), x3],
    by rw [h₅.gpr, x2, x3], by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr,
      h₁.other _ (by decide)]
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.gpr]

theorem round_ok (s : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s.rd s.wr src dst rcp) (hx0 : s.gpr .x0 = src) (hx1 : s.gpr .x1 = dst)
    (hx2 : s.gpr .x2 = rcp) (hA : Lanes s.mem src A) (hrc : s.mem.readW rcp 64 = rc) :
    WP isa (.block round) s fun s' =>
      Lanes s'.mem dst (outState A rc) ∧ Frame [⟨dst, 200⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .x0 = dst ∧ s'.gpr .x1 = src ∧
      s'.gpr .x2 = rcp + BitVec.ofNat 64 8 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      s'.gpr T = rcp + BitVec.ofNat 64 8 - s.gpr .x3 := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (columns_ok s src A hx0 he.src_in hA) fun s₁ ⟨k₁, m₁, c₁⟩ => ?_
  refine WP.mono (dcols_ok s₁ A c₁) fun s₂ ⟨k₂, m₂, _, d₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  refine WP.mono (planes_ok s₂ src dst rcp A rc (by rw [k₁₂.rd, k₁₂.wr]; exact he)
    ((k₁₂.ptrs .x0 (by decide)).trans hx0) ((k₁₂.ptrs .x1 (by decide)).trans hx1)
    ((k₁₂.ptrs .x2 (by decide)).trans hx2) (by rw [m₂, m₁]; exact hA) (by rw [m₂, m₁, hrc]) d₂)
    fun s₃ h₃ => ?_
  have k₃ := k₁₂.trans h₃.keeps
  refine WP.mono (tail_ok s₃) fun s₄ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ => ?_
  have hdx : s₃.gpr .x2 = rcp := (k₃.ptrs .x2 (by decide)).trans hx2
  have hcx : s₃.gpr .x3 = s.gpr .x3 := k₃.ptrs .x3 (by decide)
  refine ⟨fun i hi => ?_, by rw [e₆, ← m₁, ← m₂]; exact h₃.frame, by rw [e₇, k₃.rd],
    by rw [e₈, k₃.wr], by rw [e₉, k₃.sp], by rw [e₁, k₃.ptrs .x1 (by decide), hx1],
    by rw [e₂, k₃.ptrs .x0 (by decide), hx0], by rw [e₃, hdx], by rw [e₄, hcx],
    by rw [e₅, hdx, hcx]⟩
  rw [e₆, h₃.lanes i (by omega)]
  simp [outState]

end VG.Proof.Sha3.AArch64
