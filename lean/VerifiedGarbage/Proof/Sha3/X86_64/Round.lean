import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Sha3.X86_64.Wp
import VerifiedGarbage.Impl.Sha3.X86_64

/-!
# Keccak-f[1600] on x86-64: one round

Untrusted: everything here is checked by Lean. One round (`round`) from the
state at `rdi` to the state at `rsi`, lane by lane (`Proof.Sha3.out`), and
the swap of `rdi` and `rsi` after it.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Proof.Sha3 (C D B out)
open VG.Impl.Sha3 (piSrc)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## Registers -/

/-- The pointers, which a round only moves between each other. -/
def ptrRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem creg_inj : ∀ x < 5, ∀ x' < 5, creg x = creg x' → x = x' := by decide
theorem dreg_inj : ∀ x < 5, ∀ x' < 5, dreg x = dreg x' → x = x' := by decide
theorem creg_dreg : ∀ x < 5, ∀ x' < 5, creg x ≠ dreg x' := by decide
theorem creg_ptr : ∀ x < 5, ∀ r ∈ ptrRegs, creg x ≠ r := by decide
theorem dreg_ptr : ∀ x < 5, ∀ r ∈ ptrRegs, dreg x ≠ r := by decide
theorem T_ptr : ∀ r ∈ ptrRegs, T ≠ r := by decide
theorem T_creg : ∀ x < 5, T ≠ creg x := by decide
theorem T_dreg : ∀ x < 5, T ≠ dreg x := by decide

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : creg x' ≠ creg x :=
  fun e => h (creg_inj x' hx' x hx e)

theorem dreg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : dreg x' ≠ dreg x :=
  fun e => h (dreg_inj x' hx' x hx e)

/-! ## Addresses -/

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]; rw [ofInt_natCast]

theorem ea_lane (s : State) (b : Reg) (i : Nat) :
    s.ea (lane b i) = s.gpr b + BitVec.ofNat 64 (8 * i) := ea_at s b (8 * i)

/-! ## θ -/

/-- What a phase of the round keeps. -/
structure Keeps (s s' : State) : Prop where
  ptrs : ∀ r ∈ ptrRegs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.ptrs r hr).trans (h₁.ptrs r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Keeps.ofUpd {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v)
    (hd : ∀ r ∈ ptrRegs, d ≠ r) : Keeps s s' :=
  ⟨fun r hr => h.other r (hd r hr).symm, h.rd, h.wr⟩

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (src : Addr) (A : KState)
    (hrdi : s.gpr .rdi = src) (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr src i) 8)
    (hA : Lanes s.mem src A) :
    WP isa (.block (column x)) s fun s' => Upd s s' (creg x) (C A x) := by
  have hr : ∀ s' : State, Upd s s' (creg x) (s'.gpr (creg x)) → s'.gpr .rdi = src ∧
      InRegions (s'.rd ++ s'.wr) = InRegions (s.rd ++ s.wr) ∧ s'.mem = s.mem := fun s' h =>
    ⟨(h.other _ (creg_ptr x hx .rdi (by decide)).symm).trans hrdi, by rw [h.rd, h.wr], h.mem⟩
  have ld : ∀ (s' : State) (k : Nat), k < 25 → Upd s s' (creg x) (s'.gpr (creg x)) →
      s'.ea (lane .rdi k) = laneAddr src k ∧ InRegions (s'.rd ++ s'.wr) (laneAddr src k) 8 ∧
      s'.mem.readW (laneAddr src k) 64 = A[k]! := fun s' k hk h => by
    obtain ⟨e₁, e₂, e₃⟩ := hr s' h
    refine ⟨by rw [ea_lane, e₁], by rw [e₂]; exact hin k hk, by rw [e₃, hA k hk]; simp [hk]⟩
  have u₀ : Upd s s (creg x) (s.gpr (creg x)) := ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  unfold column
  obtain ⟨a₀, i₀, v₀⟩ := ld s x (by omega) u₀
  refine wp_movm a₀ i₀ fun s₁ h₁ => ?_
  have u₁ : Upd s s₁ (creg x) (s₁.gpr (creg x)) := ⟨rfl, h₁.other, h₁.mem, h₁.rd, h₁.wr⟩
  obtain ⟨a₁, i₁, v₁⟩ := ld s₁ (x + 5) (by omega) u₁
  refine wp_xorm a₁ i₁ fun s₂ h₂ => ?_
  have u₂ := u₁.trans ⟨rfl, h₂.other, h₂.mem, h₂.rd, h₂.wr⟩
  obtain ⟨a₂, i₂, v₂⟩ := ld s₂ (x + 10) (by omega) u₂
  refine wp_xorm a₂ i₂ fun s₃ h₃ => ?_
  have u₃ := u₂.trans ⟨rfl, h₃.other, h₃.mem, h₃.rd, h₃.wr⟩
  obtain ⟨a₃, i₃, v₃⟩ := ld s₃ (x + 15) (by omega) u₃
  refine wp_xorm a₃ i₃ fun s₄ h₄ => ?_
  have u₄ := u₃.trans ⟨rfl, h₄.other, h₄.mem, h₄.rd, h₄.wr⟩
  obtain ⟨a₄, i₄, v₄⟩ := ld s₄ (x + 20) (by omega) u₄
  refine wp_xorm a₄ i₄ fun s₅ h₅ => wp_nil ?_
  refine ⟨?_, (u₄.trans ⟨rfl, h₅.other, h₅.mem, h₅.rd, h₅.wr⟩).other, by rw [h₅.mem, u₄.mem],
    by rw [h₅.rd, u₄.rd], by rw [h₅.wr, u₄.wr]⟩
  rw [h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, v₀, v₁, v₂, v₃, v₄]
  rfl

/-- After the first `k` columns. -/
def ColInv (s₀ : State) (A : KState) (k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ ∀ x < k, s.gpr (creg x) = C A x

theorem columns_ok (s₀ : State) (src : Addr) (A : KState)
    (hrdi : s₀.gpr .rdi = src) (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr src i) 8)
    (hA : Lanes s₀.mem src A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ A) (fun x s hx ⟨hk, hm, hc⟩ => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, rfl, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx s src A ((hk.ptrs .rdi (by decide)).trans hrdi)
    (by rw [hk.rd, hk.wr]; exact hin) (by rw [hm]; exact hA)) fun s' h => ?_
  refine ⟨hk.trans (Keeps.ofUpd h (creg_ptr x hx)), h.mem.trans hm, fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact h.gpr
  · rw [h.other _ (creg_ne hx (by omega) e), hc x' (by omega)]

/-! ## D -/

theorem dcol_ok (x : Nat) (hx : x < 5) (s : State) (A : KState)
    (hc : ∀ x' < 5, s.gpr (creg x') = C A x') :
    WP isa (.block (dcol x)) s fun s' => Upd s s' (dreg x) (D A x) := by
  unfold dcol
  refine wp_mov fun s₁ h₁ => wp_ror (by decide) (by decide) fun s₂ h₂ => wp_xor fun s₃ h₃ => wp_nil ?_
  have u := (h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr⟩).trans
    ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr⟩
  refine ⟨?_, u.other, u.mem, u.rd, u.wr⟩
  rw [h₃.gpr, h₂.gpr, h₁.gpr, h₂.other _ (creg_dreg _ (Nat.mod_lt _ (by omega)) x hx),
    h₁.other _ (creg_dreg _ (Nat.mod_lt _ (by omega)) x hx), hc _ (Nat.mod_lt _ (by omega)),
    hc _ (Nat.mod_lt _ (by omega))]
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
    (hrdi : s.gpr .rdi = src) (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr src i) 8)
    (hA : ∀ i < 25, s.mem.readW (laneAddr src i) 64 = A[i]!)
    (hd : ∀ x' < 5, s.gpr (dreg x') = D A x') :
    WP isa (.block (laneB x y)) s fun s' => Upd s s' (creg x) (B A x y) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold laneB
  rw [List.cons_append, List.cons_append]
  refine wp_movm (by rw [ea_lane, hrdi]) (hin _ hj) fun s₁ h₁ => wp_xor fun s₂ h₂ => ?_
  have u := h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr⟩
  have hv : s₂.gpr (creg x) = A[piSrc x y]! ^^^ D A ((x + 3 * y) % 5) := by
    rw [h₂.gpr, h₁.gpr, hA _ hj, h₁.other _ (creg_dreg x hx _ hk).symm, hd _ hk]
  unfold B Proof.Sha3.rotl
  split
  · exact wp_nil ⟨by rw [hv], u.other, u.mem, u.rd, u.wr⟩
  · have := Proof.Sha3.rhoOff_lt _ hj
    refine wp_ror (by omega) (by omega) fun s₃ h₃ => wp_nil ?_
    refine ⟨by rw [h₃.gpr, hv], (u.trans ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr⟩).other,
      by rw [h₃.mem, u.mem], by rw [h₃.rd, u.rd], by rw [h₃.wr, u.wr]⟩

/-- After the first `k` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (A : KState) (y k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ (∀ x < 5, s.gpr (dreg x) = D A x) ∧
    ∀ x < k, s.gpr (creg x) = B A x y

theorem laneBs_ok (y : Nat) (_hy : y < 5) (s₀ : State) (src : Addr) (A : KState)
    (hrdi : s₀.gpr .rdi = src) (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr src i) 8)
    (hA : ∀ i < 25, s₀.mem.readW (laneAddr src i) 64 = A[i]!)
    (hd : ∀ x < 5, s₀.gpr (dreg x) = D A x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB x y)) s₀ (BInv s₀ A y 5) := by
  refine wp_range_flatMap (M := isa) (BInv s₀ A y) (fun x s hx ⟨hk, hm, hds, hb⟩ => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, rfl, hd, fun _ h => absurd h (by omega)⟩
  refine WP.mono (laneB_ok x y hx _hy s src A ((hk.ptrs .rdi (by decide)).trans hrdi)
    (by rw [hk.rd, hk.wr]; exact hin) (by rw [hm]; exact hA) hds) fun s' h => ?_
  refine ⟨hk.trans (Keeps.ofUpd h (creg_ptr x hx)), h.mem.trans hm, fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [h.other _ (creg_dreg x hx x' hx').symm, hds x' hx']
  · by_cases e : x' = x
    · subst e; exact h.gpr
    · rw [h.other _ (creg_ne hx (by omega) e), hb x' (by omega)]

theorem allOnes : BitVec.signExtend 64 (0xffffffff : BitVec 32) = (0xffffffffffffffff : BitVec 64) := by
  decide

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) (s : State) (dst rcp : Addr) (A : KState)
    (rc : Lane) (hrsi : s.gpr .rsi = dst) (hrdx : s.gpr .rdx = rcp)
    (hout : InRegions s.wr (laneAddr dst (x + 5 * y)) 8) (hrc_in : InRegions (s.rd ++ s.wr) rcp 8)
    (hrc : s.mem.readW rcp 64 = rc) (hb : ∀ x' < 5, s.gpr (creg x') = B A x' y) :
    WP isa (.block (chi x y)) s fun s' =>
      (∀ r, r ≠ T → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (laneAddr dst (x + 5 * y)) (out A rc x y) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold chi
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ h₁ => wp_xori fun s₂ h₂ => wp_and fun s₃ h₃ => wp_xor fun s₄ h₄ => ?_
  have u := ((h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr⟩).trans
    ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr⟩).trans ⟨h₄.gpr, h₄.other, h₄.mem, h₄.rd, h₄.wr⟩
  have ht : s₄.gpr T = (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^
      B A x y := by
    rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, h₃.other _ (T_creg _ hx).symm,
      h₂.other _ (T_creg _ hx).symm, h₁.other _ (T_creg _ hx).symm, h₂.other _ (T_creg _ h2).symm,
      h₁.other _ (T_creg _ h2).symm, hb _ h1, hb _ h2, hb _ hx, allOnes]
  have hsi : s₄.gpr .rsi = dst := (u.other _ (T_ptr .rsi (by decide)).symm).trans hrsi
  have hdx : s₄.gpr .rdx = rcp := (u.other _ (T_ptr .rdx (by decide)).symm).trans hrdx
  have fin : ∀ s₅ : State, Upd s s₅ T (out A rc x y) →
      WP isa (.block [.store (lane .rsi (x + 5 * y)) T]) s₅ fun s' =>
        (∀ r, r ≠ T → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem.writeW (laneAddr dst (x + 5 * y)) (out A rc x y) := fun s₅ h₅ => by
    refine wp_store (by rw [ea_lane, h₅.other _ (T_ptr .rsi (by decide)).symm, hrsi])
      (by rw [h₅.wr]; exact hout) fun s₆ g₆ m₆ r₆ w₆ => wp_nil ?_
    exact ⟨fun r hr => by rw [g₆, h₅.other r hr], by rw [r₆, h₅.rd], by rw [w₆, h₅.wr],
      by rw [m₆, h₅.mem, h₅.gpr]⟩
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [and_self, ite_true, List.singleton_append]
    refine wp_xorm (a := rcp) (by rw [ea_at, hdx]; exact BitVec.add_zero _)
      (by rw [u.rd, u.wr]; exact hrc_in) fun s₅ h₅ => ?_
    refine fin s₅ (u.trans ⟨?_, h₅.other, h₅.mem, h₅.rd, h₅.wr⟩)
    rw [h₅.gpr, ht, u.mem, hrc, out]
    simp only [and_self, ite_true]
  · simp only [h0, ite_false, List.nil_append]
    refine fin s₄ (u.trans ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
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
    (he : Env s₀.rd s₀.wr src dst rcp) (hrsi : s₀.gpr .rsi = dst) (hrdx : s₀.gpr .rdx = rcp)
    (hrc : s₀.mem.readW rcp 64 = rc) (s : State) (hs : ChiInv s₀ A rc dst y 0 s) :
    WP isa (.block ((List.range 5).flatMap fun x => chi x y)) s (ChiInv s₀ A rc dst y 5) := by
  refine wp_range_flatMap (M := isa) (ChiInv s₀ A rc dst y) (fun x s hx hi => ?_) 5 le_rfl s hs
  have hj : x + 5 * y < 25 := by omega
  refine WP.mono (chi_ok x y hx hy s dst rcp A rc ((hi.keeps.ptrs .rsi (by decide)).trans hrsi)
    ((hi.keeps.ptrs .rdx (by decide)).trans hrdx) (by rw [hi.keeps.wr]; exact he.dst_out _ hj)
    (by rw [hi.keeps.rd, hi.keeps.wr]; exact he.rc_in) (by rw [he.rc_frame hi.frame, hrc]) hi.bregs)
    fun s' ⟨hg, hrd, hwr, hm⟩ => ?_
  refine ⟨⟨fun r hr => by rw [hg r (T_ptr r hr).symm, hi.keeps.ptrs r hr], hrd.trans hi.keeps.rd,
      hwr.trans hi.keeps.wr⟩, ?_, fun x' hx' => by rw [hg _ (T_dreg x' hx').symm, hi.dregs x' hx'],
    fun x' hx' => by rw [hg _ (T_creg x' hx').symm, hi.bregs x' hx'], fun j hj' => ?_⟩
  · rw [hm]; exact hi.frame.writeW (List.mem_singleton_self _) _ (lane_contains dst hj)
  · rw [hm]
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
    (he : Env s₀.rd s₀.wr src dst rcp) (hrdi : s₀.gpr .rdi = src) (hrsi : s₀.gpr .rsi = dst)
    (hrdx : s₀.gpr .rdx = rcp) (hA : Lanes s₀.mem src A) (hrc : s₀.mem.readW rcp 64 = rc)
    (hd : ∀ x < 5, s₀.gpr (dreg x) = D A x) :
    WP isa (.block ((List.range 5).flatMap plane)) s₀ (PInv s₀ A rc dst 5) := by
  refine wp_range_flatMap (M := isa) (PInv s₀ A rc dst) (fun y s hy hi => ?_) 5 le_rfl s₀
    ⟨Keeps.refl _, Frame.refl _ _, hd, fun _ h => absurd h (by omega)⟩
  unfold plane
  rw [WP.block_append_iff]
  have hA' : ∀ i < 25, s.mem.readW (laneAddr src i) 64 = A[i]! := fun i hi' => by
    rw [he.src_frame hi.frame hi', hA i hi']; simp [hi']
  refine WP.mono (laneBs_ok y hy s src A ((hi.keeps.ptrs .rdi (by decide)).trans hrdi)
    (by rw [hi.keeps.rd, hi.keeps.wr]; exact he.src_in) hA' hi.dregs) fun s₁ ⟨hk, hm, hds, hb⟩ => ?_
  refine WP.mono (chis_ok y hy s₀ src dst rcp A rc he hrsi hrdx hrc s₁
    ⟨hi.keeps.trans hk, by rw [hm]; exact hi.frame, hds, hb, fun j hj => by rw [hm]; exact hi.lanes j hj⟩)
    fun s₂ h₂ => ⟨h₂.keeps, h₂.frame, h₂.dregs, fun j hj => h₂.lanes j (by omega)⟩

/-! ## The round -/

theorem tail_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rax),
      .alu .add .rdx (.imm 8), .alu .cmp .rdx (.reg .rcx)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .rdi ∧ s'.gpr .rdx = s.gpr .rdx + 8 ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.zf = some (s.gpr .rdx + 8 - s.gpr .rcx == 0) := by
  refine wp_mov fun s₁ h₁ => wp_mov fun s₂ h₂ => wp_mov fun s₃ h₃ => wp_addi fun s₄ h₄ =>
    wp_cmp fun s₅ g₅ m₅ r₅ w₅ _ z₅ => wp_nil ?_
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = (8 : BitVec 64) := by decide
  have di : s₄.gpr .rdi = s.gpr .rsi := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)]
  have si : s₄.gpr .rsi = s.gpr .rdi := by
    rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.gpr]
  have dx : s₄.gpr .rdx = s.gpr .rdx + 8 := by
    rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), e8]
  have cx : s₄.gpr .rcx = s.gpr .rcx := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  have sp : s₄.gpr .rsp = s.gpr .rsp := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  exact ⟨by rw [g₅, di], by rw [g₅, si], by rw [g₅, dx], by rw [g₅, cx], by rw [g₅, sp],
    by rw [m₅, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [r₅, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
    by rw [w₅, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [z₅, dx, cx]⟩

theorem round_ok (s : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s.rd s.wr src dst rcp) (hrdi : s.gpr .rdi = src) (hrsi : s.gpr .rsi = dst)
    (hrdx : s.gpr .rdx = rcp) (hA : Lanes s.mem src A) (hrc : s.mem.readW rcp 64 = rc) :
    WP isa (.block round) s fun s' =>
      Lanes s'.mem dst (outState A rc) ∧ Frame [⟨dst, 200⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rdi = dst ∧ s'.gpr .rsi = src ∧
      s'.gpr .rdx = rcp + 8 ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.zf = some (rcp + 8 - s.gpr .rcx == 0) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (columns_ok s src A hrdi he.src_in hA) fun s₁ ⟨k₁, m₁, c₁⟩ => ?_
  refine WP.mono (dcols_ok s₁ A c₁) fun s₂ ⟨k₂, m₂, _, d₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  refine WP.mono (planes_ok s₂ src dst rcp A rc (by rw [k₁₂.rd, k₁₂.wr]; exact he)
    ((k₁₂.ptrs .rdi (by decide)).trans hrdi) ((k₁₂.ptrs .rsi (by decide)).trans hrsi)
    ((k₁₂.ptrs .rdx (by decide)).trans hrdx) (by rw [m₂, m₁]; exact hA) (by rw [m₂, m₁, hrc]) d₂)
    fun s₃ h₃ => ?_
  have k₃ := k₁₂.trans h₃.keeps
  refine WP.mono (tail_ok s₃) fun s₄ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ => ?_
  have hdx : s₃.gpr .rdx = rcp := (k₃.ptrs .rdx (by decide)).trans hrdx
  have hcx : s₃.gpr .rcx = s.gpr .rcx := k₃.ptrs .rcx (by decide)
  refine ⟨fun i hi => ?_, by rw [e₆, ← m₁, ← m₂]; exact h₃.frame, by rw [e₇, k₃.rd],
    by rw [e₈, k₃.wr], by rw [e₁, k₃.ptrs .rsi (by decide), hrsi],
    by rw [e₂, k₃.ptrs .rdi (by decide), hrdi], by rw [e₃, hdx], by rw [e₄, hcx],
    by rw [e₅, k₃.ptrs .rsp (by decide)], by rw [e₉, hdx, hcx]⟩
  rw [e₆, h₃.lanes i (by omega)]
  simp [outState]

end VG.Proof.Sha3.X86_64
