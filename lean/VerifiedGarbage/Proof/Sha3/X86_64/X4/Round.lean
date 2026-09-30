import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp

/-!
# Keccak-f[1600] four times at once on x86-64: one round

Untrusted: everything here is checked by Lean. One round (`round`) of the
four interleaved states at `rdi` to those at `rsi`, lane by lane
(`Proof.Sha3.out`) in each of the four elements, and the swap of `rdi` and
`rsi` after it. The proof follows the scalar one (`Proof/Sha3/X86_64/Permute.lean`).
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3 (C D B out rotl outState)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha3.X86_64 (ea_at wp_mov wp_addi wp_cmp wp_nil)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## The four states in memory -/

/-- Lane `i` of state `k` of the four at `p`. -/
abbrev la (p : Addr) (i k : Nat) : Addr := p + BitVec.ofNat 64 (32 * i + 8 * k)

/-- The four states at `p` hold `A 0`, …, `A 3`. -/
def Lanes4 (m : Mem) (p : Addr) (A : Nat → KState) : Prop :=
  ∀ i < 25, ∀ k < 4, m.readW (la p i k) 64 = (A k)[i]!

theorem la_eq (p : Addr) (i k : Nat) :
    p + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (8 * k) = la p i k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Where a round reads and writes: the states at `src`, the round constant
at `rcp`, and the states at `dst`, which overlap neither. -/
structure Env (rd wr : List Region) (src dst rcp : Addr) : Prop where
  src_in : ∀ i < 25, InRegions (rd ++ wr) (src + BitVec.ofNat 64 (32 * i)) 32
  dst_out : ∀ i < 25, InRegions wr (dst + BitVec.ofNat 64 (32 * i)) 32
  rc_in : InRegions (rd ++ wr) rcp 32
  dst_src : Region.Disjoint ⟨dst, 800⟩ ⟨src, 800⟩
  dst_rc : Region.Disjoint ⟨dst, 800⟩ ⟨rcp, 32⟩

theorem la_contains (p : Addr) {i k : Nat} (hi : i < 25) (hk : k < 4) :
    (⟨p, 800⟩ : Region).Contains (la p i k) (64 / 8) :=
  Offset.contains_base p (by omega) (by omega)

theorem Env.src_frame {rd wr : List Region} {src dst rcp : Addr} (h : Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 800⟩] m m') {i k : Nat} (hi : i < 25) (hk : k < 4) :
    m'.readW (la src i k) 64 = m.readW (la src i k) 64 :=
  hf.readW (la_contains src hi hk) (by simpa using h.dst_src.symm) (by decide)

theorem Env.rc_frame {rd wr : List Region} {src dst rcp : Addr} (h : Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 800⟩] m m') {k : Nat} (hk : k < 4) :
    m'.readW (la rcp 0 k) 64 = m.readW (la rcp 0 k) 64 :=
  hf.readW (Offset.contains_base rcp (show 32 * 0 + 8 * k + 64 / 8 ≤ 32 by omega) (by omega))
    (by simpa using h.dst_rc.symm) (by decide)

/-! ## Registers -/

theorem creg_inj : ∀ x < 5, ∀ x' < 5, creg x = creg x' → x = x' := by decide
theorem dreg_inj : ∀ x < 5, ∀ x' < 5, dreg x = dreg x' → x = x' := by decide
theorem creg_dreg : ∀ x < 5, ∀ x' < 5, creg x ≠ dreg x' := by decide
theorem T_creg : ∀ x < 5, T ≠ creg x := by decide
theorem T_dreg : ∀ x < 5, T ≠ dreg x := by decide
theorem U_creg : ∀ x < 5, U ≠ creg x := by decide
theorem U_dreg : ∀ x < 5, U ≠ dreg x := by decide
theorem T_U : T ≠ U := by decide

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : creg x' ≠ creg x :=
  fun e => h (creg_inj x' hx' x hx e)

theorem dreg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : dreg x' ≠ dreg x :=
  fun e => h (dreg_inj x' hx' x hx e)

/-! ## Vector code -/

/-- `s'` differs from `s` only in the vector registers `ws` (and the flags). -/
structure VW (s s' : State) (ws : List XReg) : Prop where
  other : ∀ r, r ∉ ws → ∀ k < 4, q4 s' r k = q4 s r k
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VW.refl (s : State) (ws : List XReg) : VW s s ws := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem VW.trans {s₁ s₂ s₃ : State} {ws : List XReg} (h₁ : VW s₁ s₂ ws) (h₂ : VW s₂ s₃ ws) : VW s₁ s₃ ws :=
  ⟨fun r h k hk => (h₂.other r h k hk).trans (h₁.other r h k hk), h₂.gpr.trans h₁.gpr,
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem VUpd.vw {s s' : State} {d : XReg} {v : Nat → BitVec 64} (h : VUpd s s' d v) {ws : List XReg}
    (hd : d ∈ ws) : VW s s' ws :=
  ⟨fun r hr k hk => h.other r (fun e => hr (e ▸ hd)) k hk, h.gpr, h.mem, h.rd, h.wr⟩

theorem VW.upd {s₀ s s' : State} {ws : List XReg} (h : VW s₀ s ws) {d : XReg} {v : Nat → BitVec 64}
    (u : VUpd s s' d v) (hd : d ∈ ws) : VW s₀ s' ws := h.trans (u.vw hd)

/-- A load of lane `i` of the four states at `p` (`= b`), as they were at `s₀`. -/
theorem wp_ld {is : List Instr} {Q : State → Prop} {s₀ s : State} {ws : List XReg} (h : VW s₀ s ws)
    {b : Reg} {p : Addr} {i : Nat} {d : XReg} (hb : s₀.gpr b = p)
    (hin : InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 (32 * i)) 32)
    (k : ∀ s', VUpd s s' d (fun k => s₀.mem.readW (la p i k) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (ld d b i :: is)) s Q :=
  wp_vld (by rw [ea_at, h.gpr, hb]) (by rw [h.rd, h.wr]; exact hin) fun s' u =>
    k s' ⟨fun j hj => by rw [u.val j hj, h.mem, la_eq], u.other, u.gpr, u.mem, u.rd, u.wr⟩

/-! ## θ -/

/-- What the round reads before it writes: the states at `src`. -/
structure Src (s : State) (src : Addr) (A : Nat → KState) : Prop where
  rdi : s.gpr .rdi = src
  src_in : ∀ i < 25, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (32 * i)) 32
  lanes : Lanes4 s.mem src A

theorem Src.vw {s s' : State} {src : Addr} {A : Nat → KState} (h : Src s src A) {ws : List XReg}
    (hw : VW s s' ws) : Src s' src A :=
  ⟨by rw [hw.gpr, h.rdi], by rw [hw.rd, hw.wr]; exact h.src_in, by rw [hw.mem]; exact h.lanes⟩

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (src : Addr) (A : Nat → KState) (hs : Src s src A) :
    WP isa (.block (column x)) s fun s' =>
      VW s s' [creg x, T] ∧ ∀ k < 4, q4 s' (creg x) k = C (A k) x := by
  have cT : creg x ≠ T := (T_creg x hx).symm
  have m₁ : creg x ∈ [creg x, T] := by simp
  have m₂ : T ∈ [creg x, T] := by simp
  have w₀ := VW.refl s [creg x, T]
  unfold column
  refine wp_ld w₀ hs.rdi (hs.src_in _ (by omega)) fun s₁ u₁ => ?_
  have w₁ := w₀.upd u₁ m₁
  refine wp_ld w₁ hs.rdi (hs.src_in _ (by omega)) fun s₂ u₂ => ?_
  have w₂ := w₁.upd u₂ m₂
  refine wp_vxor fun s₃ u₃ => ?_
  have w₃ := w₂.upd u₃ m₁
  refine wp_ld w₃ hs.rdi (hs.src_in _ (by omega)) fun s₄ u₄ => ?_
  have w₄ := w₃.upd u₄ m₂
  refine wp_vxor fun s₅ u₅ => ?_
  have w₅ := w₄.upd u₅ m₁
  refine wp_ld w₅ hs.rdi (hs.src_in _ (by omega)) fun s₆ u₆ => ?_
  have w₆ := w₅.upd u₆ m₂
  refine wp_vxor fun s₇ u₇ => ?_
  have w₇ := w₆.upd u₇ m₁
  refine wp_ld w₇ hs.rdi (hs.src_in _ (by omega)) fun s₈ u₈ => ?_
  have w₈ := w₇.upd u₈ m₂
  refine wp_vxor fun s₉ u₉ => wp_nil ⟨w₈.upd u₉ m₁, fun k hk => ?_⟩
  simp only [u₉.val k hk, u₈.val k hk, u₈.other _ cT k hk, u₇.val k hk, u₆.val k hk, u₆.other _ cT k hk,
    u₅.val k hk, u₄.val k hk, u₄.other _ cT k hk, u₃.val k hk, u₂.val k hk, u₂.other _ cT k hk,
    u₁.val k hk, hs.lanes x (by omega) k hk, hs.lanes (x + 5) (by omega) k hk,
    hs.lanes (x + 10) (by omega) k hk, hs.lanes (x + 15) (by omega) k hk, hs.lanes (x + 20) (by omega) k hk]
  rfl

/-- `s'` agrees with `s` but for the vector registers and the flags. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {s₁ s₂ s₃ : State} (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) : Same s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem VW.same {s s' : State} {ws : List XReg} (h : VW s s' ws) : Same s s' := ⟨h.gpr, h.mem, h.rd, h.wr⟩

theorem Src.same {s s' : State} {src : Addr} {A : Nat → KState} (h : Src s src A) (hw : Same s s') :
    Src s' src A :=
  ⟨by rw [hw.gpr, h.rdi], by rw [hw.rd, hw.wr]; exact h.src_in, by rw [hw.mem]; exact h.lanes⟩

/-- After the first `n` columns. -/
def ColInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ ∀ x < n, ∀ k < 4, q4 s (creg x) k = C (A k) x

theorem columns_ok (s₀ : State) (src : Addr) (A : Nat → KState) (hs : Src s₀ src A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ A) (fun x s hx ⟨hw, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx s src A (hs.same hw)) fun s' ⟨h, hv⟩ => ⟨hw.trans h.same, fun x' hx' k hk => ?_⟩
  by_cases e : x' = x
  · subst e; exact hv k hk
  · rw [h.other _ (by simpa using ⟨creg_ne hx (by omega) e, (T_creg x' (by omega)).symm⟩) k hk,
      hc x' (by omega) k hk]

/-! ## D -/

theorem rotr63 (v : BitVec 64) : v <<< 1 ||| v >>> 63 = v.rotateRight 63 := by
  have := shr_or_shl v (n := 1) (by decide) (by decide)
  rwa [BitVec.or_comm] at this

theorem dcol_ok (x : Nat) (_hx : x < 5) (s : State) (A : Nat → KState)
    (hc : ∀ x' < 5, ∀ k < 4, q4 s (creg x') k = C (A k) x') :
    WP isa (.block (dcol x)) s fun s' =>
      VW s s' [T, U, dreg x] ∧ ∀ k < 4, q4 s' (dreg x) k = D (A k) x := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  have w₀ := VW.refl s [T, U, dreg x]
  unfold dcol
  refine wp_vshl (by decide) fun s₁ u₁ => wp_vshr (by decide) fun s₂ u₂ => wp_vor fun s₃ u₃ =>
    wp_vxor fun s₄ u₄ => wp_nil ⟨(((w₀.upd u₁ (by simp)).upd u₂ (by simp)).upd u₃ (by simp)).upd u₄ (by simp),
      fun k hk => ?_⟩
  simp only [u₄.val k hk, u₃.val k hk, u₃.other _ (T_creg _ h4).symm k hk, u₂.other _ T_U k hk,
    u₂.val k hk, u₂.other _ (U_creg _ h4).symm k hk, u₁.val k hk, u₁.other _ (T_creg _ h1).symm k hk,
    u₁.other _ (T_creg _ h4).symm k hk, hc _ h1 k hk, hc _ h4 k hk, rotr63]
  rfl

/-- After the first `n` of the `D[x]`. -/
def DInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x < 5, ∀ k < 4, q4 s (creg x) k = C (A k) x) ∧ ∀ x < n, ∀ k < 4, q4 s (dreg x) k = D (A k) x

theorem dcols_ok (s₀ : State) (A : Nat → KState) (hc : ∀ x < 5, ∀ k < 4, q4 s₀ (creg x) k = C (A k) x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ A) (fun x s hx ⟨hw, hcs, hd⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hc, fun _ h => absurd h (by omega)⟩
  refine WP.mono (dcol_ok x hx s A hcs) fun s' ⟨h, hv⟩ => ⟨hw.trans h.same, fun x' hx' k hk => ?_, fun x' hx' k hk => ?_⟩
  · rw [h.other _ (by simpa using ⟨(T_creg x' hx').symm, (U_creg x' hx').symm, creg_dreg x' hx' x hx⟩) k hk,
      hcs x' hx' k hk]
  · by_cases e : x' = x
    · subst e; exact hv k hk
    · rw [h.other _ (by simpa using ⟨(T_dreg x' (by omega)).symm, (U_dreg x' (by omega)).symm,
          dreg_ne hx (by omega) e⟩) k hk,
        hd x' (by omega) k hk]

/-! ## A plane -/

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) (s : State) (src : Addr) (A : Nat → KState)
    (hs : Src s src A) (hd : ∀ x' < 5, ∀ k < 4, q4 s (dreg x') k = D (A k) x') :
    WP isa (.block (laneB x y)) s fun s' =>
      VW s s' [creg x, T] ∧ ∀ k < 4, q4 s' (creg x) k = B (A k) x y := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk5 : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  have cT : creg x ≠ T := (T_creg x hx).symm
  have w₀ := VW.refl s [creg x, T]
  unfold laneB
  rw [List.cons_append, List.cons_append]
  refine wp_ld w₀ hs.rdi (hs.src_in _ hj) fun s₁ u₁ => wp_vxor fun s₂ u₂ => ?_
  have w₂ := (w₀.upd u₁ (by simp)).upd u₂ (by simp)
  have hv : ∀ k < 4, q4 s₂ (creg x) k = (A k)[piSrc x y]! ^^^ D (A k) ((x + 3 * y) % 5) := fun k hk => by
    simp only [u₂.val k hk, u₁.val k hk, u₁.other _ (creg_dreg x hx _ hk5).symm k hk, hd _ hk5 k hk,
      hs.lanes _ hj k hk]
  split
  · rename_i h0
    refine wp_nil ⟨w₂, fun k hk => ?_⟩
    rw [hv k hk, B, rotl, h0, ite_eq_left rfl]
  · rename_i h0
    have hr := Proof.Sha3.rhoOff_lt _ hj
    refine wp_vshl hr fun s₃ u₃ => wp_vshr (by omega) fun s₄ u₄ => wp_vor fun s₅ u₅ =>
      wp_nil ⟨((w₂.upd u₃ (by simp)).upd u₄ (by simp)).upd u₅ (by simp), fun k hk => ?_⟩
    simp only [u₅.val k hk, u₄.val k hk, u₄.other _ cT.symm k hk, u₃.val k hk, u₃.other _ cT k hk, hv k hk]
    rw [shr_or_shl _ (by omega) hr, B, rotl, ite_eq_right h0]

/-- After the first `n` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (A : Nat → KState) (y n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x < 5, ∀ k < 4, q4 s (dreg x) k = D (A k) x) ∧ ∀ x < n, ∀ k < 4, q4 s (creg x) k = B (A k) x y

theorem laneBs_ok (y : Nat) (hy : y < 5) (s₀ : State) (src : Addr) (A : Nat → KState) (hs : Src s₀ src A)
    (hd : ∀ x < 5, ∀ k < 4, q4 s₀ (dreg x) k = D (A k) x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB x y)) s₀ (BInv s₀ A y 5) := by
  refine wp_range_flatMap (M := isa) (BInv s₀ A y) (fun x s hx ⟨hw, hds, hb⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hd, fun _ h => absurd h (by omega)⟩
  refine WP.mono (laneB_ok x y hx hy s src A (hs.same hw) hds) fun s' ⟨h, hv⟩ =>
    ⟨hw.trans h.same, fun x' hx' k hk => ?_, fun x' hx' k hk => ?_⟩
  · rw [h.other _ (by simpa using ⟨(creg_dreg x hx x' hx').symm, (T_dreg x' hx').symm⟩) k hk, hds x' hx' k hk]
  · by_cases e : x' = x
    · subst e; exact hv k hk
    · rw [h.other _ (by simpa using ⟨creg_ne hx (by omega) e, (T_creg x' (by omega)).symm⟩) k hk,
        hb x' (by omega) k hk]

theorem not_eq_xor (v : Lane) : ~~~v = v ^^^ 0xffffffffffffffff := by
  rw [BitVec.xor_comm]; rfl

/-- The 64-bit element `k` of a 256-bit write, read back. -/
theorem readW_write256 (m : Mem) (a : Addr) (v : BitVec 256) {k : Nat} (hk : k < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * k)) 64 = v.extractLsb' (64 * k) 64 := by
  have e := readW_writeW_inside m a v (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * k) = 64 * k by omega] at e
  exact e

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) (s : State) (dst rcp : Addr) (A : Nat → KState)
    (rc : Lane) (hrsi : s.gpr .rsi = dst) (hrdx : s.gpr .rdx = rcp)
    (hout : InRegions s.wr (dst + BitVec.ofNat 64 (32 * (x + 5 * y))) 32)
    (hrc_in : InRegions (s.rd ++ s.wr) (rcp + BitVec.ofNat 64 (32 * 0)) 32)
    (hrc : ∀ k < 4, s.mem.readW (la rcp 0 k) 64 = rc)
    (hb : ∀ x' < 5, ∀ k < 4, q4 s (creg x') k = B (A k) x' y) :
    WP isa (.block (chi x y)) s fun s' =>
      s'.gpr = s.gpr ∧ (∀ r, r ≠ T → r ≠ U → ∀ k < 4, q4 s' r k = q4 s r k) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∃ v : BitVec 256, s'.mem = s.mem.writeW (dst + BitVec.ofNat 64 (32 * (x + 5 * y))) v ∧
        ∀ k < 4, v.extractLsb' (64 * k) 64 = out (A k) rc x y := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have w₀ := VW.refl s [T, U]
  unfold chi
  simp only [List.cons_append, List.nil_append]
  refine wp_vandn fun s₁ u₁ => wp_vxor fun s₂ u₂ => ?_
  have w₂ := (w₀.upd u₁ (by simp)).upd u₂ (by simp)
  have ht : ∀ k < 4, q4 s₂ T k = (B (A k) ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B (A k) ((x + 2) % 5) y ^^^
      B (A k) x y := fun k hk => by
    simp only [u₂.val k hk, u₁.val k hk, u₁.other _ (T_creg _ hx).symm k hk, hb _ h1 k hk, hb _ h2 k hk,
      hb _ hx k hk, not_eq_xor]
  -- The store, from a state that differs from `s` only in `T` and `U`.
  have fin : ∀ s₅ : State, VW s s₅ [T, U] → (∀ k < 4, q4 s₅ T k = out (A k) rc x y) →
      WP isa (.block [Impl.Sha3.X86_64.X4.st .rsi (x + 5 * y) T]) s₅ fun s' =>
        s'.gpr = s.gpr ∧ (∀ r, r ≠ T → r ≠ U → ∀ k < 4, q4 s' r k = q4 s r k) ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ ∃ v : BitVec 256, s'.mem = s.mem.writeW (dst + BitVec.ofNat 64 (32 * (x + 5 * y))) v ∧
          ∀ k < 4, v.extractLsb' (64 * k) 64 = out (A k) rc x y := fun s₅ h₅ hv => by
    refine wp_vst (by rw [ea_at, h₅.gpr, hrsi]) (by rw [h₅.wr]; exact hout) fun s₆ g₆ q₆ m₆ r₆ w₆ => wp_nil ?_
    refine ⟨by rw [g₆, h₅.gpr], fun r h₁ h₂ k hk => by rw [q₆, h₅.other r (by simp [h₁, h₂]) k hk],
      by rw [r₆, h₅.rd], by rw [w₆, h₅.wr], s₅.ymm T, by rw [m₆, h₅.mem], fun k hk => ?_⟩
    rw [q4_ymm _ _ hk, hv k hk]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [and_self, ite_true, List.cons_append, List.nil_append]
    refine wp_ld w₂ hrdx hrc_in fun s₃ u₃ => wp_vxor fun s₄ u₄ => ?_
    refine fin s₄ ((w₂.upd u₃ (by simp)).upd u₄ (by simp)) fun k hk => ?_
    simp only [u₄.val k hk, u₃.val k hk, u₃.other _ T_U k hk, ht k hk, hrc k hk, out, and_self, ite_true]
  · simp only [h0, ite_false, List.nil_append]
    refine fin s₂ w₂ fun k hk => ?_
    rw [ht k hk, out]
    simp only [h0, ite_false]

/-- After `n` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (A : Nat → KState) (rc : Lane) (dst : Addr) (y n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨dst, 800⟩] s₀.mem s.mem
  dregs : ∀ x < 5, ∀ k < 4, q4 s (dreg x) k = D (A k) x
  bregs : ∀ x < 5, ∀ k < 4, q4 s (creg x) k = B (A k) x y
  lanes : ∀ j < 5 * y + n, ∀ k < 4, s.mem.readW (la dst j k) 64 = out (A k) rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) (s₀ : State) (src dst rcp : Addr) (A : Nat → KState) (rc : Lane)
    (he : Env s₀.rd s₀.wr src dst rcp) (hrsi : s₀.gpr .rsi = dst) (hrdx : s₀.gpr .rdx = rcp)
    (hrc : ∀ k < 4, s₀.mem.readW (la rcp 0 k) 64 = rc) (s : State) (hs : ChiInv s₀ A rc dst y 0 s) :
    WP isa (.block ((List.range 5).flatMap fun x => chi x y)) s (ChiInv s₀ A rc dst y 5) := by
  refine wp_range_flatMap (M := isa) (ChiInv s₀ A rc dst y) (fun x s hx hi => ?_) 5 (Nat.le_refl _) s hs
  have hj : x + 5 * y < 25 := by omega
  refine WP.mono (chi_ok x y hx hy s dst rcp A rc (by rw [hi.gpr, hrsi]) (by rw [hi.gpr, hrdx])
    (by rw [hi.wr]; exact he.dst_out _ hj) (by rw [hi.rd, hi.wr]; simpa using he.rc_in)
    (fun k hk => by rw [he.rc_frame hi.frame hk, hrc k hk]) hi.bregs)
    fun s' ⟨hg, hq, hrd, hwr, v, hm, hv⟩ => ?_
  refine ⟨hg.trans hi.gpr, hrd.trans hi.rd, hwr.trans hi.wr, ?_,
    fun x' hx' k hk => by rw [hq _ (T_dreg x' hx').symm (U_dreg x' hx').symm k hk, hi.dregs x' hx' k hk],
    fun x' hx' k hk => by rw [hq _ (T_creg x' hx').symm (U_creg x' hx').symm k hk, hi.bregs x' hx' k hk],
    fun j hj' k hk => ?_⟩
  · rw [hm]; exact hi.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base dst (by omega) (by omega))
  · rw [hm]
    by_cases e : j = x + 5 * y
    · subst e
      rw [← la_eq, readW_write256 _ _ _ hk, hv k hk, show (x + 5 * y) % 5 = x by omega,
        show (x + 5 * y) / 5 = y by omega]
    · have := readW_writeW_off s.mem dst v (d := 32 * j + 8 * k) (e := 32 * (x + 5 * y)) (n := 8)
        (by omega) (by omega) (by omega)
      rw [this]
      exact hi.lanes j (by omega) k hk

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (A : Nat → KState) (rc : Lane) (dst : Addr) (y : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨dst, 800⟩] s₀.mem s.mem
  dregs : ∀ x < 5, ∀ k < 4, q4 s (dreg x) k = D (A k) x
  lanes : ∀ j < 5 * y, ∀ k < 4, s.mem.readW (la dst j k) 64 = out (A k) rc (j % 5) (j / 5)

theorem planes_ok (s₀ : State) (src dst rcp : Addr) (A : Nat → KState) (rc : Lane)
    (he : Env s₀.rd s₀.wr src dst rcp) (hrdi : s₀.gpr .rdi = src) (hrsi : s₀.gpr .rsi = dst)
    (hrdx : s₀.gpr .rdx = rcp) (hA : Lanes4 s₀.mem src A) (hrc : ∀ k < 4, s₀.mem.readW (la rcp 0 k) 64 = rc)
    (hd : ∀ x < 5, ∀ k < 4, q4 s₀ (dreg x) k = D (A k) x) :
    WP isa (.block ((List.range 5).flatMap plane)) s₀ (PInv s₀ A rc dst 5) := by
  refine wp_range_flatMap (M := isa) (PInv s₀ A rc dst) (fun y s hy hi => ?_) 5 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, hd, fun _ h => absurd h (by omega)⟩
  unfold plane
  rw [WP.block_append_iff]
  have hs : Src s src A := ⟨by rw [hi.gpr, hrdi], by rw [hi.rd, hi.wr]; exact he.src_in,
    fun i hi' k hk => by rw [he.src_frame hi.frame hi' hk, hA i hi' k hk]⟩
  refine WP.mono (laneBs_ok y hy s src A hs hi.dregs) fun s₁ ⟨hw, hds, hb⟩ => ?_
  refine WP.mono (chis_ok y hy s₀ src dst rcp A rc he hrsi hrdx hrc s₁
    ⟨hw.gpr.trans hi.gpr, hw.rd.trans hi.rd, hw.wr.trans hi.wr, by rw [hw.mem]; exact hi.frame, hds, hb,
      fun j hj k hk => by rw [hw.mem]; exact hi.lanes j hj k hk⟩)
    fun s₂ h₂ => ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.frame, h₂.dregs, fun j hj => h₂.lanes j (by omega)⟩

/-! ## The round -/

theorem tail_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rax),
      .alu .add .rdx (.imm 32), .alu .cmp .rdx (.reg .rcx)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .rdi ∧ s'.gpr .rdx = s.gpr .rdx + 32 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (s.gpr .rdx + 32 - s.gpr .rcx == 0) := by
  refine wp_mov fun s₁ h₁ => wp_mov fun s₂ h₂ => wp_mov fun s₃ h₃ => wp_addi fun s₄ h₄ =>
    wp_cmp fun s₅ g₅ m₅ r₅ w₅ _ z₅ => wp_nil ?_
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = (32 : BitVec 64) := by decide
  have dx : s₄.gpr .rdx = s.gpr .rdx + 32 := by
    rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), e32]
  have cx : s₄.gpr .rcx = s.gpr .rcx := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  exact ⟨by rw [g₅, h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)],
    by rw [g₅, h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.gpr], by rw [g₅, dx],
    fun r ra rdi rsi rdx => by rw [g₅, h₄.other r rdx, h₃.other r rsi, h₂.other r rdi, h₁.other r ra],
    by rw [m₅, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [r₅, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
    by rw [w₅, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [z₅, dx, cx]⟩

theorem round_ok (s : State) (src dst rcp : Addr) (A : Nat → KState) (rc : Lane)
    (he : Env s.rd s.wr src dst rcp) (hrdi : s.gpr .rdi = src) (hrsi : s.gpr .rsi = dst)
    (hrdx : s.gpr .rdx = rcp) (hA : Lanes4 s.mem src A) (hrc : ∀ k < 4, s.mem.readW (la rcp 0 k) 64 = rc) :
    WP isa (.block round) s fun s' =>
      Lanes4 s'.mem dst (fun k => outState (A k) rc) ∧ Frame [⟨dst, 800⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rdi = dst ∧ s'.gpr .rsi = src ∧ s'.gpr .rdx = rcp + 32 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.zf = some (rcp + 32 - s.gpr .rcx == 0) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (columns_ok s src A ⟨hrdi, he.src_in, hA⟩) fun s₁ ⟨k₁, c₁⟩ => ?_
  refine WP.mono (dcols_ok s₁ A c₁) fun s₂ ⟨k₂, _, d₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  refine WP.mono (planes_ok s₂ src dst rcp A rc (by rw [k₁₂.rd, k₁₂.wr]; exact he)
    (by rw [k₁₂.gpr, hrdi]) (by rw [k₁₂.gpr, hrsi]) (by rw [k₁₂.gpr, hrdx]) (by rw [k₁₂.mem]; exact hA)
    (by rw [k₁₂.mem]; exact hrc) d₂) fun s₃ h₃ => ?_
  refine WP.mono (tail_ok s₃) fun s₄ ⟨e₁, e₂, e₃, e₄, e₆, e₇, e₈, e₉⟩ => ?_
  have hg : s₃.gpr = s.gpr := h₃.gpr.trans k₁₂.gpr
  refine ⟨fun i hi k hk => ?_, by rw [e₆, ← k₁₂.mem]; exact h₃.frame, by rw [e₇, h₃.rd, k₁₂.rd],
    by rw [e₈, h₃.wr, k₁₂.wr], by rw [e₁, hg, hrsi], by rw [e₂, hg, hrdi], by rw [e₃, hg, hrdx],
    fun r a b c d => by rw [e₄ r a b c d, hg], by rw [e₉, hg, hrdx]⟩
  rw [e₆, h₃.lanes i (by omega) k hk]
  simp [outState, hi]

end VG.Proof.Sha3.X86_64.X4
