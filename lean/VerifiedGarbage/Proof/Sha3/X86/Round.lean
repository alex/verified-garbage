import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Sha3.X86.Wp

/-!
# Keccak-f[1600] on x86 (32-bit): one round

Untrusted: everything here is checked by Lean. One round (`round src dst`)
from the state at `src` to the state at `dst`, lane by lane
(`Proof.Sha3.out`), each lane a pair of 32-bit words, through the work area
of the scratch space (`C`, then `B`, and `D`), proved once for both of the
rounds of an iteration (`src`, `dst` being `esi`, `edi` or `edi`, `esi`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86 VG.Impl.Sha3.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha512.Word64 (lo hi)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha512.X86 (Only Pair Wrote rd64 write64 mem_rd Acc rd64_write64_self rd64_write64_ne
  rd64_frame wp_xorS)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_addi contains_addr)
open VG.Proof.Sha3 (C D B out outState)

abbrev KState := Spec.Sha3.State

/-! ## Registers -/

/-- The pointer registers of the rounds: `esi` (`state`) and `edi` (`scratch`). -/
def Ptr (r : Reg) : Prop := r = .esi ∨ r = .edi

theorem Ptr.ne {r : Reg} (h : Ptr r) : r ≠ .eax ∧ r ≠ .edx ∧ r ≠ .ecx ∧ r ≠ .ebp := by
  rcases h with rfl | rfl <;> decide

theorem nm1 {r a : Reg} (h : r ≠ a) : r ∉ [a] := by simp [h]
theorem nm3 {r a b c : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) (h₃ : r ≠ c) : r ∉ [a, b, c] := by
  simp [h₁, h₂, h₃]

/-! ## Regions -/

theorem addr_zero (b : BitVec 32) : addr b 0 = b.setWidth 64 := by simp [addr]

/-- The `n` bytes at offset `o` of a region at `b` are within its part at offset `a`. -/
theorem sub_contains {b : BitVec 32} {N a k o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hak : a + k ≤ N)
    (h1 : a ≤ o) (h2 : o + n ≤ a + k) (hn : 0 < n) : (⟨addr b a, k⟩ : Region).Contains (addr b o) n := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have hE : (b.setWidth 64).toNat = b.toNat := VG.Proof.Sha256.X86.Stream.addr_toNat b
  generalize b.setWidth 64 = E at *
  bv_omega

/-- Two parts of a region at `b` that do not overlap. -/
theorem sub_disj {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ha : a + n ≤ N)
    (hc : c + k ≤ N) (hn : 0 < n) (hk : 0 < k) (h : a + n ≤ c ∨ c + k ≤ a) :
    Region.Disjoint ⟨addr b a, n⟩ ⟨addr b c, k⟩ := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Proof.Sha3.off_disjoint _ (by omega) (by omega) h

/-- The region of `n` bytes at a 32-bit pointer. -/
abbrev reg32 (b : BitVec 32) (n : Nat) : Region := ⟨b.setWidth 64, n⟩

/-- The work area of the scratch space at `W`: `C` and then `B`, and `D`. -/
abbrev workR (W : BitVec 32) : Region := ⟨addr W 408, 80⟩

theorem work_contains {W : BitVec 32} (hfit : W.toNat + 512 ≤ 2 ^ 32) {o : Nat} (h1 : 408 ≤ o)
    (h2 : o + 4 ≤ 488) : (workR W).Contains (addr W o) 4 :=
  sub_contains (N := 512) hfit (by omega) h1 (by omega) (by omega)

theorem reg_contains {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) {o : Nat} (h : o + 4 ≤ N) :
    (reg32 b N).Contains (addr b o) 4 :=
  contains_addr h (by omega) hfit

theorem Frame.write64' {rs : List Region} {m m' : Mem} (h : Frame rs m m') {R : Region} (hr : R ∈ rs)
    {b : BitVec 32} {o : Nat} (hc0 : R.Contains (addr b o) 4) (hc4 : R.Contains (addr b (o + 4)) 4)
    (v : Lane) : Frame rs m (write64 m' b o v) :=
  (h.writeW hr _ hc0).writeW hr _ hc4

theorem rd64_frame' {rs : List Region} {m m' : Mem} (h : Frame rs m m') {R : Region} {b : BitVec 32}
    {o : Nat} (hc0 : R.Contains (addr b o) 4) (hc4 : R.Contains (addr b (o + 4)) 4)
    (hd : ∀ r ∈ rs, R.Disjoint r) : rd64 m' b o = rd64 m b o := by
  simp only [rd64]
  rw [h.readW hc4 hd (by decide), h.readW hc0 hd (by decide)]

/-- A word of the work area is unchanged by writes outside it. -/
theorem work_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {W : BitVec 32}
    (hfit : W.toNat + 512 ≤ 2 ^ 32) {o : Nat} (h1 : 408 ≤ o) (h2 : o + 8 ≤ 488)
    (hd : ∀ r ∈ rs, (workR W).Disjoint r) : rd64 m' W o = rd64 m W o :=
  rd64_frame' h (work_contains hfit h1 (by omega)) (work_contains hfit (by omega) (by omega)) hd

/-! ## States in memory -/

/-- The state at `b` holds `K`, lane `i` as the pair of words at `b + 8i`. -/
def Lanes32 (m : Mem) (b : BitVec 32) (K : KState) : Prop := ∀ i < 25, rd64 m b (8 * i) = K[i]!

theorem Lanes32.frame {m m' : Mem} {b : BitVec 32} {K : KState} (hK : Lanes32 m b K) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (reg32 b 200).Disjoint r) (hfit : b.toNat + 200 ≤ 2 ^ 32) :
    Lanes32 m' b K := fun i hi => by
  rw [rd64_frame hf hd hfit (by omega)]; exact hK i hi

/-- Where a round reads and writes: the state at `S`, the scratch space at
`W` (its work area), the round constant at `P`, and the state at `Dd`,
which overlaps none of the others. -/
structure Env (wr : List Region) (S Dd W P : BitVec 32) : Prop where
  fitS : S.toNat + 200 ≤ 2 ^ 32
  fitD : Dd.toNat + 200 ≤ 2 ^ 32
  fitW : W.toNat + 512 ≤ 2 ^ 32
  fitP : P.toNat + 8 ≤ 2 ^ 32
  accS : Acc wr S 200
  accD : Acc wr Dd 200
  accW : Acc wr W 512
  accP : Acc wr P 8
  sd : (reg32 S 200).Disjoint (reg32 Dd 200)
  sw : (reg32 S 200).Disjoint (workR W)
  dw : (reg32 Dd 200).Disjoint (workR W)
  pd : (reg32 P 8).Disjoint (reg32 Dd 200)
  pw : (reg32 P 8).Disjoint (workR W)

theorem Env.rd2W {wr : List Region} {S Dd W P : BitVec 32} (E : Env wr S Dd W P) {o : Nat} (ho : o + 8 ≤ 512)
    {s : State} (hw : s.wr = wr) : Rd2 s W o := fun h hh =>
  mem_rd (by rw [hw]; exact E.accW _ (by rcases hh with rfl | rfl <;> omega))

theorem Env.wr2W {wr : List Region} {S Dd W P : BitVec 32} (E : Env wr S Dd W P) {o : Nat} (ho : o + 8 ≤ 512)
    {s : State} (hw : s.wr = wr) : Wr2 s W o :=
  ⟨by rw [hw]; exact E.accW _ (by omega), by rw [hw]; exact E.accW _ (by omega)⟩

theorem cOff_lt (x : Nat) (hx : x < 5) : 408 ≤ cOff x ∧ cOff x + 8 ≤ 448 := by simp only [cOff]; omega

theorem dOff_lt (x : Nat) (hx : x < 5) : 448 ≤ dOff x ∧ dOff x + 8 ≤ 488 := by simp only [dOff]; omega

/-! ## θ -/

theorem colHalf_ok {src : Reg} (hsrc : Ptr src) {x h : Nat} (hx : x < 5) (hh : h = 0 ∨ h = 4)
    {S W : BitVec 32} {K : KState} (s : State) (hS : s.gpr src = S) (hW : s.gpr .edi = W)
    (aS : Acc s.wr S 200) (aW : Acc s.wr W 512) (hK : Lanes32 s.mem S K) :
    WP isa (.block (colHalf src x h)) s fun s' =>
      Wrote [.eax] s s' (s.mem.writeW (addr W (cOff x + h)) (half h (C K x))) := by
  have rS : ∀ i < 25, InRegions (s.rd ++ s.wr) (addr S (8 * i + h)) 4 := fun i hi =>
    mem_rd (aS _ (by rcases hh with rfl | rfl <;> omega))
  have ve : ∀ i < 25, s.mem.readW (addr S (8 * i + h)) 32 = half h K[i]! := fun i hi => by
    rw [← hK i hi, half_rd64 hh]
  have se := hsrc.ne.1
  unfold colHalf
  refine wp_ldm hS (rS x (by omega)) fun s₁ u₁ => ?_
  refine wp_xorm (by rw [u₁.other _ se, hS]) (by rw [u₁.rd, u₁.wr]; exact rS (x + 5) (by omega))
    fun s₂ u₂ => ?_
  have U₂ := Upd.trans u₁ u₂
  refine wp_xorm (by rw [U₂.other _ se, hS]) (by rw [U₂.rd, U₂.wr]; exact rS (x + 10) (by omega))
    fun s₃ u₃ => ?_
  have U₃ := Upd.trans U₂ u₃
  refine wp_xorm (by rw [U₃.other _ se, hS]) (by rw [U₃.rd, U₃.wr]; exact rS (x + 15) (by omega))
    fun s₄ u₄ => ?_
  have U₄ := Upd.trans U₃ u₄
  refine wp_xorm (by rw [U₄.other _ se, hS]) (by rw [U₄.rd, U₄.wr]; exact rS (x + 20) (by omega))
    fun s₅ u₅ => ?_
  have U₅ := Upd.trans U₄ u₅
  refine wp_stm (by rw [U₅.other _ (by decide), hW])
    (by rw [U₅.wr]; exact aW _ (by simp only [cOff]; rcases hh with rfl | rfl <;> omega))
    fun s₆ u₆ => WP.block_nil ⟨fun r hr => ?_, ?_, by rw [u₆.rd, U₅.rd], by rw [u₆.wr, U₅.wr]⟩
  · rw [u₆.gpr, U₅.other r (by simpa using hr)]
  · rw [u₆.mem, U₅.mem, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, U₄.mem, U₃.mem, U₂.mem, u₁.mem,
      ve x (by omega), ve (x + 5) (by omega), ve (x + 10) (by omega), ve (x + 15) (by omega),
      ve (x + 20) (by omega), C, half_xor, half_xor, half_xor, half_xor]

theorem column_ok {src : Reg} (hsrc : Ptr src) {x : Nat} (hx : x < 5) {S Dd W P : BitVec 32}
    {K : KState} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S) (hW : s.gpr .edi = W)
    (hK : Lanes32 s.mem S K) :
    WP isa (.block (column src x)) s fun s' => Wrote [.eax] s s' (write64 s.mem W (cOff x) (C K x)) := by
  have hc := cOff_lt x hx
  unfold column
  rw [WP.block_append_iff]
  refine WP.mono (colHalf_ok hsrc hx (.inl rfl) s hS hW E.accS E.accW hK) fun s₁ w₁ => ?_
  have hf : Frame [workR W] s.mem s₁.mem := by
    rw [w₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (work_contains E.fitW hc.1 (by omega))
  refine WP.mono (colHalf_ok hsrc hx (.inr rfl) s₁ (by rw [w₁.gpr _ (nm1 hsrc.ne.1), hS])
    (by rw [w₁.gpr _ (nm1 (by decide)), hW]) (by rw [w₁.wr]; exact E.accS) (by rw [w₁.wr]; exact E.accW)
    (hK.frame hf (by simpa using E.sw) E.fitS)) fun s₂ w₂ =>
      ⟨fun r hr => by rw [w₂.gpr r hr, w₁.gpr r hr], ?_, w₂.rd.trans w₁.rd, w₂.wr.trans w₁.wr⟩
  rw [w₂.mem, w₁.mem, half_lo, half_hi]; rfl

/-- After the first `k` columns. -/
structure ColInv (s₀ : State) (K : KState) (W : BitVec 32) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR W] s₀.mem s.mem
  cs : ∀ x < k, rd64 s.mem W (cOff x) = C K x

theorem columns_ok {src : Reg} (hsrc : Ptr src) {S Dd W P : BitVec 32} {K : KState} (s₀ : State)
    (E : Env s₀.wr S Dd W P) (hS : s₀.gpr src = S) (hW : s₀.gpr .edi = W) (hK : Lanes32 s₀.mem S K) :
    WP isa (.block ((List.range 5).flatMap (column src))) s₀ (ColInv s₀ K W 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ K W) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hc := cOff_lt x hx
  refine WP.mono (column_ok hsrc hx s (hI.wr ▸ E) (by rw [hI.gpr _ (nm1 hsrc.ne.1), hS])
    (by rw [hI.gpr _ (nm1 (by decide)), hW]) (hK.frame hI.frame (by simpa using E.sw) E.fitS))
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun x' hx' => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (work_contains E.fitW hc.1 (by omega))
      (work_contains E.fitW (by omega) (by omega)) _
  · rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by have := E.fitW; omega)
    · have := cOff_lt x' (by omega)
      rw [rd64_write64_ne _ _ (by have := E.fitW; omega) (by have := E.fitW; omega)
        (by simp only [cOff]; omega)]
      exact hI.cs x' (by omega)

/-! ## D -/

theorem dcol_ok (x : Nat) (hx : x < 5) {S Dd W P : BitVec 32} {K : KState} (s : State)
    (E : Env s.wr S Dd W P) (hW : s.gpr .edi = W) (hc : ∀ x' < 5, rd64 s.mem W (cOff x') = C K x') :
    WP isa (.block (dcol x)) s fun s' =>
      Wrote [.eax, .edx, .ecx] s s' (write64 s.mem W (dOff x) (D K x)) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  have c1 := cOff_lt _ h1
  have c4 := cOff_lt _ h4
  have d := dOff_lt x hx
  unfold dcol
  refine wp_ld2 hW (by decide) (E.rd2W (by omega) rfl) fun s₁ o₁ p₁ => ?_
  refine wp_rot (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O₂ : Only [.eax, .edx, .ecx] s s₂ := (o₁.trans o₂).mono (by simp)
  refine wp_xor2 (sw := false) (by rw [O₂.gpr _ (by decide), hW]) (by decide)
    (E.rd2W (by omega) O₂.wr) p₂ fun s₃ o₃ p₃ => ?_
  have O₃ : Only [.eax, .edx, .ecx] s s₃ := (O₂.trans o₃).mono (by simp)
  rw [← List.append_nil (st2 _ _)]
  refine wp_st2 (by rw [O₃.gpr _ (by decide), hW]) (E.wr2W (by omega) O₃.wr) p₃ fun s₄ u₄ =>
    WP.block_nil ⟨fun r hr => by rw [u₄.gpr, O₃.gpr r hr], ?_, by rw [u₄.rd, O₃.rd],
      by rw [u₄.wr, O₃.wr]⟩
  rw [u₄.mem, O₃.mem, O₂.mem, hc _ h1, hc _ h4, swapIf_true, swapIf_false,
    rotateRight_add _ (show 32 + 31 < 64 by decide)]
  rfl

/-- After the first `k` of the `D[x]`. -/
structure DInv (s₀ : State) (K : KState) (W : BitVec 32) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .edx, .ecx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR W] s₀.mem s.mem
  cs : ∀ x < 5, rd64 s.mem W (cOff x) = C K x
  ds : ∀ x < k, rd64 s.mem W (dOff x) = D K x

theorem dcols_ok {S Dd W P : BitVec 32} {K : KState} (s₀ : State) (E : Env s₀.wr S Dd W P)
    (hW : s₀.gpr .edi = W) (hc : ∀ x < 5, rd64 s₀.mem W (cOff x) = C K x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ K W 5) := by
  have fW := E.fitW
  refine wp_range_flatMap (M := isa) (DInv s₀ K W) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, hc, fun _ h => absurd h (by omega)⟩
  have d := dOff_lt x hx
  refine WP.mono (dcol_ok x hx s (hI.wr ▸ E) (by rw [hI.gpr _ (by decide), hW]) hI.cs)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (work_contains fW (by omega) (by omega))
      (work_contains fW (by omega) (by omega)) _
  · have := cOff_lt x' hx'
    rw [w.mem, rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
    exact hI.cs x' hx'
  · rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by have := dOff_lt x' (by omega); omega)
        (by simp only [dOff]; omega)]
      exact hI.ds x' (by omega)

/-! ## A plane -/

theorem rhoOff_ne32 : ∀ j < 25, rhoOff j ≠ 32 := by decide

/-- ρ's rotation, as the code does it: the halves swapped (`swp`), then a
rotation by less than 32 (`rotAmt`). -/
theorem rho_rot (v : Lane) {j : Nat} (hj : j < 25) :
    (swapIf (swp j) v).rotateRight (rotAmt j) = Proof.Sha3.rotl v (rhoOff j) := by
  have h64 := Proof.Sha3.rhoOff_lt j hj
  have h32 := rhoOff_ne32 j hj
  simp only [swp, rotAmt, Proof.Sha3.rotl]
  generalize rhoOff j = r at *
  by_cases h0 : r = 0
  · subst h0; simp [swapIf, rotateRight_zero']
  · by_cases hl : r < 32
    · simp only [h0, hl, ite_false, ite_true, decide_true, Bool.and_true, swapIf,
        show (0 < r) = True from eq_true (by omega), decide_true]
      rw [rotateRight_add _ (by omega), show 32 + (32 - r) = 64 - r by omega]
    · simp only [h0, hl, ite_false, swapIf, show decide (0 < r) = true from decide_eq_true (by omega),
        Bool.true_and, decide_false, Bool.false_eq_true]

theorem rotAmt_lt {j : Nat} (hj : j < 25) : rotAmt j < 32 := by
  have := rhoOff_ne32 j hj
  have := Proof.Sha3.rhoOff_lt j hj
  unfold rotAmt
  split
  · omega
  · split <;> omega

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) {src : Reg} (hsrc : Ptr src)
    {S Dd W P : BitVec 32} {K : KState} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S)
    (hW : s.gpr .edi = W) (hK : Lanes32 s.mem S K) (hD : ∀ x' < 5, rd64 s.mem W (dOff x') = D K x') :
    WP isa (.block (laneB src x y)) s fun s' =>
      Wrote [.eax, .edx, .ecx] s s' (write64 s.mem W (cOff x) (B K x y)) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  have d := dOff_lt _ hk
  have c := cOff_lt x hx
  unfold laneB
  refine wp_ld2 hS hsrc.ne.1 (fun h hh => mem_rd (E.accS _ (by rcases hh with rfl | rfl <;> omega)))
    fun s₁ o₁ p₁ => ?_
  refine wp_xor2 (by rw [o₁.gpr _ (by decide), hW]) (by decide) (E.rd2W (by omega) o₁.wr) p₁
    fun s₂ o₂ p₂ => ?_
  have O₂ : Only [.eax, .edx] s s₂ := (o₁.trans o₂).mono (by simp)
  refine wp_rot (rotAmt_lt hj) p₂ fun s₃ o₃ p₃ => ?_
  have O₃ : Only [.eax, .edx, .ecx] s s₃ := (O₂.trans o₃).mono (by simp)
  rw [← List.append_nil (st2 _ _)]
  refine wp_st2 (by rw [O₃.gpr _ (by decide), hW]) (E.wr2W (by omega) O₃.wr) p₃ fun s₄ u₄ =>
    WP.block_nil ⟨fun r hr => by rw [u₄.gpr, O₃.gpr r hr], ?_, by rw [u₄.rd, O₃.rd],
      by rw [u₄.wr, O₃.wr]⟩
  rw [u₄.mem, O₃.mem, o₁.mem, hK _ hj, hD _ hk, ← swapIf_xor, rho_rot _ hj, B]

/-- After the first `k` lanes `B[x]` of plane `y`. -/
structure BInv (s₀ : State) (K : KState) (W : BitVec 32) (y k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .edx, .ecx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR W] s₀.mem s.mem
  ds : ∀ x < 5, rd64 s.mem W (dOff x) = D K x
  bs : ∀ x < k, rd64 s.mem W (cOff x) = B K x y

theorem laneBs_ok (y : Nat) (hy : y < 5) {src : Reg} (hsrc : Ptr src) {S Dd W P : BitVec 32}
    {K : KState} (s₀ : State) (E : Env s₀.wr S Dd W P) (hS : s₀.gpr src = S) (hW : s₀.gpr .edi = W)
    (hK : Lanes32 s₀.mem S K) (hD : ∀ x < 5, rd64 s₀.mem W (dOff x) = D K x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB src x y)) s₀ (BInv s₀ K W y 5) := by
  have fW := E.fitW
  refine wp_range_flatMap (M := isa) (BInv s₀ K W y) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, hD, fun _ h => absurd h (by omega)⟩
  have c := cOff_lt x hx
  obtain ⟨se, sd, sc, -⟩ := hsrc.ne
  refine WP.mono (laneB_ok x y hx hy hsrc s (hI.wr ▸ E) (by rw [hI.gpr _ (nm3 se sd sc), hS])
    (by rw [hI.gpr _ (by decide), hW]) (hK.frame hI.frame (by simpa using E.sw) E.fitS) hI.ds)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (work_contains fW c.1 (by omega))
      (work_contains fW (by omega) (by omega)) _
  · have := dOff_lt x' hx'
    rw [w.mem, rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
    exact hI.ds x' hx'
  · rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by have := cOff_lt x' (by omega); omega)
        (by simp only [cOff]; omega)]
      exact hI.bs x' (by omega)

/-- Half `h` of lane `(x, y)` of the output. -/
theorem chiHalf_ok (x y h : Nat) (hx : x < 5) (hy : y < 5) (hh : h = 0 ∨ h = 4) {dst : Reg}
    (hdst : Ptr dst) {S Dd W P : BitVec 32} {K : KState} {rc : Lane} (s : State)
    (E : Env s.wr S Dd W P) (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P)
    (hb : ∀ x' < 5, rd64 s.mem W (cOff x') = B K x' y) (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (chiHalf dst x y h)) s fun s' =>
      Wrote [.eax] s s' (s.mem.writeW (addr Dd (8 * (x + 5 * y) + h)) (half h (out K rc x y))) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have c0 := cOff_lt x hx
  have c1 := cOff_lt _ h1
  have c2 := cOff_lt _ h2
  have hB : ∀ x' < 5, s.mem.readW (addr W (cOff x' + h)) 32 = half h (B K x' y) := fun x' hx' => by
    rw [← hb x' hx', half_rd64 hh]
  have rW : ∀ x' < 5, InRegions (s.rd ++ s.wr) (addr W (cOff x' + h)) 4 := fun x' hx' =>
    mem_rd (E.accW _ (by have := cOff_lt x' hx'; rcases hh with rfl | rfl <;> omega))
  unfold chiHalf
  simp only [List.cons_append, List.nil_append]
  refine wp_ldm hW (rW _ h1) fun s₁ u₁ => ?_
  refine wp_xorS rfl fun s₂ u₂ => ?_
  have U₂ := Upd.trans u₁ u₂
  refine wp_andm (by rw [U₂.other _ (by decide), hW]) (by rw [U₂.rd, U₂.wr]; exact rW _ h2)
    fun s₃ u₃ => ?_
  have U₃ := Upd.trans U₂ u₃
  refine wp_xorm (by rw [U₃.other _ (by decide), hW]) (by rw [U₃.rd, U₃.wr]; exact rW _ hx)
    fun s₄ u₄ => ?_
  have U₄ := Upd.trans U₃ u₄
  have v₄ : s₄.gpr .eax = half h ((B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^
      B K x y) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, U₃.mem, U₂.mem, hB _ h1, hB _ h2, hB _ hx, half_xor,
      half_and, half_xor, half_ones]
  have fin : ∀ s₅ : State, Upd s s₅ .eax (half h (out K rc x y)) →
      WP isa (.block [.store (at_ dst (8 * (x + 5 * y) + h)) .eax]) s₅ fun s' =>
        Wrote [.eax] s s' (s.mem.writeW (addr Dd (8 * (x + 5 * y) + h)) (half h (out K rc x y))) :=
    fun s₅ U₅ => wp_stm (by rw [U₅.other _ hdst.ne.1, hd])
      (by rw [U₅.wr]; exact E.accD _ (by rcases hh with rfl | rfl <;> omega))
      fun s₆ u₆ => WP.block_nil ⟨fun r hr => by rw [u₆.gpr, U₅.other r (by simpa using hr)],
        by rw [u₆.mem, U₅.mem, U₅.gpr], by rw [u₆.rd, U₅.rd], by rw [u₆.wr, U₅.wr]⟩
  by_cases h0 : x = 0 ∧ y = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    simp only [List.cons_append, List.nil_append]
    have hr : s.mem.readW (addr P h) 32 = half h rc := by rw [← hrc, half_rd64 hh, Nat.zero_add]
    refine wp_xorm (by rw [U₄.other _ (by decide), hP]) (by
      rw [U₄.rd, U₄.wr]; exact mem_rd (E.accP _ (by rcases hh with rfl | rfl <;> omega))) fun s₅ u₅ => ?_
    refine fin s₅ ⟨?_, (Upd.trans U₄ u₅).other, (Upd.trans U₄ u₅).mem, (Upd.trans U₄ u₅).rd, (Upd.trans U₄ u₅).wr⟩
    rw [u₅.gpr, v₄, U₄.mem, hr, ← half_xor, out]
    simp only [h0, and_self, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    simp only [List.nil_append]
    refine fin s₄ ⟨?_, U₄.other, U₄.mem, U₄.rd, U₄.wr⟩
    rw [v₄, out]
    simp only [h0, ite_false]

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) {dst : Reg} (hdst : Ptr dst)
    {S Dd W P : BitVec 32} {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd W P)
    (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P)
    (hb : ∀ x' < 5, rd64 s.mem W (cOff x') = B K x' y) (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (chi dst x y)) s fun s' =>
      Wrote [.eax] s s' (write64 s.mem Dd (8 * (x + 5 * y)) (out K rc x y)) := by
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  unfold chi
  rw [WP.block_append_iff]
  refine WP.mono (chiHalf_ok x y 0 hx hy (.inl rfl) hdst s E hd hW hP hb hrc) fun s₁ w₁ => ?_
  have hf : Frame [reg32 Dd 200] s.mem s₁.mem := by
    rw [w₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (reg_contains E.fitD (by omega))
  have g : ∀ r, r ≠ .eax → s₁.gpr r = s.gpr r := fun r hr => w₁.gpr r (nm1 hr)
  refine WP.mono (chiHalf_ok x y 4 hx hy (.inr rfl) hdst (rc := rc) s₁ (w₁.wr ▸ E) (by rw [g _ hdst.ne.1, hd])
    (by rw [g _ (by decide), hW]) (by rw [g _ (by decide), hP])
    (fun x' hx' => by
      have := cOff_lt x' hx'
      rw [work_frame hf E.fitW this.1 (by omega) (by simpa using E.dw.symm)]; exact hb x' hx')
    (by rw [rd64_frame hf (by simpa using E.pd) E.fitP (by omega)]; exact hrc)) fun s₂ w₂ =>
      ⟨fun r hr => by rw [w₂.gpr r hr, w₁.gpr r hr], ?_, w₂.rd.trans w₁.rd, w₂.wr.trans w₁.wr⟩
  rw [w₂.mem, w₁.mem, half_lo, half_hi]; rfl

/-- After `k` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (K : KState) (rc : Lane) (Dd W : BitVec 32) (y k : Nat) (s : State) :
    Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [reg32 Dd 200] s₀.mem s.mem
  lanes : ∀ j < 5 * y + k, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) {dst : Reg} (hdst : Ptr dst) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd W P) (hd : s₀.gpr dst = Dd)
    (hW : s₀.gpr .edi = W) (hP : s₀.gpr .ebp = P) (hb : ∀ x < 5, rd64 s₀.mem W (cOff x) = B K x y)
    (hrc : rd64 s₀.mem P 0 = rc) (hl : ∀ j < 5 * y, rd64 s₀.mem Dd (8 * j) = out K rc (j % 5) (j / 5)) :
    WP isa (.block ((List.range 5).flatMap fun x => chi dst x y)) s₀ (ChiInv s₀ K rc Dd W y 5) := by
  have fD := E.fitD
  refine wp_range_flatMap (M := isa) (ChiInv s₀ K rc Dd W y) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => hl j (by omega)⟩
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  refine WP.mono (chi_ok x y hx hy hdst (rc := rc) s (hI.wr ▸ E) (by rw [hI.gpr _ (nm1 hdst.ne.1), hd])
    (by rw [hI.gpr _ (by decide), hW]) (by rw [hI.gpr _ (by decide), hP])
    (fun x' hx' => by
      have := cOff_lt x' hx'
      rw [work_frame hI.frame E.fitW this.1 (by omega) (by simpa using E.dw.symm)]; exact hb x' hx')
    (by rw [rd64_frame hI.frame (by simpa using E.pd) E.fitP (by omega)]; exact hrc))
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun j hj => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (reg_contains fD (by omega))
      (reg_contains fD (by omega)) _
  · rw [w.mem]
    by_cases e : j = x + 5 * y
    · subst e
      rw [rd64_write64_self _ _ (by omega), show (x + 5 * y) % 5 = x by omega,
        show (x + 5 * y) / 5 = y by omega]
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.lanes j (by omega)

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (K : KState) (rc : Lane) (Dd W : BitVec 32) (y : Nat) (s : State) :
    Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .edx, .ecx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [reg32 Dd 200, workR W] s₀.mem s.mem
  ds : ∀ x < 5, rd64 s.mem W (dOff x) = D K x
  lanes : ∀ j < 5 * y, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem planes_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd W P) (hS : s₀.gpr src = S)
    (hd : s₀.gpr dst = Dd) (hW : s₀.gpr .edi = W) (hP : s₀.gpr .ebp = P) (hK : Lanes32 s₀.mem S K)
    (hrc : rd64 s₀.mem P 0 = rc) (s : State) (hs : PInv s₀ K rc Dd W 0 s) :
    WP isa (.block ((List.range 5).flatMap (plane src dst))) s (PInv s₀ K rc Dd W 5) := by
  have fD := E.fitD
  refine wp_range_flatMap (M := isa) (PInv s₀ K rc Dd W) (fun y s hy hI => ?_) 5 (Nat.le_refl _) s hs
  unfold plane
  rw [WP.block_append_iff]
  obtain ⟨se, sd, sc, -⟩ := hsrc.ne
  obtain ⟨de, dd, dc, -⟩ := hdst.ne
  have E' : Env s.wr S Dd W P := hI.wr ▸ E
  refine WP.mono (laneBs_ok y hy hsrc s E' (by rw [hI.gpr _ (nm3 se sd sc), hS])
    (by rw [hI.gpr _ (by decide), hW]) (hK.frame hI.frame (by simpa using ⟨E.sd, E.sw⟩) E.fitS) hI.ds)
    fun s₁ b₁ => ?_
  have E₁ : Env s₁.wr S Dd W P := b₁.wr ▸ E'
  have f₁ : Frame [reg32 Dd 200, workR W] s₀.mem s₁.mem :=
    hI.frame.trans (b₁.frame.mono (by simp))
  refine WP.mono (chis_ok y hy hdst (rc := rc) s₁ E₁ (by rw [b₁.gpr _ (nm3 de dd dc), hI.gpr _ (nm3 de dd dc), hd])
    (by rw [b₁.gpr _ (by decide), hI.gpr _ (by decide), hW])
    (by rw [b₁.gpr _ (by decide), hI.gpr _ (by decide), hP]) b₁.bs
    (by rw [rd64_frame f₁ (by simpa using ⟨E.pd, E.pw⟩) E.fitP (by omega)]; exact hrc)
    (fun j hj => by
      rw [rd64_frame b₁.frame (by simpa using E.dw) fD (by omega)]; exact hI.lanes j hj))
    fun s₂ c₂ => ⟨fun r hr => ?_, by rw [c₂.rd, b₁.rd, hI.rd], by rw [c₂.wr, b₁.wr, hI.wr],
      f₁.trans (c₂.frame.mono (by simp)), fun x hx => ?_, fun j hj => c₂.lanes j (by omega)⟩
  · have ⟨a, b, c⟩ : r ≠ .eax ∧ r ≠ .edx ∧ r ≠ .ecx := by simpa using hr
    rw [c₂.gpr r (nm1 a), b₁.gpr r hr, hI.gpr r hr]
  · have := dOff_lt x hx
    rw [work_frame c₂.frame E.fitW (by omega) this.2 (by simpa using E.dw.symm)]; exact b₁.ds x hx

/-! ## The round -/

theorem round_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S)
    (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P) (hK : Lanes32 s.mem S K)
    (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (round src dst)) s fun s' =>
      Lanes32 s'.mem Dd (outState K rc) ∧ Frame [reg32 Dd 200, workR W] s.mem s'.mem ∧
      s'.gpr .ebp = P + 8 ∧ (∀ r, r ∉ [Reg.eax, .edx, .ecx, .ebp] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold round
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok hsrc s E hS hW hK) fun s₁ c₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dcols_ok s₁ (c₁.wr ▸ E) (by rw [c₁.gpr _ (by decide), hW]) c₁.cs) fun s₂ d₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (planes_ok hsrc hdst s E hS hd hW hP hK hrc s₂ ⟨fun r hr => ?_,
    by rw [d₂.rd, c₁.rd], by rw [d₂.wr, c₁.wr], (c₁.frame.trans d₂.frame).mono (by simp), d₂.ds,
    fun j hj => absurd hj (by omega)⟩) fun s₃ p₃ => ?_
  · have a : r ≠ .eax := by rintro rfl; simp at hr
    rw [d₂.gpr r hr, c₁.gpr r (nm1 a)]
  refine wp_addi fun s₄ u₄ => WP.block_nil ⟨fun i hi => ?_, by rw [u₄.mem]; exact p₃.frame,
    by rw [u₄.gpr, p₃.gpr _ (by decide), hP], fun r hr => ?_, by rw [u₄.rd, p₃.rd],
    by rw [u₄.wr, p₃.wr]⟩
  · rw [u₄.mem, p₃.lanes i (by omega)]
    simp [outState, hi]
  · have ⟨a, b, c, e⟩ : r ≠ .eax ∧ r ≠ .edx ∧ r ≠ .ecx ∧ r ≠ .ebp := by simpa using hr
    rw [u₄.other r e, p₃.gpr r (nm3 a b c)]

end VG.Proof.Sha3.X86
