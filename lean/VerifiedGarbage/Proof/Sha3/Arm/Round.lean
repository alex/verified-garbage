import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Impl.Sha3.Arm

/-!
# Keccak-f[1600] on ARMv7: one round

Untrusted: everything here is checked by Lean. One round (`round src dst`)
from the state at `src` to the state at `dst`, lane by lane
(`Proof.Sha3.out`), each lane a pair of 32-bit halves (as the SHA-512 proof
handles them: `VG.Proof.Sha512.Arm`), proved once for both of the rounds of
an iteration (`src`, `dst` being `r0`, `r1` or `r1`, `r0`).
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Impl.Sha512.Arm (lo hi ld st sig Op)
open VG.Proof.Sha512.Arm (Only Wrote Pair rd64 write64 A Reg64 wp_ld wp_st wp_sig wp_eor mem_rd
  A_eq rd64_write64_self rd64_write64_ne frame_write64 contains_A lo_xor hi_xor lo_and hi_and
  lo_rd64 hi_rd64 evalOps)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd wp_mov wp_and wp_ldr wp_str wp_add op2_reg op2_imm)
open VG.Proof.Sha3 (C D B out outState)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## Registers -/

/-- The pointer registers, which a round never writes. -/
def Ptr (r : Reg) : Prop := r ∈ [Reg.r0, .r1]

/-- The registers the columns write. -/
def colRegs : List Reg := [cl 0, ch 0, cl 1, ch 1, cl 2, ch 2, cl 3, ch 3, cl 4, ch 4, T1]

theorem cl_inj : ∀ x < 5, ∀ x' < 5, cl x = cl x' → x = x' := by decide
theorem ch_inj : ∀ x < 5, ∀ x' < 5, ch x = ch x' → x = x' := by decide
theorem cl_ch : ∀ x < 5, ∀ x' < 5, cl x ≠ ch x' := by decide
theorem cl_T : ∀ x < 5, cl x ≠ T1 ∧ cl x ≠ T2 ∧ ch x ≠ T1 ∧ ch x ≠ T2 := by decide
theorem T12 : T1 ≠ T2 := by decide
theorem ptr_cl : ∀ r ∈ [Reg.r0, .r1], ∀ x < 5, cl x ≠ r ∧ ch x ≠ r := by decide
theorem ptr_T : ∀ r ∈ [Reg.r0, .r1], T1 ≠ r ∧ T2 ≠ r := by decide
theorem ptr_col : ∀ r ∈ [Reg.r0, .r1], r ∉ colRegs := by decide
theorem col_mono : ∀ x < 5, ∀ r ∈ colRegs ++ [cl x, ch x, T1], r ∈ colRegs := by decide

/-- The registers the planes write. -/
def bRegs : List Reg := [cl 0, ch 0, cl 1, ch 1, cl 2, ch 2, cl 3, ch 3, cl 4, ch 4, T1, T2]

theorem ptr_b : ∀ r ∈ [Reg.r0, .r1], r ∉ bRegs := by decide
theorem b_mono : ∀ x < 5, ∀ r ∈ bRegs ++ [T1, T2, cl x, ch x], r ∈ bRegs := by decide

theorem Ptr.cl {r : Reg} (h : Ptr r) {x : Nat} (hx : x < 5) : cl x ≠ r ∧ ch x ≠ r := ptr_cl r h x hx

theorem Ptr.T {r : Reg} (h : Ptr r) : T1 ≠ r ∧ T2 ≠ r := ptr_T r h

theorem cl_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : cl x' ≠ cl x :=
  fun e => h (cl_inj x' hx' x hx e)

theorem ch_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : ch x' ≠ ch x :=
  fun e => h (ch_inj x' hx' x hx e)

theorem nm2 {r a b : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) : r ∉ [a, b] := by simp [h₁, h₂]
theorem nm3 {r a b c : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) (h₃ : r ≠ c) : r ∉ [a, b, c] := by
  simp [h₁, h₂, h₃]
theorem nm4 {r a b c d : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) (h₃ : r ≠ c) (h₄ : r ≠ d) :
    r ∉ [a, b, c, d] := by simp [h₁, h₂, h₃, h₄]

/-! ## States in memory -/

/-- The state at `b` holds `K`, lane `i` as the pair of words at `b + 8i`. -/
def Lanes32 (m : Mem) (b : BitVec 32) (K : KState) : Prop := ∀ i < 25, rd64 m b (8 * i) = K[i]!

/-- The 32-bit region of `n` bytes at `b`. -/
abbrev regR (b : BitVec 32) (n : Nat) : Region := ⟨State.addr b, n⟩

/-- Where a round reads and writes: the state at `S`, the pointer at
`Sc + rcPtr` to the round constant, the round constant at `P`, and the state
at `Dd`, which overlaps none of them. -/
structure Env (wr : List Region) (S Dd Sc P : BitVec 32) : Prop where
  fitS : S.toNat + 200 ≤ 2 ^ 32
  fitD : Dd.toNat + 200 ≤ 2 ^ 32
  wS : Reg64 wr S 200
  wD : Reg64 wr Dd 200
  ptr_in : InRegions wr (A Sc rcPtr) 4
  rc_in : ∀ o, o = 0 ∨ o = 4 → InRegions wr (A P o) 4
  src_dst : Region.Disjoint (regR S 200) (regR Dd 200)
  ptr_dst : Region.Disjoint ⟨A Sc rcPtr, 4⟩ (regR Dd 200)
  rc_dst : ∀ o, o = 0 ∨ o = 4 → Region.Disjoint ⟨A P o, 4⟩ (regR Dd 200)

theorem Env.src {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') {i : Nat} (hi : i < 25) : rd64 m' S (8 * i) = rd64 m S (8 * i) :=
  VG.Proof.Sha512.Arm.rd64_frame hf (by simpa using E.src_dst) E.fitS (by omega)

theorem Env.ptr {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') : m'.readW (A Sc rcPtr) 32 = m.readW (A Sc rcPtr) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using E.ptr_dst) (by decide)

theorem Env.rc {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') {o : Nat} (ho : o = 0 ∨ o = 4) :
    m'.readW (A P o) 32 = m.readW (A P o) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using E.rc_dst o ho) (by decide)

theorem Env.dst_contains {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {o : Nat}
    (ho : o + 4 ≤ 200) : (regR Dd 200).Contains (A Dd o) (32 / 8) :=
  contains_A E.fitD ho

/-! ## θ -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `(l, h) ^=` the lane at `[b, #off]`. -/
theorem wp_ldx {l h b : Reg} {B' : BitVec 32} {off : Nat} {v : Lane} (hlT : l ≠ T1) (hhT : h ≠ T1)
    (hbT : b ≠ T1) (hbl : b ≠ l) (hlh : l ≠ h) (ho : off + 4 < 4096) (hb : s.gpr b = B')
    (hi : InRegions s.wr (A B' off) 4) (hi' : InRegions s.wr (A B' (off + 4)) 4) (hp : Pair s l h v)
    (k : ∀ s', Only [T1, l, h] s s' → Pair s' l h (v ^^^ rd64 s.mem B' off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ldx l h b off ++ rest)) s Q := by
  simp only [ldx, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (by rw [hb]) (mem_rd hi) fun s₁ u₁ => ?_
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_ldr ho (by rw [u₂.other b hbl, u₁.other b hbT, hb])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd hi') fun s₃ u₃ => ?_
  refine wp_eor (op2_reg _ _) fun s₄ u₄ => k s₄ ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans
    (Only.of_upd u₃)).trans (Only.of_upd u₄) |>.mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other l hlh, u₃.other l hlT, u₂.gpr, u₁.other l hlT, u₁.gpr, hp.1, lo_xor, lo_rd64]
  · rw [u₄.gpr, u₃.gpr, u₃.other h hhT, u₂.other h (Ne.symm hlh), u₁.other h hhT,
      u₂.mem, u₁.mem, hp.2, hi_xor, hi_rd64]

theorem wp_ldx' {l h b : Reg} {B' : BitVec 32} {off : Nat} {v : Lane} (hlT : l ≠ T1) (hhT : h ≠ T1)
    (hbT : b ≠ T1) (hbl : b ≠ l) (hlh : l ≠ h) (ho : off + 4 < 4096) (hb : s.gpr b = B')
    (hi : InRegions s.wr (A B' off) 4) (hi' : InRegions s.wr (A B' (off + 4)) 4) (hp : Pair s l h v)
    (k : ∀ s', Only [T1, l, h] s s' → Pair s' l h (v ^^^ rd64 s.mem B' off) → Q s') :
    WP isa (.block (ldx l h b off)) s Q := by
  rw [← List.append_nil (ldx l h b off)]
  exact wp_ldx hlT hhT hbT hbl hlh ho hb hi hi' hp fun s' o p => WP.block_nil (k s' o p)

end

theorem column_ok (x : Nat) (hx : x < 5) {src : Reg} (hsrc : Ptr src) {S : BitVec 32} {K : KState}
    (s : State) (h0 : s.gpr src = S) (hR : Reg64 s.wr S 200) (hK : Lanes32 s.mem S K) :
    WP isa (.block (column src x)) s fun s' =>
      Only [cl x, ch x, T1] s s' ∧ Pair s' (cl x) (ch x) (C K x) := by
  obtain ⟨hlT, -, hhT, -⟩ := cl_T x hx
  obtain ⟨hsl, hsh⟩ := hsrc.cl hx
  have hsT := hsrc.T.1
  have hlh : cl x ≠ ch x := cl_ch x hx x hx
  unfold column
  refine wp_ld hsl hlh (by omega) h0 (hR _ (by omega)).1 (hR _ (by omega)).2 fun s₁ o₁ p₁ => ?_
  have g : ∀ t : State, Only [cl x, ch x, T1] s t → t.gpr src = S ∧ t.wr = s.wr ∧ t.mem = s.mem :=
    fun t o => ⟨by rw [o.gpr src (nm3 hsl.symm hsh.symm hsT.symm), h0], o.wr, o.mem⟩
  have o₁' : Only [cl x, ch x, T1] s s₁ := o₁.mono (by simp)
  obtain ⟨a₁, w₁, m₁⟩ := g s₁ o₁'
  refine wp_ldx hlT hhT hsT.symm hsl.symm hlh (by omega) a₁ (by rw [w₁]; exact (hR _ (by omega)).1)
    (by rw [w₁]; exact (hR _ (by omega)).2) p₁ fun s₂ o₂ p₂ => ?_
  have o₂' : Only [cl x, ch x, T1] s s₂ := (o₁'.trans o₂).mono (by simp)
  obtain ⟨a₂, w₂, m₂⟩ := g s₂ o₂'
  refine wp_ldx hlT hhT hsT.symm hsl.symm hlh (by omega) a₂ (by rw [w₂]; exact (hR _ (by omega)).1)
    (by rw [w₂]; exact (hR _ (by omega)).2) p₂ fun s₃ o₃ p₃ => ?_
  have o₃' : Only [cl x, ch x, T1] s s₃ := (o₂'.trans o₃).mono (by simp)
  obtain ⟨a₃, w₃, m₃⟩ := g s₃ o₃'
  refine wp_ldx hlT hhT hsT.symm hsl.symm hlh (by omega) a₃ (by rw [w₃]; exact (hR _ (by omega)).1)
    (by rw [w₃]; exact (hR _ (by omega)).2) p₃ fun s₄ o₄ p₄ => ?_
  have o₄' : Only [cl x, ch x, T1] s s₄ := (o₃'.trans o₄).mono (by simp)
  obtain ⟨a₄, w₄, m₄⟩ := g s₄ o₄'
  refine wp_ldx' hlT hhT hsT.symm hsl.symm hlh (by omega) a₄ (by rw [w₄]; exact (hR _ (by omega)).1)
    (by rw [w₄]; exact (hR _ (by omega)).2) p₄ fun s₅ o₅ p₅ => ⟨(o₄'.trans o₅).mono (by simp), ?_⟩
  rw [m₁, m₂, m₃, m₄, hK x (by omega), hK (x + 5) (by omega), hK (x + 10) (by omega),
    hK (x + 15) (by omega), hK (x + 20) (by omega)] at p₅
  exact p₅

/-- After the first `k` columns. -/
def ColInv (s₀ : State) (K : KState) (k : Nat) (s : State) : Prop :=
  Only colRegs s₀ s ∧ ∀ x < k, Pair s (cl x) (ch x) (C K x)

theorem columns_ok {src : Reg} (hsrc : Ptr src) {S : BitVec 32} {K : KState} (s₀ : State)
    (h0 : s₀.gpr src = S) (hR : Reg64 s₀.wr S 200) (hK : Lanes32 s₀.mem S K) :
    WP isa (.block ((List.range 5).flatMap (column src))) s₀ (ColInv s₀ K 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ K) (fun x s hx ⟨ho, hc⟩ => ?_) 5 le_rfl s₀
    ⟨Only.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx hsrc (K := K) s (by rw [ho.gpr src (ptr_col src hsrc), h0])
    (by rw [ho.wr]; exact hR) (by rw [ho.mem]; exact hK)) fun s' ⟨o, p⟩ =>
      ⟨(ho.trans o).mono (col_mono x hx), fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact p
  · have hx'5 : x' < 5 := by omega
    exact (hc x' (by omega)).of_only o
      (nm3 (cl_ne hx hx'5 e) (cl_ch x' hx'5 x hx) (cl_T x' hx'5).1)
      (nm3 (fun h => cl_ch x hx x' hx'5 h.symm) (ch_ne hx hx'5 e) (cl_T x' hx'5).2.2.1)

/-! ## D -/

theorem evalOps_rotr (v : Lane) (n : Nat) : evalOps v [.rotr n] = v.rotateRight n := by
  simp [evalOps, VG.Impl.Sha512.Arm.Op.eval]

theorem dOff_lt (x : Nat) (hx : x < 5) : dOff x + 8 ≤ 200 := by simp only [dOff]; omega

theorem dcol_ok (x : Nat) (hx : x < 5) {dst : Reg} (hdst : Ptr dst) {Dd : BitVec 32} {K : KState}
    (s : State) (hd : s.gpr dst = Dd) (hR : Reg64 s.wr Dd 200)
    (hc : ∀ x' < 5, Pair s (cl x') (ch x') (C K x')) :
    WP isa (.block (dcol dst x)) s fun s' => Wrote [T1, T2] s s' (write64 s.mem Dd (dOff x) (D K x)) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  obtain ⟨l1T1, l1T2, h1T1, h1T2⟩ := cl_T _ h1
  obtain ⟨l4T1, l4T2, h4T1, h4T2⟩ := cl_T _ h4
  have hdo := dOff_lt x hx
  unfold dcol
  refine wp_sig (by simp) (by decide) T12 l1T1 h1T1 l1T2 h1T2 (hc _ h1) fun s₁ o₁ p₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  rw [← List.append_nil (st T1 T2 dst (dOff x))]
  have hd₃ : s₃.gpr dst = Dd := by
    rw [u₃.other dst hdst.T.2.symm, u₂.other dst hdst.T.1.symm,
      o₁.gpr dst (nm2 hdst.T.1.symm hdst.T.2.symm), hd]
  have hw₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, o₁.wr]
  refine wp_st (x := D K x) (by omega) hd₃ ⟨?_, ?_⟩ (by rw [hw₃]; exact (hR _ hdo).1)
    (by rw [hw₃]; exact (hR _ hdo).2) fun s₄ u₄ => WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other T1 T12, u₂.gpr, p₁.1, o₁.gpr (cl _) (nm2 l4T1 l4T2), (hc _ h4).1, evalOps_rotr, D,
      lo_xor]
  · rw [u₃.gpr, u₂.other T2 T12.symm, u₂.other _ h4T1, p₁.2, o₁.gpr (ch _) (nm2 h4T1 h4T2),
      (hc _ h4).2, evalOps_rotr, D, hi_xor]
  · have ⟨a, b⟩ : r ≠ T1 ∧ r ≠ T2 := by simpa using hr
    rw [u₄.gpr, u₃.other r b, u₂.other r a, o₁.gpr r hr]
  · rw [u₄.mem, u₃.mem, u₂.mem, o₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, o₁.rd]
  · rw [u₄.wr, hw₃]
  · rw [u₄.sp, u₃.sp, u₂.sp, o₁.sp]

/-- After the first `k` of the `D[x]`. -/
structure DInv (s₀ : State) (K : KState) (Dd : BitVec 32) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [T1, T2] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR Dd 200] s₀.mem s.mem
  dl : ∀ x < k, rd64 s.mem Dd (dOff x) = D K x

theorem dcols_ok {dst : Reg} (hdst : Ptr dst) {Dd : BitVec 32} {K : KState} (s₀ : State)
    (hd : s₀.gpr dst = Dd) (fitD : Dd.toNat + 200 ≤ 2 ^ 32) (hR : Reg64 s₀.wr Dd 200)
    (hc : ∀ x < 5, Pair s₀ (cl x) (ch x) (C K x)) :
    WP isa (.block ((List.range 5).flatMap (dcol dst))) s₀ (DInv s₀ K Dd 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ K Dd) (fun x s hx hI => ?_) 5 le_rfl s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hdo := dOff_lt x hx
  refine WP.mono (dcol_ok x hx hdst (K := K) s (by rw [hI.gpr dst (nm2 hdst.T.1.symm hdst.T.2.symm), hd])
    (by rw [hI.wr]; exact hR) fun x' hx' => ⟨?_, ?_⟩) fun s' w => ⟨fun r hr => by
      rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, w.sp.trans hI.sp, ?_, ?_⟩
  · rw [hI.gpr _ (nm2 (cl_T x' hx').1 (cl_T x' hx').2.1)]; exact (hc x' hx').1
  · rw [hI.gpr _ (nm2 (cl_T x' hx').2.2.1 (cl_T x' hx').2.2.2)]; exact (hc x' hx').2
  · rw [w.mem]; exact frame_write64 hI.frame (List.mem_singleton_self _) fitD hdo _
  · intro x' hx'
    rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by have := dOff_lt x' (by omega); omega)
        (by simp only [dOff]; omega)]
      exact hI.dl x' (by omega)

/-! ## A plane -/

theorem rhoOff_ne32 : ∀ j < 25, rhoOff j ≠ 32 := by decide

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) {src dst : Reg} (hsrc : Ptr src)
    (hdst : Ptr dst) {S Dd : BitVec 32} {K : KState} (s : State) (h0 : s.gpr src = S)
    (hd : s.gpr dst = Dd) (hRS : Reg64 s.wr S 200) (hRD : Reg64 s.wr Dd 200)
    (hK : Lanes32 s.mem S K) (hD : ∀ x' < 5, rd64 s.mem Dd (dOff x') = D K x') :
    WP isa (.block (laneB src dst x y)) s fun s' =>
      Only [T1, T2, cl x, ch x] s s' ∧ Pair s' (cl x) (ch x) (B K x y) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  have hko := dOff_lt _ hk
  obtain ⟨lT1, lT2, hT1, hT2⟩ := cl_T x hx
  obtain ⟨sT1, sT2⟩ := hsrc.T
  obtain ⟨dT1, dT2⟩ := hdst.T
  unfold laneB
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (a := A S (8 * piSrc x y)) (by omega) (by rw [h0]) (mem_rd (hRS _ (by omega)).1)
    fun s₁ u₁ => ?_
  refine wp_ldr (a := A Dd (dOff ((x + 3 * y) % 5))) (by omega) (by rw [u₁.other dst dT1.symm, hd])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hRD _ hko).1) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldr (a := A S (8 * piSrc x y + 4)) (by omega)
    (by rw [u₃.other src sT1.symm, u₂.other src sT2.symm, u₁.other src sT1.symm, h0])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hRS _ (by omega)).2)
    fun s₄ u₄ => ?_
  refine wp_ldr (a := A Dd (dOff ((x + 3 * y) % 5) + 4)) (by omega)
    (by rw [u₄.other dst dT2.symm, u₃.other dst dT1.symm, u₂.other dst dT2.symm,
      u₁.other dst dT1.symm, hd])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hRD _ hko).2)
    fun s₅ u₅ => ?_
  refine wp_eor (op2_reg _ _) fun s₆ u₆ => ?_
  have o₆ : Only [T1, T2, cl x, ch x] s s₆ := ((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans
    (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).mono
    (by simp)
  have p₆ : Pair s₆ T1 T2 (K[piSrc x y]! ^^^ D K ((x + 3 * y) % 5)) := by
    constructor
    · rw [u₆.other T1 T12, u₅.other T1 lT1.symm, u₄.other T1 T12, u₃.gpr, u₂.other T1 T12, u₂.gpr,
        u₁.gpr, u₁.mem, lo_xor, ← hK _ hj, ← hD _ hk, lo_rd64, lo_rd64]
    · rw [u₆.gpr, u₅.gpr, u₅.other T2 lT2.symm, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hi_xor,
        ← hK _ hj, ← hD _ hk, hi_rd64, hi_rd64]
  unfold rot
  split
  · rename_i h
    refine wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
      WP.block_nil ⟨(o₆.trans (Only.of_upd u₇)).trans (Only.of_upd u₈) |>.mono (by simp), ?_, ?_⟩
    · rw [u₈.other (cl x) (cl_ch x hx x hx), u₇.gpr, p₆.1, B, Proof.Sha3.rotl, ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [u₈.gpr, u₇.other T2 lT2.symm, p₆.2, B, Proof.Sha3.rotl, ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rename_i h
    have h64 := Proof.Sha3.rhoOff_lt _ hj
    have h32 := rhoOff_ne32 _ hj
    rw [← List.append_nil (sig _ _ _ _ _)]
    refine wp_sig (by simp) (fun o ho => ?_) (cl_ch x hx x hx) lT1.symm lT2.symm hT1.symm hT2.symm p₆
      fun s₇ o₇ p₇ => WP.block_nil ⟨(o₆.trans o₇).mono (by simp), ?_⟩
    · simp only [List.mem_singleton] at ho
      subst ho
      simp only [VG.Impl.Sha512.Arm.Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      omega
    · rw [evalOps_rotr] at p₇
      rw [B, Proof.Sha3.rotl, ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact p₇

/-- `¬b ∧ c`, as the model computes it without `bic`. -/
theorem andNot (b c : Lane) : (b ^^^ 0xffffffffffffffff) &&& c = (b &&& c) ^^^ c := by
  have e : (0xffffffffffffffff : Lane) = BitVec.allOnes 64 := by decide
  rw [e]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_allOnes]
  cases b[i] <;> cases c[i] <;> rfl

/-- A half (`f`, `lo` or `hi`) of lane `(x, y)` of the output, from the
halves `r` of the lanes `B`. -/
theorem chiHalf_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) {dst : Reg} (hdst : Ptr dst)
    (r : Nat → Reg) (hr : ∀ x' < 5, r x' ≠ T1 ∧ r x' ≠ T2) (f : Lane → BitVec 32)
    (hfx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (hfa : ∀ a b, f (a &&& b) = f a &&& f b)
    {Dd Sc P : BitVec 32} {K : KState} {rc : Lane} {off o : Nat} (ho : o < 4096) (hoff : off < 4096)
    (s : State) (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc) (hout : InRegions s.wr (A Dd o) 4)
    (hb : ∀ x' < 5, s.gpr (r x') = f (B K x' y))
    (hrc : x = 0 ∧ y = 0 → InRegions (s.rd ++ s.wr) (A Sc rcPtr) 4 ∧
      s.mem.readW (A Sc rcPtr) 32 = P ∧ InRegions (s.rd ++ s.wr) (A P off) 4 ∧
      s.mem.readW (A P off) 32 = f rc) :
    WP isa (.block (chiHalf dst r x y off o)) s fun s' =>
      Wrote [T1, T2] s s' (s.mem.writeW (A Dd o) (f (out K rc x y))) := by
  have h1' : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2' : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold chiHalf
  simp only [List.cons_append, List.nil_append]
  refine wp_and (op2_reg _ _) fun s₁ u₁ => wp_eor (op2_reg _ _) fun s₂ u₂ =>
    wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have hT : s₃.gpr T1 = f ((B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^
      B K x y) := by
    rw [u₃.gpr, u₂.gpr, u₂.other (r x) (hr x hx).1, u₁.gpr, u₁.other (r ((x + 2) % 5)) (hr _ h2').1,
      u₁.other (r x) (hr x hx).1, hb _ h1', hb _ h2', hb x hx, andNot, hfx, hfx, hfa]
  have fin : ∀ s₄ : State, (∀ q, q ≠ T1 → q ≠ T2 → s₄.gpr q = s.gpr q) →
      s₄.gpr T1 = f (out K rc x y) → s₄.mem = s.mem → s₄.rd = s.rd → s₄.wr = s.wr → s₄.sp = s.sp →
      WP isa (.block [.str T1 dst o]) s₄ fun s' =>
        Wrote [T1, T2] s s' (s.mem.writeW (A Dd o) (f (out K rc x y))) :=
    fun s₄ g₄ v₄ m₄ r₄ w₄ p₄ => by
      refine wp_str ho (by rw [g₄ dst hdst.T.1.symm hdst.T.2.symm, hd]) (by rw [w₄]; exact hout)
        fun s₅ u₅ => WP.block_nil ⟨fun q hq => ?_, by rw [u₅.mem, m₄, v₄], by rw [u₅.rd, r₄],
          by rw [u₅.wr, w₄], by rw [u₅.sp, p₄]⟩
      have ⟨a, b⟩ : q ≠ T1 ∧ q ≠ T2 := by simpa using hq
      rw [u₅.gpr, g₄ q a b]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have g₃ : ∀ q, q ≠ T1 → s₃.gpr q = s.gpr q := fun q hq => by
    rw [u₃.other q hq, u₂.other q hq, u₁.other q hq]
  by_cases h0 : x = 0 ∧ y = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    simp only [List.cons_append, List.nil_append]
    obtain ⟨i1, e1, i2, e2⟩ := hrc h0
    refine wp_ldr (a := A Sc rcPtr) (by decide) (by rw [g₃ .r1 (by decide), h1])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i1) fun s₄ u₄ => ?_
    refine wp_ldr (a := A P off) hoff (by rw [u₄.gpr, m₃, e1])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i2) fun s₅ u₅ => ?_
    refine wp_eor (op2_reg _ _) fun s₆ u₆ => fin s₆ (fun q a b => ?_) ?_ (by
      rw [u₆.mem, u₅.mem, u₄.mem, m₃]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    · rw [u₆.other q a, u₅.other q b, u₄.other q b, g₃ q a]
    · rw [u₆.gpr, u₅.other T1 T12, u₄.other T1 T12, u₅.gpr, u₄.mem, m₃, e2, hT, ← hfx, out]
      simp only [h0, and_self, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    simp only [List.nil_append]
    refine fin s₃ (fun q a _ => g₃ q a) ?_ m₃ (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr]) (by rw [u₃.sp, u₂.sp, u₁.sp])
    rw [hT, out]
    simp only [h0, ite_false]

theorem rc_lo {m : Mem} {P : BitVec 32} {rc : Lane} (h : rd64 m P 0 = rc) :
    m.readW (A P 0) 32 = lo rc := by rw [← h, lo_rd64]

theorem rc_hi {m : Mem} {P : BitVec 32} {rc : Lane} (h : rd64 m P 0 = rc) :
    m.readW (A P 4) 32 = hi rc := by rw [← h, hi_rd64]

theorem Env.rc64 {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') : rd64 m' P 0 = rd64 m P 0 := by
  simp only [rd64]
  rw [E.rc hf (o := 0 + 4) (.inr rfl), E.rc hf (.inl rfl)]

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) {dst : Reg} (hdst : Ptr dst)
    {S Dd Sc P : BitVec 32} {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd Sc P)
    (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc) (hP : s.mem.readW (A Sc rcPtr) 32 = P)
    (hrc : rd64 s.mem P 0 = rc) (hb : ∀ x' < 5, Pair s (cl x') (ch x') (B K x' y)) :
    WP isa (.block (chi dst x y)) s fun s' =>
      Wrote [T1, T2] s s' (write64 s.mem Dd (8 * (x + 5 * y)) (out K rc x y)) := by
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  unfold chi
  rw [WP.block_append_iff]
  refine WP.mono (chiHalf_ok x y hx hy hdst cl (fun x' hx' => ⟨(cl_T x' hx').1, (cl_T x' hx').2.1⟩)
    lo lo_xor lo_and (by omega) (by decide) s hd h1 (E.wD _ ho).1 (fun x' hx' => (hb x' hx').1)
    (fun _ => ⟨mem_rd E.ptr_in, hP, mem_rd (E.rc_in 0 (.inl rfl)), rc_lo hrc⟩)) fun s₁ w₁ => ?_
  have hf : Frame [regR Dd 200] s.mem s₁.mem := by
    rw [w₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (E.dst_contains (by omega))
  obtain ⟨dT1, dT2⟩ := hdst.T
  refine WP.mono (chiHalf_ok x y hx hy hdst ch
    (fun x' hx' => ⟨(cl_T x' hx').2.2.1, (cl_T x' hx').2.2.2⟩) hi hi_xor hi_and (by omega) (by decide)
    s₁ (by rw [w₁.gpr dst (nm2 dT1.symm dT2.symm), hd]) (by rw [w₁.gpr .r1 (by decide), h1])
    (by rw [w₁.wr]; exact (E.wD _ ho).2)
    (fun x' hx' => by
      rw [w₁.gpr _ (nm2 (cl_T x' hx').2.2.1 (cl_T x' hx').2.2.2)]; exact (hb x' hx').2)
    (fun _ => ⟨by rw [w₁.rd, w₁.wr]; exact mem_rd E.ptr_in, by rw [E.ptr hf, hP],
      by rw [w₁.rd, w₁.wr]; exact mem_rd (E.rc_in 4 (.inr rfl)), by rw [E.rc hf (.inr rfl), rc_hi hrc]⟩))
    fun s₂ w₂ => ⟨fun q hq => by rw [w₂.gpr q hq, w₁.gpr q hq], by rw [w₂.mem, w₁.mem]; rfl,
      w₂.rd.trans w₁.rd, w₂.wr.trans w₁.wr, w₂.sp.trans w₁.sp⟩

/-- After `k` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (K : KState) (rc : Lane) (Dd : BitVec 32) (y k : Nat) (s : State) :
    Prop where
  gpr : ∀ q, q ∉ [T1, T2] → s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR Dd 200] s₀.mem s.mem
  dl : y + 1 < 5 → ∀ x < 5, rd64 s.mem Dd (dOff x) = D K x
  lanes : ∀ j < 5 * y + k, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) {dst : Reg} (hdst : Ptr dst) {S Dd Sc P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd Sc P) (hd : s₀.gpr dst = Dd)
    (h1 : s₀.gpr .r1 = Sc) (hP : s₀.mem.readW (A Sc rcPtr) 32 = P) (hrc : rd64 s₀.mem P 0 = rc)
    (hb : ∀ x < 5, Pair s₀ (cl x) (ch x) (B K x y))
    (hdl : y + 1 < 5 → ∀ x < 5, rd64 s₀.mem Dd (dOff x) = D K x)
    (hl : ∀ j < 5 * y, rd64 s₀.mem Dd (8 * j) = out K rc (j % 5) (j / 5)) :
    WP isa (.block ((List.range 5).flatMap fun x => chi dst x y)) s₀ (ChiInv s₀ K rc Dd y 5) := by
  have fD := E.fitD
  obtain ⟨dT1, dT2⟩ := hdst.T
  refine wp_range_flatMap (M := isa) (ChiInv s₀ K rc Dd y) (fun x s hx hI => ?_) 5 le_rfl s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, hdl, fun j hj => hl j (by omega)⟩
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  refine WP.mono (chi_ok x y hx hy hdst s (hI.wr ▸ E) (by rw [hI.gpr dst (nm2 dT1.symm dT2.symm), hd])
    (by rw [hI.gpr .r1 (by decide), h1]) (by rw [E.ptr hI.frame, hP]) (by rw [E.rc64 hI.frame, hrc])
    (fun x' hx' => ⟨by rw [hI.gpr _ (nm2 (cl_T x' hx').1 (cl_T x' hx').2.1)]; exact (hb x' hx').1,
      by rw [hI.gpr _ (nm2 (cl_T x' hx').2.2.1 (cl_T x' hx').2.2.2)]; exact (hb x' hx').2⟩))
    fun s' w => ⟨fun q hq => by rw [w.gpr q hq, hI.gpr q hq], w.rd.trans hI.rd, w.wr.trans hI.wr,
      w.sp.trans hI.sp, ?_, fun hy' x' hx' => ?_, fun j hj => ?_⟩
  · rw [w.mem]; exact frame_write64 hI.frame (List.mem_singleton_self _) fD ho _
  · rw [w.mem, rd64_write64_ne _ _ (by omega) (by have := dOff_lt x' hx'; omega)
      (by simp only [dOff]; omega)]
    exact hI.dl hy' x' hx'
  · rw [w.mem]
    by_cases e : j = x + 5 * y
    · subst e
      rw [rd64_write64_self _ _ (by omega), show (x + 5 * y) % 5 = x by omega,
        show (x + 5 * y) / 5 = y by omega]
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.lanes j (by omega)

/-- After the first `k` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (K : KState) (y k : Nat) (s : State) : Prop :=
  Only bRegs s₀ s ∧ ∀ x < k, Pair s (cl x) (ch x) (B K x y)

theorem laneBs_ok (y : Nat) (hy : y < 5) {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst)
    {S Dd : BitVec 32} {K : KState} (s₀ : State) (h0 : s₀.gpr src = S) (hd : s₀.gpr dst = Dd)
    (hRS : Reg64 s₀.wr S 200) (hRD : Reg64 s₀.wr Dd 200) (hK : Lanes32 s₀.mem S K)
    (hD : ∀ x < 5, rd64 s₀.mem Dd (dOff x) = D K x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB src dst x y)) s₀ (BInv s₀ K y 5) := by
  refine wp_range_flatMap (M := isa) (BInv s₀ K y) (fun x s hx ⟨ho, hc⟩ => ?_) 5 le_rfl s₀
    ⟨Only.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (laneB_ok x y hx hy hsrc hdst (K := K) s (by rw [ho.gpr src (ptr_b src hsrc), h0])
    (by rw [ho.gpr dst (ptr_b dst hdst), hd]) (by rw [ho.wr]; exact hRS) (by rw [ho.wr]; exact hRD)
    (by rw [ho.mem]; exact hK) (by rw [ho.mem]; exact hD)) fun s' ⟨o, p⟩ =>
      ⟨(ho.trans o).mono (b_mono x hx), fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact p
  · have hx'5 : x' < 5 := by omega
    exact (hc x' (by omega)).of_only o
      (nm4 (cl_T x' hx'5).1 (cl_T x' hx'5).2.1 (cl_ne hx hx'5 e) (cl_ch x' hx'5 x hx))
      (nm4 (cl_T x' hx'5).2.2.1 (cl_T x' hx'5).2.2.2 (fun h => cl_ch x hx x' hx'5 h.symm)
        (ch_ne hx hx'5 e))

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (K : KState) (rc : Lane) (Dd : BitVec 32) (y : Nat) (s : State) :
    Prop where
  gpr : ∀ q ∈ [Reg.r0, .r1], s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR Dd 200] s₀.mem s.mem
  dl : y < 5 → ∀ x < 5, rd64 s.mem Dd (dOff x) = D K x
  lanes : ∀ j < 5 * y, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem planes_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd Sc P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd Sc P) (h0 : s₀.gpr src = S)
    (hd : s₀.gpr dst = Dd) (h1 : s₀.gpr .r1 = Sc) (hK : Lanes32 s₀.mem S K)
    (hP : s₀.mem.readW (A Sc rcPtr) 32 = P) (hrc : rd64 s₀.mem P 0 = rc) (s : State)
    (hs : PInv s₀ K rc Dd 0 s) :
    WP isa (.block ((List.range 5).flatMap (plane src dst))) s (PInv s₀ K rc Dd 5) := by
  refine wp_range_flatMap (M := isa) (PInv s₀ K rc Dd) (fun y s hy hI => ?_) 5 le_rfl s hs
  unfold plane
  rw [WP.block_append_iff]
  have E' : Env s.wr S Dd Sc P := hI.wr ▸ E
  refine WP.mono (laneBs_ok y hy hsrc hdst (K := K) s (by rw [hI.gpr src hsrc, h0])
    (by rw [hI.gpr dst hdst, hd]) E'.wS E'.wD (fun i hi => by rw [E.src hI.frame hi, hK i hi])
    (hI.dl hy)) fun s₁ ⟨o₁, b₁⟩ => ?_
  have E₁ : Env s₁.wr S Dd Sc P := o₁.wr ▸ E'
  refine WP.mono (chis_ok y hy hdst s₁ E₁ (by rw [o₁.gpr dst (ptr_b dst hdst), hI.gpr dst hdst, hd])
    (by rw [o₁.gpr .r1 (by decide), hI.gpr .r1 (by simp), h1]) (by rw [o₁.mem, E.ptr hI.frame, hP])
    (by rw [o₁.mem, E.rc64 hI.frame, hrc]) b₁ (fun hy' => by rw [o₁.mem]; exact hI.dl hy)
    (fun j hj => by rw [o₁.mem]; exact hI.lanes j hj)) fun s₂ h₂ => ⟨fun q hq => ?_,
      by rw [h₂.rd, o₁.rd, hI.rd], by rw [h₂.wr, o₁.wr, hI.wr], by rw [h₂.sp, o₁.sp, hI.sp],
      hI.frame.trans (o₁.mem ▸ h₂.frame), fun hy' => h₂.dl (by omega),
      fun j hj => h₂.lanes j (by omega)⟩
  obtain ⟨qT1, qT2⟩ := ptr_T q hq
  rw [h₂.gpr q (nm2 qT1.symm qT2.symm), o₁.gpr q (ptr_b q hq), hI.gpr q hq]

/-! ## The round -/

theorem rd64_writeW_disj (m : Mem) {Dd : BitVec 32} {a : Addr} (v : BitVec 32)
    (hd : Region.Disjoint ⟨a, 4⟩ (regR Dd 200)) (hfit : Dd.toNat + 200 ≤ 2 ^ 32) {o : Nat}
    (ho : o + 8 ≤ 200) : rd64 (m.writeW a v) Dd o = rd64 m Dd o := by
  simp only [rd64]
  rw [Mem.readW_writeW_sep (hd.symm.sep (contains_A hfit (by omega)) (Region.contains_self a 4))
    (by decide), Mem.readW_writeW_sep (hd.symm.sep (contains_A hfit (by omega))
    (Region.contains_self a 4)) (by decide)]

theorem round_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd Sc P : BitVec 32}
    {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd Sc P) (h0 : s.gpr src = S)
    (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc) (hK : Lanes32 s.mem S K)
    (hP : s.mem.readW (A Sc rcPtr) 32 = P) (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (round src dst)) s fun s' =>
      Lanes32 s'.mem Dd (outState K rc) ∧ Frame [regR Dd 200, ⟨A Sc rcPtr, 4⟩] s.mem s'.mem ∧
      s'.mem.readW (A Sc rcPtr) 32 = P + 8 ∧ (∀ q ∈ [Reg.r0, .r1], s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨dT1, dT2⟩ := hdst.T
  unfold round
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok hsrc (K := K) s h0 E.wS hK) fun s₁ ⟨o₁, c₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dcols_ok hdst s₁ (by rw [o₁.gpr dst (ptr_col dst hdst), hd]) E.fitD
    (by rw [o₁.wr]; exact E.wD) c₁) fun s₂ d₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (planes_ok hsrc hdst s E h0 hd h1 hK hP hrc s₂ ⟨fun q hq => ?_,
    by rw [d₂.rd, o₁.rd], by rw [d₂.wr, o₁.wr], by rw [d₂.sp, o₁.sp], by rw [← o₁.mem]; exact d₂.frame,
    fun _ => d₂.dl, fun j hj => absurd hj (by omega)⟩) fun s₃ p₃ => ?_
  · obtain ⟨qT1, qT2⟩ := ptr_T q hq
    rw [d₂.gpr q (nm2 qT1.symm qT2.symm), o₁.gpr q (ptr_col q hq)]
  have g₃ : s₃.gpr .r1 = Sc := by rw [p₃.gpr .r1 (by simp), h1]
  refine wp_ldr (a := A Sc rcPtr) (by decide) (by rw [g₃]) (by rw [p₃.rd, p₃.wr]; exact mem_rd E.ptr_in)
    fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_str (a := A Sc rcPtr) (by decide) (by rw [u₅.other .r1 (by decide), u₄.other .r1 (by decide), g₃])
    (by rw [u₅.wr, u₄.wr, p₃.wr]; exact E.ptr_in) fun s₆ u₆ =>
      WP.block_nil ⟨fun i hi => ?_, ?_, ?_, fun q hq => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, p₃.rd],
        by rw [u₆.wr, u₅.wr, u₄.wr, p₃.wr], by rw [u₆.sp, u₅.sp, u₄.sp, p₃.sp]⟩
  · rw [u₆.mem, rd64_writeW_disj _ _ E.ptr_dst E.fitD (by omega), u₅.mem, u₄.mem, p₃.lanes i (by omega)]
    simp [outState, hi]
  · rw [u₆.mem, u₅.mem, u₄.mem]
    exact (p₃.frame.mono (by simp)).writeW (r := ⟨A Sc rcPtr, 4⟩) (by simp) _ (Region.contains_self _ _)
  · rw [u₆.mem, Mem.readW_writeW_self32, u₅.gpr, u₄.gpr, E.ptr p₃.frame, hP]
  · obtain ⟨qT1, -⟩ := ptr_T q hq
    rw [u₆.gpr, u₅.other q qT1.symm, u₄.other q qT1.symm, p₃.gpr q hq]

end VG.Proof.Sha3.Arm
