import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Sha3.Arm.Round
import VerifiedGarbage.Proof.Sha3.Arm.Contract

/-!
# Keccak-f[1600] on ARMv7: the whole function

Untrusted: everything here is checked by Lean. The prologue saves the
callee-saved registers and stores the round constants in the scratch space;
each iteration of the loop runs two rounds (`round_ok`), from the state to
the second state in the scratch space and back; the epilogue restores the
registers.
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.Sha512.Arm (rd64 write64 A A_eq contains_A readW64 rd64_write64_self rd64_write64_ne
  rd64_write64_disj frame_write64 rd64_frame mem_rd wp_movw wp_movt Reg64)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd wp_add wp_sub wp_ldr wp_str wp_cmp op2_reg op2_imm eval_ne
  sub_beq readW_writeW_save)
open VG.Proof.Sha3 (outState_eq foldl_succ off_disjoint sub_offset add_zero')

/-! ## Addresses -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev scp : BitVec 32 := s₀.gpr .r1
abbrev A₀ : KState := stateAt s₀.mem (State.addr (stp s₀))

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : BitVec 32 := if r % 2 = 0 then stp s₀ else scp s₀
def oth (r : Nat) : BitVec 32 := if r % 2 = 0 then scp s₀ else stp s₀

/-- The address of the constant of round `r`. -/
abbrev rcp (r : Nat) : BitVec 32 := scp s₀ + BitVec.ofNat 32 (200 + 8 * r)

end

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = stp s₀ ∧ oth s₀ r = scp s₀) ∨ (cur s₀ r = scp s₀ ∧ oth s₀ r = stp s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem cur_even (s₀ : State) (t : Nat) : cur s₀ (2 * t) = stp s₀ ∧ oth s₀ (2 * t) = scp s₀ := by
  simp only [cur, oth]; split
  · exact ⟨rfl, rfl⟩
  · omega

theorem cur_odd (s₀ : State) (t : Nat) : cur s₀ (2 * t + 1) = scp s₀ ∧ oth s₀ (2 * t + 1) = stp s₀ := by
  simp only [cur, oth]; split
  · omega
  · exact ⟨rfl, rfl⟩

theorem A_add (b : BitVec 32) (a o : Nat) : A (b + BitVec.ofNat 32 a) o = A b (a + o) := by
  simp only [A]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rcp_succ (s₀ : State) (r : Nat) : rcp s₀ r + 8 = rcp s₀ (r + 1) := by
  simp only [rcp]
  bv_omega

theorem rd64_rcp (m : Mem) (s₀ : State) (r : Nat) : rd64 m (rcp s₀ r) 0 = rd64 m (scp s₀) (200 + 8 * r) := by
  simp only [rd64, rcp, A_add, Nat.zero_add, Nat.add_zero]

theorem rd64_congr {m m' : Mem} {b : BitVec 32} {o : Nat} (h1 : m'.readW (A b o) 32 = m.readW (A b o) 32)
    (h2 : m'.readW (A b (o + 4)) 32 = m.readW (A b (o + 4)) 32) : rd64 m' b o = rd64 m b o := by
  simp only [rd64]; rw [h1, h2]

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [regR (stp s₀) 200, regR (scp s₀) 512]
  disj : (regR (stp s₀) 200).Disjoint (regR (scp s₀) 512)
  fitS : (stp s₀).toNat + 200 ≤ 2 ^ 32
  fitC : (scp s₀).toNat + 512 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem scA {d : Nat} (hd : d < 512) : A (scp s₀) d = State.addr (scp s₀) + BitVec.ofNat 64 d :=
  A_eq (by have := h.fitC; omega)

theorem scr_in {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (scp s₀) d) 4 :=
  ⟨_, by rw [h.wr]; simp, contains_A h.fitC hd⟩

theorem scr_disj {a n b k : Nat} (ha : a + n ≤ 512) (hb : b + k ≤ 512) (hs : a + n ≤ b ∨ b + k ≤ a)
    (hn : 0 < n) (hk : 0 < k) : Region.Disjoint ⟨A (scp s₀) a, n⟩ ⟨A (scp s₀) b, k⟩ := by
  rw [h.scA (by omega), h.scA (by omega)]
  exact off_disjoint _ (by omega) (by omega) hs

theorem off_st {d n : Nat} (hd : d + n ≤ 512) (hn : 0 < n) :
    Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR (stp s₀) 200) := by
  have hs : Region.Sub ⟨A (scp s₀) d, n⟩ (regR (scp s₀) 512) := by
    rw [h.scA (by omega)]; exact sub_offset hd (by omega)
  exact h.disj.symm.sub_left hs

theorem off_scr {d n : Nat} (hd₀ : 200 ≤ d) (hd : d + n ≤ 512) (hn : 0 < n) :
    Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR (scp s₀) 200) := by
  have := off_disjoint (State.addr (scp s₀)) (a := d) (n := n) (b := 0) (k := 200) (by omega)
    (by omega) (.inr hd₀)
  rw [add_zero'] at this
  rw [h.scA (by omega)]; exact this

theorem off_dst {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {d n : Nat} (hd₀ : 200 ≤ d)
    (hd : d + n ≤ 512) (hn : 0 < n) : Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR Dd 200) := by
  rcases hD with rfl | rfl
  · exact h.off_st hd hn
  · exact h.off_scr hd₀ hd hn

theorem st_scr200 : (regR (stp s₀) 200).Disjoint (regR (scp s₀) 200) :=
  h.disj.sub_right (Region.sub_prefix (by omega))

theorem reg64_st : Reg64 s₀.wr (stp s₀) 200 :=
  VG.Proof.Sha512.Arm.Reg64.of_mem (by rw [h.wr]; simp) h.fitS

theorem reg64_scr : Reg64 s₀.wr (scp s₀) 200 := fun o ho =>
  ⟨h.scr_in (d := o) (by omega), h.scr_in (d := o + 4) (by omega)⟩

theorem env_of {S Dd : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    (hSD : (regR S 200).Disjoint (regR Dd 200)) {r : Nat} (hr : r < 24) :
    Env s₀.wr S Dd (scp s₀) (rcp s₀ r) := by
  have fS := h.fitS
  have fC := h.fitC
  refine ⟨?_, ?_, ?_, ?_, h.scr_in (d := rcPtr) (by decide), fun o ho => ?_, hSD,
    h.off_dst hD (d := rcPtr) (by decide) (by decide) (by decide), fun o ho => ?_⟩
  · rcases hS with rfl | rfl <;> omega
  · rcases hD with rfl | rfl <;> omega
  · rcases hS with rfl | rfl
    · exact h.reg64_st
    · exact h.reg64_scr
  · rcases hD with rfl | rfl
    · exact h.reg64_st
    · exact h.reg64_scr
  · rw [A_add]; exact h.scr_in (by rcases ho with rfl | rfl <;> omega)
  · rw [A_add]; exact h.off_dst hD (by omega) (by rcases ho with rfl | rfl <;> omega) (by decide)

theorem env {r : Nat} (hr : r < 24) : Env s₀.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := by
  rcases cur_cases s₀ r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.env_of (.inl rfl) (.inr rfl) h.st_scr200 hr
  · exact h.env_of (.inr rfl) (.inl rfl) h.st_scr200.symm hr

end Pre

/-! ## What the scratch space holds -/

/-- The round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, rd64 m (scp s₀) (200 + 8 * j) = RC j

/-- The saved registers. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (A (scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_ok : ∀ p ∈ saved, p.1 ≠ .r1 ∧ p.2 < 4096 ∧ 396 ≤ p.2 ∧ p.2 + 4 ≤ 432 := by decide

theorem Aux.keep {s₀ : State} {m m' : Mem} (ha : Aux s₀ m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32) :
    Aux s₀ m' := fun j hj =>
  (rd64_congr (hk (200 + 8 * j) (by omega) (by omega)) (hk (200 + 8 * j + 4) (by omega) (by omega))).trans
    (ha j hj)

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 396 ≤ d → d + 4 ≤ 432 → m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32) :
    Saved s₀ m' := fun p hp => by
  obtain ⟨-, -, h1, h2⟩ := saved_ok p hp
  rw [hk _ h1 h2]; exact hs p hp

theorem readW_writeW_A (m : Mem) {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (v : BitVec 32)
    {d e : Nat} (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hs : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A b e) v).readW (A b d) 32 = m.readW (A b d) 32 := by
  rw [A_eq (by omega), A_eq (by omega)]; exact readW_writeW_save m _ v (by omega) (by omega) hs

/-- Words the rounds do not write. -/
theorem Pre.keep_round {s₀ : State} (hp : Pre s₀) {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    {m m' : Mem} (hf : Frame [regR Dd 200, ⟨A (scp s₀) rcPtr, 4⟩] m m') {d : Nat} (hd : 200 ≤ d)
    (hd' : d + 4 ≤ 512) (hne : d + 4 ≤ 392 ∨ 396 ≤ d) :
    m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.off_dst hD hd hd' (by decide)
  · exact hp.scr_disj hd' (by decide) (by simp only [rcPtr]; omega) (by decide) (by decide)

/-! ## The state in memory -/

theorem stateAt_get {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) (m : Mem) {i : Nat} (hi : i < 25) :
    (stateAt m (State.addr b))[i] = rd64 m b (8 * i) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega), A_eq (by omega),
    show State.addr b + BitVec.ofNat 64 (8 * i) + 4 = State.addr b + BitVec.ofNat 64 (8 * i + 4) by
      bv_omega]

theorem stateAt_eq {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) {m : Mem} {K : KState}
    (h : Lanes32 m b K) : stateAt m (State.addr b) = K := by
  apply Vector.ext
  intro i hi
  rw [stateAt_get hfit m hi, h i hi]
  exact getElem!_pos K i hi

/-! ## The rounds -/

/-- The loop's invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r1 : s.gpr .r1 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : s.mem.readW (A (scp s₀) rcPtr) 32 = rcp s₀ r
  state : Lanes32 s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  saved : Saved s₀ s.mem
  frame : Frame [regR (stp s₀) 200, regR (scp s₀) 512] s₀.mem s.mem

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {src dst : Reg} (hsrc : Ptr src)
    (hdst : Ptr dst) {s : State} (hL : LInv s₀ r s) (h0 : s.gpr src = cur s₀ r)
    (hd : s.gpr dst = oth s₀ r) : WP isa (.block (round src dst)) s (LInv s₀ (r + 1)) := by
  have hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := (cur_cases s₀ r).symm.imp (·.2) (·.2)
  have E : Env s.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env hr
  refine WP.mono (round_ok hsrc hdst (rc := RC r) s E h0 hd hL.r1 hL.state hL.ptr
    (by rw [rd64_rcp]; exact hL.aux r hr)) fun s' ⟨hl, hf, hptr, hq, hrd, hwr, hsp⟩ => ?_
  refine ⟨by rw [hq .r0 (by simp), hL.r0], by rw [hq .r1 (by simp), hL.r1], hrd.trans hL.rd,
    hwr.trans hL.wr, hsp.trans hL.sp, by rw [hptr, rcp_succ], ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega) (.inl hd'),
    hL.saved.keep fun d hd hd' => hp.keep_round hD hf (by omega) (by omega) (.inr hd), ?_⟩
  · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · rcases hD with e | e <;> rw [e]
      · exact ⟨regR (stp s₀) 200, by simp, fun _ h => h⟩
      · exact ⟨regR (scp s₀) 512, by simp, Region.sub_prefix (by omega)⟩
    · refine ⟨regR (scp s₀) 512, by simp, ?_⟩
      rw [hp.scA (by decide)]; exact sub_offset (by decide) (by decide)

theorem body_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 12) {s : State} (hL : LInv s₀ (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega) (src := .r0) (dst := .r1) (by simp [Ptr])
    (by simp [Ptr]) hL (by rw [hL.r0, (cur_even s₀ t).1]) (by rw [hL.r1, (cur_even s₀ t).2]))
    fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega) (src := .r1) (dst := .r0) (by simp [Ptr])
    (by simp [Ptr]) h₁ (by rw [h₁.r1, (cur_odd s₀ t).1]) (by rw [h₁.r0, (cur_odd s₀ t).2]))
    fun s₂ h₂ => ?_
  have h₂' : LInv s₀ (2 * (t + 1)) s₂ := by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]; exact h₂
  refine wp_ldr (a := A (scp s₀) rcPtr) (by decide) (by rw [h₂.r1])
    (by rw [h₂.rd, h₂.wr]; exact mem_rd (hp.scr_in (by decide))) fun s₃ u₃ => ?_
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  have hT : s₄.gpr T1 = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .r1 (by decide), h₂'.ptr, h₂.r1]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    sub_beq (by omega) (by omega)] at hz
  have hs₅ : LInv s₀ (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.gpr, u₄.other .r0 (by decide), u₃.other .r0 (by decide), h₂'.r0]
    · rw [u₅.gpr, u₄.other .r1 (by decide), u₃.other .r1 (by decide), h₂'.r1]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, h₂'.sp]
    · rw [u₅.mem, u₄.mem, u₃.mem, h₂'.ptr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.saved
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.frame
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega)]; rfl, by omega, hs₅⟩

/-! ## The prologue -/

/-- The memory after storing the registers `l` (values `g`) at `b + offset`. -/
def saveMemA (m : Mem) (b : BitVec 32) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | p :: l => saveMemA (m.writeW (A b p.2) (g p.1)) b g l

theorem saveA_ok {bR : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ InRegions s.wr (A (s.gpr bR) p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMemA s.mem (s.gpr bR) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.str p.1 bR p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h3⟩ := hl p (by simp)
    refine wp_str h1 rfl h3 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr sp m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) (sp.trans u₁.sp) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem saveMemA_frame {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)) (m : Mem), (∀ p ∈ l, p.2 + 4 ≤ N) →
      Frame [regR b N] m (saveMemA m b g l) := by
  intro l
  induction l with
  | nil => intro m _; exact Frame.refl _ _
  | cons p l ih =>
    intro m hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_A hfit (hl p (by simp)))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

set_option simprocs false in
theorem saveMemA_saved (m : Mem) {b : BitVec 32} (hfit : b.toNat + 512 ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMemA m b g saved).readW (A b p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [saved, saveMemA, Mem.readW_writeW_self32, readW_writeW_A (hfit := hfit)]

/-- Round constant `k`, stored in the scratch space. -/
theorem rcStore_ok (k : Nat) (hk : k < 24) (s : State)
    (hin : InRegions s.wr (A (s.gpr .r1) (200 + 8 * k)) 4)
    (hin' : InRegions s.wr (A (s.gpr .r1) (200 + 8 * k + 4)) 4) :
    WP isa (.block (rcStore k)) s fun s' =>
      (∀ r, r ≠ T1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = write64 s.mem (s.gpr .r1) (200 + 8 * k) (RC k) := by
  unfold rcStore
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  refine wp_str (a := A (s.gpr .r1) (200 + 8 * k)) (by omega)
    (by rw [u₂.other .r1 (by decide), u₁.other .r1 (by decide)]) (by rw [u₂.wr, u₁.wr]; exact hin)
    fun s₃ u₃ => ?_
  refine wp_movw fun s₄ u₄ => wp_movt fun s₅ u₅ => ?_
  refine wp_str (a := A (s.gpr .r1) (200 + 8 * k + 4)) (by omega)
    (by rw [u₅.other .r1 (by decide), u₄.other .r1 (by decide), u₃.gpr, u₂.other .r1 (by decide),
      u₁.other .r1 (by decide), show 204 + 8 * k = 200 + 8 * k + 4 by omega])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hin') fun s₆ u₆ =>
      WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.gpr, u₅.other r hr, u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.mem, u₅.gpr, u₄.gpr, movw_movt, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, movw_movt, u₂.mem,
      u₁.mem]
    rfl

/-- During the stores of the round constants. -/
structure RcInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r1 : s.gpr .r1 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR (scp s₀) 512] s₀.mem s.mem
  saved : Saved s₀ s.mem
  rcs : ∀ j < k, rd64 s.mem (scp s₀) (200 + 8 * j) = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) :
    ∀ s, RcInv s₀ 0 s → WP isa (.block ((List.range 24).flatMap rcStore)) s (RcInv s₀ 24) := by
  have fC := hp.fitC
  refine wp_range_flatMap (M := isa) (RcInv s₀) (fun k s hk hI => ?_) 24 le_rfl
  refine WP.mono (rcStore_ok k hk s (by rw [hI.wr, hI.r1]; exact hp.scr_in (by omega))
    (by rw [hI.wr, hI.r1]; exact hp.scr_in (by omega))) fun s' ⟨g', r', w', p', m'⟩ => ?_
  rw [hI.r1] at m'
  refine ⟨by rw [g' _ (by decide), hI.r0], by rw [g' _ (by decide), hI.r1], r'.trans hI.rd, w'.trans hI.wr,
    p'.trans hI.sp, ?_, ?_, fun j hj => ?_⟩
  · rw [m']; exact frame_write64 hI.frame (List.mem_singleton_self _) fC (by omega) _
  · refine hI.saved.keep fun d hd hd' => ?_
    rw [m']
    simp only [write64]
    rw [readW_writeW_A _ fC _ (by omega) (by omega) (by omega),
      readW_writeW_A _ fC _ (by omega) (by omega) (by omega)]
  · rw [m']
    by_cases e : j = k
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.rcs j (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  have fC := hp.fitC
  have fS := hp.fitS
  rw [show prologue = saved.map (fun p => Instr.str p.1 .r1 p.2) ++
    ((List.range 24).flatMap rcStore ++ [.dp .add T1 .r1 (.imm 200), .str T1 .r1 rcPtr]) from rfl]
  refine saveA_ok saved s₀ _ (fun p hp' => ⟨(saved_ok p hp').2.1, hp.scr_in (by have := saved_ok p hp'; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₁ ⟨by rw [g₁], by rw [g₁], rd₁, wr₁, sp₁, ?_, ?_,
    fun _ h => absurd h (by omega)⟩) fun s₂ h₂ => ?_
  · rw [m₁]; exact saveMemA_frame fC _ _ _ (fun p hp' => by have := saved_ok p hp'; omega)
  · intro p hp'; rw [m₁]; exact saveMemA_saved _ fC _ p hp'
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := A (scp s₀) rcPtr) (by decide) (by rw [u₃.other .r1 (by decide), h₂.r1])
    (by rw [u₃.wr, h₂.wr]; exact hp.scr_in (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s₂.mem.writeW (A (scp s₀) rcPtr) (rcp s₀ 0) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, h₂.r1]; rfl
  have keep : ∀ d, 200 ≤ d → d + 4 ≤ 512 → d + 4 ≤ 392 ∨ 396 ≤ d →
      s₄.mem.readW (A (scp s₀) d) 32 = s₂.mem.readW (A (scp s₀) d) 32 := fun d hd hd' hne => by
    rw [hm]; exact readW_writeW_A _ fC _ hd' (by decide) (by simp only [rcPtr]; omega)
  refine ⟨by rw [u₄.gpr, u₃.other .r0 (by decide), h₂.r0], by rw [u₄.gpr, u₃.other .r1 (by decide), h₂.r1],
    by rw [u₄.rd, u₃.rd, h₂.rd], by rw [u₄.wr, u₃.wr, h₂.wr], by rw [u₄.sp, u₃.sp, h₂.sp],
    by rw [hm, Mem.readW_writeW_self32], fun i hi => ?_,
    Aux.keep h₂.rcs fun d hd hd' => keep d hd (by omega) (.inl hd'),
    h₂.saved.keep fun d hd hd' => keep d (by omega) (by omega) (.inr hd), ?_⟩
  · have hc : cur s₀ 0 = stp s₀ := by simp [cur]
    rw [hc, hm, rd64_writeW_disj _ _ (hp.off_st (d := rcPtr) (by decide) (by decide)) fS (by omega),
      rd64_frame h₂.frame (fun r hr => by simp at hr; subst hr; exact hp.disj) fS (by omega),
      ← stateAt_get fS _ hi]
    simp only [List.range_zero, List.foldl_nil]
    exact (getElem!_pos _ i hi).symm
  · rw [hm]
    exact (h₂.frame.mono (by simp)).writeW (by simp) _ (contains_A fC (by decide))

/-! ## The epilogue -/

theorem restoreA_ok {bR : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ bR ∧ p.2 < 4096 ∧ InRegions (s.rd ++ s.wr) (A (s.gpr bR) p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (A (s.gpr bR) p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 bR p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 rfl h3 fun s₁ u₁ => ?_
    have e : s₁.gpr bR = s.gpr bR := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm => k s' (fun q hq => ?_) (fun r hr => ?_)
      (hm.trans u₁.mem)
    · rw [e, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, e]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem preserved_saved : ∀ r ∈ preserved, ∃ p ∈ saved, p.1 = r := by decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  rw [show restore = saved.map (fun p => Instr.ldr p.1 .r1 p.2) from rfl, ← List.append_nil (saved.map _)]
  refine restoreA_ok saved s _ (by decide) (fun p hp' => ⟨(saved_ok p hp').1, (saved_ok p hp').2.1, ?_⟩)
    fun s' ho _ hm => WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · rw [hL.rd, hL.wr, hL.r1]; exact mem_rd (hp.scr_in (by have := saved_ok p hp'; omega))
  · obtain ⟨p, hp', rfl⟩ := preserved_saved r hr
    rw [ho p hp', hL.r1]; exact hL.saved p hp'
  · show stateAt s'.mem (State.addr (stp s₀)) = keccakF (A₀ s₀)
    rw [hm]
    have hc : cur s₀ 24 = stp s₀ := by simp [cur]
    exact stateAt_eq hp.fitS (hc ▸ hL.state)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  unfold permute
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 24) ?_ fun s₂ h₂ => restore_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ t, n = 12 - t ∧ t < 12 ∧ LInv s₀ (2 * t) s
  refine WP.loop (M := isa) Inv (fun n s ⟨t, hn, ht, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (body_ok hp ht hL) fun s' h => ?_
  rcases h with ⟨he, hL'⟩ | ⟨he, ht', hL'⟩
  · exact .inl ⟨he, hL'⟩
  · exact .inr ⟨he, 12 - (t + 1), by omega, t + 1, rfl, ht', hL'⟩

/-! ## Constant time -/

/-- The initial taint: the pointers are public, and point at the writable regions. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1], flags := false, lens := [200, 512], bases := [(.r0, 0), (.r1, 1)] }

theorem wf₀ {s : State} (h : Proof.Sha3.permuteArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of s h
  have hst := hp.fitS; have hsc := hp.fitC
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => by simp [τ₀] at h⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.permuteArm.pre s₁) (h₂ : Proof.Sha3.permuteArm.pre s₂)
    (hpub : Proof.Sha3.permuteArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · rw [(pre_of s₁ h₁).wr, (pre_of s₂ h₂).wr, stp, scp, stp, scp, p0, p1]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_verified : Verified Arm.target Impl.Sha3.Arm.permute Proof.Sha3.permuteArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide)
  · refine ⟨satState, rfl, rfl, ?_, by decide, by decide⟩
    intro a h₁ h₂
    simp only [Region.Contains, satState, State.addr] at h₁ h₂
    bv_omega

end VG.Proof.Sha3.Arm
