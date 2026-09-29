import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Sha3.X86.Round
import VerifiedGarbage.Proof.Sha3.X86.Contract

/-!
# Keccak-f[1600] on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean. The prologue loads the
arguments, saves the callee-saved registers and stores the round constants
in the scratch space; each iteration of the loop runs two rounds
(`round_ok`), from the state to the second state in the scratch space and
back; the epilogue restores the registers.
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86 VG.Impl.Sha3.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Sha512.Arm (lo hi)
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha512.X86 (Only Wrote rd64 write64 mem_rd Acc rd64_write64_self rd64_write64_ne
  rd64_frame)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_addi wp_sub wp_cmpi eval_ne sub_beq
  addr_toNat)
open VG.Proof.Sha3 (outState_eq foldl_succ)
open VG.Proof.Sha512.Arm (readW64)

/-! ## Addresses -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := arg s₀ 0
abbrev scp : BitVec 32 := arg s₀ 1
abbrev A₀ : KState := stateAt s₀.mem ((stp s₀).setWidth 64)
abbrev stR : Region := reg32 (stp s₀) 200
abbrev scR : Region := reg32 (scp s₀) 512
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : BitVec 32 := if r % 2 = 0 then stp s₀ else scp s₀
def oth (r : Nat) : BitVec 32 := if r % 2 = 0 then scp s₀ else stp s₀

/-- The address of the constant of round `r`. -/
abbrev rcp (r : Nat) : BitVec 32 := scp s₀ + BitVec.ofNat 32 (200 + 8 * r)

end

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | omega | rfl

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

theorem addr_add (b : BitVec 32) (a o : Nat) : addr (b + BitVec.ofNat 32 a) o = addr b (a + o) := by
  simp only [addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rcp_succ (s₀ : State) (r : Nat) : rcp s₀ r + 8 = rcp s₀ (r + 1) := by
  simp only [rcp]
  bv_omega

theorem rd64_rcp (m : Mem) (s₀ : State) (r : Nat) :
    rd64 m (rcp s₀ r) 0 = rd64 m (scp s₀) (200 + 8 * r) := by
  simp only [rd64, rcp, addr_add, Nat.zero_add, Nat.add_zero]

theorem reg32_eq (b : BitVec 32) (n : Nat) : reg32 b n = ⟨addr b 0, n⟩ := by rw [addr_zero]

/-- A part of a region at `b`. -/
theorem sub32 {b : BitVec 32} {N a k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : a + k ≤ N) (hk : 0 < k) :
    Region.Sub ⟨addr b a, k⟩ (reg32 b N) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [addr_eq (by omega)] at hx
  have hE := addr_toNat b
  generalize b.setWidth 64 = E at *
  bv_omega

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  disj : (stR s₀).Disjoint (scR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_sc : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_sc : (retR s₀).Disjoint (scR s₀)
  fitS : (stp s₀).toNat + 200 ≤ 2 ^ 32
  fitC : (scp s₀).toNat + 512 ≤ 2 ^ 32
  fitSp : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem accS : Acc s₀.wr (stp s₀) 200 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [h.wr]; simp) h.fitS

theorem accC : Acc s₀.wr (scp s₀) 512 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [h.wr]; simp) h.fitC

theorem accC200 : Acc s₀.wr (scp s₀) 200 := fun o ho => h.accC o (by omega)

/-- A part of the scratch space beyond the second state, and the state being written. -/
theorem sc_dst {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {d n : Nat} (hd₀ : 200 ≤ d)
    (hd : d + n ≤ 512) (hn : 0 < n) : Region.Disjoint ⟨addr (scp s₀) d, n⟩ (reg32 Dd 200) := by
  rcases hD with rfl | rfl
  · exact h.disj.symm.sub_left (sub32 h.fitC hd hn)
  · rw [reg32_eq]; exact sub_disj h.fitC hd (by omega) hn (by omega) (.inr hd₀)

/-- A part of the scratch space outside its work area. -/
theorem sc_work {d n : Nat} (hd : d + n ≤ 512) (hn : 0 < n) (hs : d + n ≤ 408 ∨ 488 ≤ d) :
    Region.Disjoint ⟨addr (scp s₀) d, n⟩ (workR (scp s₀)) :=
  sub_disj h.fitC hd (by omega) hn (by omega) hs

theorem st_work : (stR s₀).Disjoint (workR (scp s₀)) :=
  h.disj.sub_right (sub32 h.fitC (by omega) (by omega))

theorem state_work {S : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) :
    (reg32 S 200).Disjoint (workR (scp s₀)) := by
  rcases hS with rfl | rfl
  · exact h.st_work
  · rw [reg32_eq]; exact h.sc_work (by omega) (by omega) (.inl (by omega))

theorem st_sc200 : (stR s₀).Disjoint (reg32 (scp s₀) 200) :=
  h.disj.sub_right (Region.sub_prefix (by omega))

theorem env_of {S Dd : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    (hSD : (reg32 S 200).Disjoint (reg32 Dd 200)) {r : Nat} (hr : r < 24) :
    Env s₀.wr S Dd (scp s₀) (rcp s₀ r) := by
  have fS := h.fitS
  have fC := h.fitC
  have hP : (rcp s₀ r).toNat = (scp s₀).toNat + (200 + 8 * r) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 200 + 8 * r) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, fC, by omega, ?_, ?_, h.accC, fun o ho => ?_, hSD, h.state_work hS,
    h.state_work hD, ?_, ?_⟩
  · rcases hS with rfl | rfl <;> omega
  · rcases hD with rfl | rfl <;> omega
  · rcases hS with rfl | rfl
    · exact h.accS
    · exact h.accC200
  · rcases hD with rfl | rfl
    · exact h.accS
    · exact h.accC200
  · rw [addr_add]; exact h.accC _ (by omega)
  · show Region.Disjoint ⟨addr (scp s₀) (200 + 8 * r), 8⟩ _
    exact h.sc_dst hD (by omega) (by omega) (by omega)
  · show Region.Disjoint ⟨addr (scp s₀) (200 + 8 * r), 8⟩ _
    exact h.sc_work (by omega) (by omega) (.inl (by omega))

theorem env {r : Nat} (hr : r < 24) : Env s₀.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := by
  rcases cur_cases s₀ r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.env_of (.inl rfl) (.inr rfl) h.st_sc200 hr
  · exact h.env_of (.inr rfl) (.inl rfl) h.st_sc200.symm hr

/-- Words of the scratch space that a round does not write. -/
theorem keep_round {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {m m' : Mem}
    (hf : Frame [reg32 Dd 200, workR (scp s₀)] m m') {d : Nat} (hd : 200 ≤ d) (hd' : d + 4 ≤ 408) :
    m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (scp s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.sc_dst hD hd (by omega) (by decide)
  · exact h.sc_work (by omega) (by decide) (.inl hd')

end Pre

/-! ## What the scratch space holds -/

/-- The round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, rd64 m (scp s₀) (200 + 8 * j) = RC j

/-- The saved registers. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_ok : ∀ p ∈ saved, 392 ≤ p.2 ∧ p.2 + 4 ≤ 404 := by decide

theorem Aux.keep {s₀ : State} {m m' : Mem} (ha : Aux s₀ m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32) :
    Aux s₀ m' := fun j hj => by
  simp only [rd64]
  rw [hk _ (by omega) (by omega), hk _ (by omega) (by omega)]
  exact ha j hj

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 392 ≤ d → d + 4 ≤ 404 → m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32) :
    Saved s₀ m' := fun p hp => by
  obtain ⟨h1, h2⟩ := saved_ok p hp
  rw [hk _ h1 h2]; exact hs p hp

/-! ## The state in memory -/

theorem stateAt_get {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) (m : Mem) {i : Nat} (hi : i < 25) :
    (stateAt m (b.setWidth 64))[i] = rd64 m b (8 * i) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, show b.setWidth 64 + BitVec.ofNat 64 (8 * i) + 4 =
      b.setWidth 64 + BitVec.ofNat 64 (8 * i + 4) by bv_omega,
    ← addr_eq (by omega), ← addr_eq (by omega)]

theorem stateAt_eq {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) {m : Mem} {K : KState}
    (h : Lanes32 m b K) : stateAt m (b.setWidth 64) = K := by
  apply Vector.ext
  intro i hi
  rw [stateAt_get hfit m hi, h i hi]
  exact getElem!_pos K i hi

/-! ## The rounds -/

/-- The loop's invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  esi : s.gpr .esi = stp s₀
  edi : s.gpr .edi = scp s₀
  ebp : s.gpr .ebp = rcp s₀ r
  keep : ∀ q, q ∉ [Reg.eax, .edx, .ecx, .esi, .edi, .ebp] → s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes32 s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  saved : Saved s₀ s.mem
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {src dst : Reg} (hsrc : Ptr src)
    (hdst : Ptr dst) {s : State} (hL : LInv s₀ r s) (h0 : s.gpr src = cur s₀ r)
    (hd : s.gpr dst = oth s₀ r) : WP isa (.block (round src dst)) s (LInv s₀ (r + 1)) := by
  have hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := (cur_cases s₀ r).symm.imp (·.2) (·.2)
  have E : Env s.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env hr
  refine WP.mono (round_ok hsrc hdst (rc := RC r) s E h0 hd hL.edi hL.ebp hL.state
    (by rw [rd64_rcp]; exact hL.aux r hr)) fun s' ⟨hl, hf, hbp, hq, hrd, hwr⟩ => ?_
  have g : ∀ q ∈ [Reg.esi, .edi], s'.gpr q = s.gpr q := fun q hq' => hq q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl <;> decide)
  refine ⟨by rw [g _ (by simp), hL.esi], by rw [g _ (by simp), hL.edi], by rw [hbp, rcp_succ],
    fun q hq' => ?_, hrd.trans hL.rd, hwr.trans hL.wr, ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega),
    hL.saved.keep fun d hd hd' => hp.keep_round hD hf (by omega) (by omega), ?_⟩
  · have ⟨a, b, c, _, _, e⟩ : q ≠ .eax ∧ q ≠ .edx ∧ q ≠ .ecx ∧ q ≠ .esi ∧ q ≠ .edi ∧ q ≠ .ebp := by
      simpa using hq'
    rw [hq q (by simp [a, b, c, e]), hL.keep q hq']
  · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · rcases hD with e | e <;> rw [e]
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨scR s₀, by simp, sub32 hp.fitC (by omega) (by omega)⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 12) {s : State} (hL : LInv s₀ (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega) (src := .esi) (dst := .edi) (.inl rfl)
    (.inr rfl) hL (by rw [hL.esi, (cur_even s₀ t).1]) (by rw [hL.edi, (cur_even s₀ t).2]))
    fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega) (src := .edi) (dst := .esi) (.inr rfl)
    (.inl rfl) h₁ (by rw [h₁.edi, (cur_odd s₀ t).1]) (by rw [h₁.esi, (cur_odd s₀ t).2]))
    fun s₂ h₂ => ?_
  have h₂' : LInv s₀ (2 * (t + 1)) s₂ := by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]; exact h₂
  refine wp_mov fun s₃ u₃ => wp_sub fun s₄ u₄ _ => wp_cmpi fun s₅ u₅ _ hz => WP.block_nil ?_
  have hT : s₄.gpr .eax = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .edi (by decide), h₂'.ebp, h₂'.edi]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    sub_beq (by omega) (by omega)] at hz
  have g : ∀ q, q ≠ .eax → s₅.gpr q = s₂.gpr q := fun q hq => by
    rw [u₅.gpr, u₄.other q hq, u₃.other q hq]
  have hs₅ : LInv s₀ (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g _ (by decide), h₂'.esi]
    · rw [g _ (by decide), h₂'.edi]
    · rw [g _ (by decide), h₂'.ebp]
    · rw [g _ (by rintro rfl; simp at hq), h₂'.keep q hq]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.saved
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.frame
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega)]; rfl, by omega, hs₅⟩

/-! ## The prologue -/

/-- Round constant `k`, stored in the scratch space at `edi`. -/
theorem rcStore_ok (k : Nat) (_hk : k < 24) {W : BitVec 32} (s : State) (hW : s.gpr .edi = W)
    (hin : Wr2 s W (200 + 8 * k)) :
    WP isa (.block (rcStore k)) s fun s' =>
      Wrote [.eax] s s' (write64 s.mem W (200 + 8 * k) (RC k)) := by
  unfold rcStore
  refine wp_movi fun s₁ u₁ => wp_stm (by rw [u₁.other _ (by decide), hW]) (by rw [u₁.wr]; exact hin.1)
    fun s₂ u₂ => ?_
  refine wp_movi fun s₃ u₃ => ?_
  rw [show 204 + 8 * k = 200 + 8 * k + 4 by omega]
  refine wp_stm (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hW])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin.2) fun s₄ u₄ =>
      WP.block_nil ⟨fun r hr => ?_, ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · have hr' : r ≠ .eax := by simpa using hr
    rw [u₄.gpr, u₃.other r hr', u₂.gpr, u₁.other r hr']
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl

/-- During the stores of the round constants. -/
structure RcInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨addr (scp s₀) 200, 192⟩] s₁.mem s.mem
  rcs : ∀ j < k, rd64 s.mem (scp s₀) (200 + 8 * j) = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s₁ : State) (hW : s₁.gpr .edi = scp s₀) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 24).flatMap rcStore)) s₁ (RcInv s₀ s₁ 24) := by
  have fC := hp.fitC
  refine wp_range_flatMap (M := isa) (RcInv s₀ s₁) (fun k s hk hI => ?_) 24 (Nat.le_refl _) s₁
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (rcStore_ok k hk s (by rw [hI.gpr _ (by decide), hW])
    ⟨by rw [hI.wr, hwr]; exact hp.accC _ (by omega), by rw [hI.wr, hwr]; exact hp.accC _ (by omega)⟩)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun j hj => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _)
      (sub_contains fC (by omega) (by omega) (by omega) (by omega))
      (sub_contains fC (by omega) (by omega) (by omega) (by omega)) _
  · rw [w.mem]
    by_cases e : j = k
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.rcs j (by omega)

theorem prologue_eq : prologue = [.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 4)),
    .store (at_ .eax 392) .esi, .store (at_ .eax 396) .edi, .store (at_ .eax 400) .ebp,
    .mov .edi (.reg .eax), .mov .esi (.reg .ecx)] ++
    ((List.range 24).flatMap rcStore ++ [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 200)]) := rfl

theorem arg_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 2) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  have := hp.fitSp
  show (⟨addr (s₀.gpr .esp) 4, 8⟩ : Region).Contains _ _
  exact sub_contains (N := 12) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  have fC := hp.fitC
  have fS := hp.fitS
  rw [prologue_eq, WP.block_append_iff]
  refine wp_ldm (B := s₀.gpr .esp) rfl (arg_in hp (i := 1) (by omega)) fun s₁ u₁ => ?_
  refine wp_ldm (B := s₀.gpr .esp) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact arg_in hp (i := 0) (by omega)) fun s₂ u₂ => ?_
  have e1 : s₂.gpr .eax = scp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  have e2 : s₂.gpr .ecx = stp s₀ := by rw [u₂.gpr, u₁.mem]; rfl
  have w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have sin : ∀ (t : State), t.wr = s₀.wr → ∀ d, 392 ≤ d → d + 4 ≤ 404 →
      InRegions t.wr (addr (scp s₀) d) 4 := fun t ht d _ _ => by rw [ht]; exact hp.accC _ (by omega)
  refine wp_stm e1 (sin _ w₂ 392 (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, e1]) (sin _ (by rw [u₃.wr, w₂]) 396 (by omega) (by omega)) fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, e1]) (sin _ (by rw [u₄.wr, u₃.wr, w₂]) 400 (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have g₅ : ∀ r, s₅.gpr r = s₂.gpr r := fun r => by rw [u₅.gpr, u₄.gpr, u₃.gpr]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₂.other r h2, u₁.other r h1]
  have hW₇ : s₇.gpr .edi = scp s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e1]
  have w₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂]
  -- The saved registers, and the memory the saves changed.
  have hm₇ : s₇.mem = ((s₂.mem.writeW (addr (scp s₀) 392) (s₀.gpr .esi)).writeW (addr (scp s₀) 396)
      (s₀.gpr .edi)).writeW (addr (scp s₀) 400) (s₀.gpr .ebp) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide),
      g₂ _ (by decide) (by decide), g₂ _ (by decide) (by decide)]
  have hm₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  have c : ∀ d, 392 ≤ d → d + 4 ≤ 404 → (⟨addr (scp s₀) 392, 12⟩ : Region).Contains (addr (scp s₀) d) 4 :=
    fun d h1 h2 => sub_contains fC (by omega) h1 (by omega) (by omega)
  have fr₇ : Frame [⟨addr (scp s₀) 392, 12⟩] s₀.mem s₇.mem := by
    rw [hm₇, hm₂]
    have m := List.mem_singleton_self (⟨addr (scp s₀) 392, 12⟩ : Region)
    exact (((Frame.refl _ _).writeW m _ (c 392 (by omega) (by omega))).writeW m _
      (c 396 (by omega) (by omega))).writeW m _ (c 400 (by omega) (by omega))
  have sv₇ : Saved s₀ s₇.mem := by
    intro p hp'
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [hm₇]
    rcases hp' with rfl | rfl | rfl
    · rw [VG.Proof.Sha256.X86.Stream.readW_writeW_addr _ _ (by omega) (by omega) (by omega),
        VG.Proof.Sha256.X86.Stream.readW_writeW_addr _ _ (by omega) (by omega) (by omega),
        Mem.readW_writeW_self32]
    · rw [VG.Proof.Sha256.X86.Stream.readW_writeW_addr _ _ (by omega) (by omega) (by omega),
        Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  have hwr₇ := w₇
  -- The round constants.
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₇ hW₇ w₇) fun s₈ h₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => WP.block_nil ?_
  have g₈ : ∀ r, r ≠ .eax → s₈.gpr r = s₇.gpr r := fun r hr => h₈.gpr r (by simpa using hr)
  have keep : ∀ d, 392 ≤ d → d + 4 ≤ 404 →
      s₁₀.mem.readW (addr (scp s₀) d) 32 = s₇.mem.readW (addr (scp s₀) d) 32 := fun d h1 h2 => by
    rw [u₁₀.mem, u₉.mem]
    exact h₈.frame.readW (Region.contains_self _ _) (by
      simpa using sub_disj fC (by omega) (by omega) (by omega) (by omega) (.inr h1)) (by decide)
  have fr₁₀ : Frame [⟨addr (scp s₀) 392, 12⟩, ⟨addr (scp s₀) 200, 192⟩] s₀.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem]
    exact (fr₇.mono (by simp)).trans (h₈.frame.mono (by simp))
  refine ⟨?_, ?_, ?_, fun q hq => ?_, by rw [u₁₀.rd, u₉.rd, h₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
    u₂.rd, u₁.rd], by rw [u₁₀.wr, u₉.wr, h₈.wr, w₇], fun i hi => ?_, ?_,
    sv₇.keep fun d h1 h2 => keep d h1 h2, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), g₈ _ (by decide), u₇.gpr, u₆.other _ (by decide),
      g₅, e2]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), g₈ _ (by decide), hW₇]
  · rw [u₁₀.gpr, u₉.gpr, g₈ _ (by decide), hW₇]; rfl
  · have ⟨a, _, c', d', e', f⟩ : q ≠ .eax ∧ q ≠ .edx ∧ q ≠ .ecx ∧ q ≠ .esi ∧ q ≠ .edi ∧ q ≠ .ebp := by
      simpa using hq
    rw [u₁₀.other q f, u₉.other q f, g₈ q a, u₇.other q d', u₆.other q e', g₅,
      g₂ q a c']
  · -- The state is untouched.
    have hc : cur s₀ 0 = stp s₀ := by simp [cur]
    rw [hc, rd64_frame fr₁₀ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.disj.sub_right (sub32 fC (by omega) (by omega))
      · exact hp.disj.sub_right (sub32 fC (by omega) (by omega))) fS (by omega),
      ← stateAt_get fS _ hi]
    simp only [List.range_zero, List.foldl_nil]
    exact (getElem!_pos _ i hi).symm
  · rw [u₁₀.mem, u₉.mem]; exact h₈.rcs
  · refine fr₁₀.sub fun R hR => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨scR s₀, by simp, sub32 fC (by omega) (by omega)⟩
    · exact ⟨scR s₀, by simp, sub32 fC (by omega) (by omega)⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block restore) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.permuteX86.post s₀ s' := by
  have fC := hp.fitC
  have hin : ∀ d, 392 ≤ d → d + 4 ≤ 404 → InRegions (s.rd ++ s.wr) (addr (scp s₀) d) 4 :=
    fun d _ _ => mem_rd (by rw [hL.wr]; exact hp.accC _ (by omega))
  have sv := hL.saved
  simp only [Saved, saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at sv
  obtain ⟨v1, v2, v3⟩ := sv
  unfold restore
  refine wp_ldm hL.edi (hin 392 (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ldm (by rw [u₁.other _ (by decide), hL.edi]) (by rw [u₁.rd, u₁.wr]; exact hin 400 (by omega) (by omega))
    fun s₂ u₂ => ?_
  refine wp_ldm (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hL.edi])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 396 (by omega) (by omega)) fun s₃ u₃ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hL.keep _ (by decide)]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, v1]
    · rw [u₃.gpr, u₂.mem, u₁.mem, v2]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, v3]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hL.keep _ (by decide)]
  · rw [u₃.mem, u₂.mem, u₁.mem]
    exact hL.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_sc⟩) (by decide)
  · show stateAt s₃.mem ((stp s₀).setWidth 64) = keccakF (A₀ s₀)
    rw [u₃.mem, u₂.mem, u₁.mem]
    have hc : cur s₀ 24 = stp s₀ := by simp [cur]
    exact stateAt_eq hp.fitS (hc ▸ hL.state)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.permuteX86.post s₀ s' := by
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

/-- The taint analysis starts with `esp` public, and the words holding
`state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 512], argLen := 12,
    argBases := [(4, 0), (8, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.fitS; have hsc := hp.fitC; have hs := hp.fitSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_sc hp.arg_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.permuteX86.pre s₁)
    (h₂ : Proof.Sha3.permuteX86.pre s₂) (hpub : Proof.Sha3.permuteX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stp, scp, a0, a1]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.fitSp h4 hk, VG.X86.Taint.argByte_eq hp₂.fitSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def satMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem sat_pre : Proof.Sha3.permuteX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha3.permuteX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, satState] at h₁ h₂
    bv_omega

theorem permute_verified : Verified X86.target permute Proof.Sha3.permuteX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
      (by taint_decide),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sha3.X86
