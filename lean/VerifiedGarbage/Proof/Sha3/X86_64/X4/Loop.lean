import VerifiedGarbage.Proof.Sha3.X86_64.X4.Round

/-!
# Keccak-f[1600] four times at once on x86-64: the 24 rounds

Untrusted: everything here is checked by Lean. `permute4` applies
Keccak-f[1600] to each of the four interleaved states at `rdi`, using the
800 bytes at `rsi` for every other round and the table of round constants
at `rdx` (`permute4_ok`).
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4
open VG.Spec.Sha3 (keccakF rnd RC)
open VG.Proof.Sha3 (outState outState_eq foldl_succ)

/-- Where `permute4` reads and writes: the four states at `src`, the 800
bytes at `oth`, and the table at `tbl`, none of which overlap, and the
round constants in the table. -/
structure Pre4 (s₀ : State) (src oth tbl : Addr) : Prop where
  src_in : ∀ i < 25, InRegions s₀.wr (src + BitVec.ofNat 64 (32 * i)) 32
  oth_in : ∀ i < 25, InRegions s₀.wr (oth + BitVec.ofNat 64 (32 * i)) 32
  tbl_in : ∀ r < 24, InRegions (s₀.rd ++ s₀.wr) (tbl + BitVec.ofNat 64 (32 * r)) 32
  src_oth : Region.Disjoint ⟨src, 800⟩ ⟨oth, 800⟩
  src_tbl : Region.Disjoint ⟨src, 800⟩ ⟨tbl, 768⟩
  oth_tbl : Region.Disjoint ⟨oth, 800⟩ ⟨tbl, 768⟩
  rc : ∀ r < 24, ∀ k < 4, s₀.mem.readW (la tbl r k) 64 = RC r

section
variable (src oth : Addr)

/-- The states the rounds read before round `r`, and those they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then src else oth
def nxt (r : Nat) : Addr := if r % 2 = 0 then oth else src

theorem cur_succ (r : Nat) : cur src oth (r + 1) = nxt src oth r := by
  simp only [cur, nxt]; split <;> split <;> first | rfl | omega

theorem nxt_succ (r : Nat) : nxt src oth (r + 1) = cur src oth r := by
  simp only [cur, nxt]; split <;> split <;> first | rfl | omega

theorem cur_cases (r : Nat) :
    (cur src oth r = src ∧ nxt src oth r = oth) ∨ (cur src oth r = oth ∧ nxt src oth r = src) := by
  simp only [cur, nxt]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

end

theorem in_append {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem la_rc (tbl : Addr) (r k : Nat) : la (tbl + BitVec.ofNat 64 (32 * r)) 0 k = la tbl r k := by
  simp only [la, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_zero, Nat.zero_add]

namespace Pre4
variable {s₀ : State} {src oth tbl : Addr} (h : Pre4 s₀ src oth tbl)
include h

theorem env (r : Nat) (hr : r < 24) :
    Env s₀.rd s₀.wr (cur src oth r) (nxt src oth r) (tbl + BitVec.ofNat 64 (32 * r)) := by
  have hsub : Region.Sub ⟨tbl + BitVec.ofNat 64 (32 * r), 32⟩ ⟨tbl, 768⟩ := Offset.sub_base tbl (by omega)
  rcases cur_cases src oth r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact ⟨fun i hi => in_append (h.src_in i hi), h.oth_in, h.tbl_in r hr, h.src_oth.symm,
      h.oth_tbl.sub_right hsub⟩
  · exact ⟨fun i hi => in_append (h.oth_in i hi), h.src_in, h.tbl_in r hr, h.src_oth,
      h.src_tbl.sub_right hsub⟩

/-- Writes to the states keep the table. -/
theorem rc_frame {m : Mem} (hf : Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem m) {r k : Nat} (hr : r < 24)
    (hk : k < 4) : m.readW (la tbl r k) 64 = RC r := by
  rw [hf.readW (Offset.contains_base tbl (show 32 * r + 8 * k + 64 / 8 ≤ 768 by omega) (by omega))
    (by simpa using ⟨h.src_tbl.symm, h.oth_tbl.symm⟩) (by decide)]
  exact h.rc r hr k hk

end Pre4

/-- The rounds' invariant, before round `r`. -/
structure LInv (s₀ : State) (src oth tbl : Addr) (A : Nat → KState) (r : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = cur src oth r
  rsi : s.gpr .rsi = nxt src oth r
  rdx : s.gpr .rdx = tbl + BitVec.ofNat 64 (32 * r)
  rest : ∀ g, g ≠ .rax → g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → s.gpr g = s₀.gpr g
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes4 s.mem (cur src oth r) fun k => (List.range r).foldl rnd (A k)
  frame : Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem

theorem end_beq (tbl : Addr) (r : Nat) (hr : r < 24) :
    (tbl + BitVec.ofNat 64 (32 * r) + 32 - (tbl + BitVec.ofNat 64 768) == 0) = decide (r + 1 = 24) := by
  rw [show tbl + BitVec.ofNat 64 (32 * r) + 32 = tbl + BitVec.ofNat 64 (32 * r + 32) by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    Offset.add_sub_add_left, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  simp only [show (32 * r + 32 = 768) = (r + 1 = 24) by apply propext; omega]

theorem round_step {s₀ : State} {src oth tbl : Addr} {A : Nat → KState} (hp : Pre4 s₀ src oth tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {r : Nat} (hr : r < 24) {s : State}
    (hL : LInv s₀ src oth tbl A r s) :
    WP isa (.block round) s fun s' =>
      eval .ne s' = some (!decide (r + 1 = 24)) ∧ LInv s₀ src oth tbl A (r + 1) s' := by
  have he := hp.env r hr
  refine WP.mono (round_ok s _ _ _ _ (RC r) (by rw [hL.rd, hL.wr]; exact he) hL.rdi hL.rsi hL.rdx
    hL.state fun k hk => by rw [la_rc]; exact hp.rc_frame hL.frame hr hk)
    fun s' ⟨hl, hf, hrd, hwr, hdi, hsi, hdx, hg, hzf⟩ => ?_
  have hcx' : s.gpr .rcx = tbl + BitVec.ofNat 64 768 := by
    rw [hL.rest _ (by decide) (by decide) (by decide) (by decide), hcx]
  refine ⟨?_, by rw [hdi, cur_succ], by rw [hsi, nxt_succ],
    by rw [hdx, BitVec.add_assoc, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]; rfl,
    fun g a b c d => by rw [hg g a b c d, hL.rest g a b c d], hrd.trans hL.rd, hwr.trans hL.wr, ?_, ?_⟩
  · simp only [eval, hzf, hcx', Option.map_some, end_beq tbl r hr]
  · intro i hi k hk
    rw [cur_succ, hl i hi k hk]
    simp only [foldl_succ, ← outState_eq]
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_singleton] at hR; subst hR
    rcases cur_cases src oth r with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact ⟨_, by simp, fun _ h => h⟩

/-- Two rounds, from an even round `r`. -/
theorem body_ok {s₀ : State} {src oth tbl : Addr} {A : Nat → KState} (hp : Pre4 s₀ src oth tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {r : Nat} (hr : r + 2 ≤ 24) {s : State}
    (hL : LInv s₀ src oth tbl A r s) :
    WP isa (.block (round ++ round)) s fun s' =>
      eval .ne s' = some (!decide (r + 2 = 24)) ∧ LInv s₀ src oth tbl A (r + 2) s' := by
  rw [WP.block_append_iff]
  exact WP.mono (round_step hp hcx (by omega) hL) fun s₁ ⟨_, h₁⟩ => round_step hp hcx (by omega) h₁

/-- The 24 rounds: Keccak-f[1600] on each of the four states at `src`,
with `rdi`, `rsi` and every register but `rax` and `rdx` as they were. -/
theorem permute4_ok {s₀ : State} {src oth tbl : Addr} (hp : Pre4 s₀ src oth tbl)
    (hdi : s₀.gpr .rdi = src) (hsi : s₀.gpr .rsi = oth) (hdx : s₀.gpr .rdx = tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {A : Nat → KState} (hA : Lanes4 s₀.mem src A) :
    WP isa permute4 s₀ fun s =>
      Lanes4 s.mem src (fun k => keccakF (A k)) ∧ Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.gpr .rdx = tbl + BitVec.ofNat 64 768 ∧
      ∀ g, g ≠ .rax → g ≠ .rdx → s.gpr g = s₀.gpr g := by
  have h₀ : LInv s₀ src oth tbl A 0 s₀ :=
    ⟨by rw [hdi]; rfl, by rw [hsi]; rfl, by rw [hdx]; exact (BitVec.add_zero _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl, by simpa [cur] using hA, Frame.refl _ _⟩
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ LInv s₀ src oth tbl A (2 * j) s
  refine WP.loop (M := isa) (Q := fun s => LInv s₀ src oth tbl A 24 s) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_)
    12 s₀ ⟨0, rfl, by omega, h₀⟩ |>.mono fun s hL => ?_
  · refine WP.mono (body_ok hp hcx (by omega) hL) fun s' ⟨he, hl⟩ => ?_
    by_cases hlast : 2 * j + 2 = 24
    · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
    · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 12 - (j + 1), by omega, j + 1, rfl, by omega,
        by rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact hl⟩
  · refine ⟨fun i hi k hk => ?_, hL.frame, hL.rd, hL.wr, hL.rdx, fun g a d => ?_⟩
    · have := hL.state i hi k hk
      simp only [cur, show 24 % 2 = 0 from rfl, ite_true] at this
      exact this
    · by_cases e₁ : g = .rdi
      · subst e₁; rw [hL.rdi, hdi]; rfl
      · by_cases e₂ : g = .rsi
        · subst e₂; rw [hL.rsi, hsi]; rfl
        · exact hL.rest g a e₁ e₂ d

end VG.Proof.Sha3.X86_64.X4
