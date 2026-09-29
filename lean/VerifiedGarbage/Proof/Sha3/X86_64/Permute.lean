import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.Sha3.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Keccak-f[1600] on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev scr : Addr := s₀.gpr .rsi
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then st s₀ else scr s₀
def oth (r : Nat) : Addr := if r % 2 = 0 then scr s₀ else st s₀

/-- Scratch offset `d`. -/
abbrev off (d : Nat) : Addr := scr s₀ + BitVec.ofNat 64 d

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem oth_succ (s₀ : State) (r : Nat) : oth s₀ (r + 1) = cur s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = st s₀ ∧ oth s₀ r = scr s₀) ∨ (cur s₀ r = scr s₀ ∧ oth s₀ r = st s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_wr {R : Region} (hR : R = stR s₀ ∨ R = scrR s₀) {a : Addr} {n : Nat}
    (hc : R.Contains a n) : InRegions s₀.wr a n := by
  rw [h.wr]; rcases hR with rfl | rfl
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {i : Nat} (hi : i < 25) :
    InRegions s₀.wr (laneAddr p i) 8 := by
  rcases hp with rfl | rfl
  · exact h.in_wr (.inl rfl) (lane_contains _ hi)
  · exact h.in_wr (.inr rfl) (contains_offset (by omega) (by omega))

theorem off_in {d : Nat} (hd : d + 8 ≤ 512) : InRegions s₀.wr (off s₀ d) 8 :=
  h.in_wr (.inr rfl) (contains_offset hd (by omega))

/-- The first 200 bytes of the scratch space are disjoint from the state. -/
theorem st_scr200 : (stR s₀).Disjoint ⟨scr s₀, 200⟩ :=
  h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The state and the second state are disjoint from every later scratch offset. -/
theorem region_off {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {d n : Nat} (hd : 200 ≤ d)
    (hn : d + n ≤ 512) : Region.Disjoint ⟨p, 200⟩ ⟨off s₀ d, n⟩ := by
  rcases hp with rfl | rfl
  · exact h.st_scr.sub_right (sub_offset hn (by omega))
  · have := off_disjoint (scr s₀) (a := 0) (n := 200) (b := d) (k := n) (by omega) (by omega)
      (.inl hd)
    rwa [add_zero'] at this

theorem env (r : Nat) (hr : r < 24) :
    Env s₀.rd s₀.wr (cur s₀ r) (oth s₀ r) (off s₀ (200 + 8 * r)) := by
  have hc := cur_cases s₀ r
  have hcur : cur s₀ r = st s₀ ∨ cur s₀ r = scr s₀ := hc.imp (·.1) (·.1)
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine ⟨fun i hi => h.in_all (h.lane_in hcur hi), fun i hi => h.lane_in hoth hi,
    h.in_all (h.off_in (by omega)), ?_, h.region_off hoth (by omega) (by omega)⟩
  rcases hc with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.st_scr200.symm
  · exact h.st_scr200

end Pre

/-! ## The scratch space -/

/-- The saved registers, and the round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  (∀ k < 6, m.readW (off s₀ (392 + 8 * k)) 64 = s₀.gpr ((saved.getD k (.rax, 0)).1)) ∧
  ∀ j < 24, m.readW (off s₀ (200 + 8 * j)) 64 = RC j

/-- Writes outside the constants and the saved registers keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, 200 ≤ d → d + 8 ≤ 440 → Region.Disjoint ⟨off s₀ d, 8⟩ R) (hf : Frame [R] m m') :
    Aux s₀ m' := by
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
    exact h.1 k hk
  · rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
    exact h.2 j hj

/-! ## The prologue -/

theorem save_eq : saved.map (fun (r, d) => Instr.store (at_ .rsi d) r) =
    (List.range 6).flatMap fun k =>
      [.store (at_ .rsi (392 + 8 * k)) ((saved.getD k (.rax, 0)).1)] := by decide

theorem prologue_eq : prologue = (List.range 6).flatMap (fun k =>
      [.store (at_ .rsi (392 + 8 * k)) ((saved.getD k (.rax, 0)).1)]) ++
    (List.range 24).flatMap (fun k => [.movImm64 .rax (RC k), .store (at_ .rsi (200 + 8 * k)) .rax]) ++
    [.mov .rdx (.reg .rsi), .alu .add .rdx (.imm 200), .mov .rcx (.reg .rsi), .alu .add .rcx (.imm 392)] := by
  rw [prologue, save_eq]

/-- During the saves. -/
def SaveInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ Frame [⟨off s₀ 392, 48⟩] s₀.mem s.mem ∧
    ∀ j < k, s.mem.readW (off s₀ (392 + 8 * j)) 64 = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem saves_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ((List.range 6).flatMap fun k =>
      [.store (at_ .rsi (392 + 8 * k)) ((saved.getD k (.rax, 0)).1)])) s₀ (SaveInv s₀ 6) := by
  refine wp_range_flatMap (M := isa) (SaveInv s₀) (fun k s hk ⟨hg, hrd, hwr, hf, hv⟩ => ?_) 6 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine wp_store (a := off s₀ (392 + 8 * k)) (by rw [ea_at, hg])
    (by rw [hwr]; exact hp.off_in (by omega)) fun s' g' m' r' w' => wp_nil ?_
  refine ⟨g'.trans hg, r'.trans hrd, w'.trans hwr, ?_, fun j hj => ?_⟩
  · rw [m']
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [show off s₀ (392 + 8 * k) = off s₀ 392 + BitVec.ofNat 64 (8 * k) by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  · rw [m', hg]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 392 + 8 * j) (n := 8) (b := 392 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- During the stores of the round constants, from memory `m₁`. -/
def RcInv (s₀ : State) (m₁ : Mem) (k : Nat) (s : State) : Prop :=
  s.gpr .rdi = st s₀ ∧ s.gpr .rsi = scr s₀ ∧ s.gpr .rsp = s₀.gpr .rsp ∧
    s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ Frame [⟨off s₀ 200, 192⟩] m₁ s.mem ∧
    ∀ j < k, s.mem.readW (off s₀ (200 + 8 * j)) 64 = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : RcInv s₀ s.mem 0 s) :
    WP isa (.block ((List.range 24).flatMap fun k =>
      [.movImm64 .rax (RC k), .store (at_ .rsi (200 + 8 * k)) .rax])) s (RcInv s₀ s.mem 24) := by
  refine wp_range_flatMap (M := isa) (RcInv s₀ s.mem) (fun k s hk ⟨hdi, hsi, hsp, hrd, hwr, hf, hv⟩ => ?_)
    24 (Nat.le_refl _) s hs
  refine wp_movi64 fun s₁ h₁ => wp_store (a := off s₀ (200 + 8 * k))
    (by rw [ea_at, h₁.other _ (by decide), hsi])
    (by rw [h₁.wr, hwr]; exact hp.off_in (by omega)) fun s' g' m' r' w' => wp_nil ?_
  refine ⟨by rw [g', h₁.other _ (by decide), hdi], by rw [g', h₁.other _ (by decide), hsi],
    by rw [g', h₁.other _ (by decide), hsp], by rw [r', h₁.rd, hrd], by rw [w', h₁.wr, hwr], ?_,
    fun j hj => ?_⟩
  · rw [m', h₁.mem]
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [show off s₀ (200 + 8 * k) = off s₀ 200 + BitVec.ofNat 64 (8 * k) by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  · rw [m', h₁.mem, h₁.gpr]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 200 + 8 * j) (n := 8) (b := 200 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The rounds' invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = cur s₀ r
  rsi : s.gpr .rsi = oth s₀ r
  rdx : s.gpr .rdx = off s₀ (200 + 8 * r)
  rcx : s.gpr .rcx = off s₀ 392
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  rw [prologue_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saves_ok hp) fun s₁ ⟨g₁, rd₁, wr₁, f₁, v₁⟩ => ?_
  refine WP.mono (rcs_ok hp s₁ ⟨by rw [g₁], by rw [g₁], by rw [g₁], rd₁, wr₁, Frame.refl _ _,
    fun _ h => absurd h (by omega)⟩) fun s₂ ⟨di₂, si₂, sp₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  refine wp_mov fun s₃ h₃ => wp_addi fun s₄ h₄ => wp_mov fun s₅ h₅ => wp_addi fun s₆ h₆ => wp_nil ?_
  have m : s₆.mem = s₂.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem]
  have k : ∀ r, r ≠ .rdx → r ≠ .rcx → s₆.gpr r = s₂.gpr r := fun r a b => by
    rw [h₆.other r b, h₅.other r b, h₄.other r a, h₃.other r a]
  have e200 : BitVec.signExtend 64 (200 : BitVec 32) = BitVec.ofNat 64 200 := by decide
  have e392 : BitVec.signExtend 64 (392 : BitVec 32) = BitVec.ofNat 64 392 := by decide
  -- The prologue writes only scratch offsets 200 to 440.
  have hf : Frame [⟨off s₀ 200, 240⟩] s₀.mem s₂.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, off_sub _ (by omega) (by omega) (by omega)⟩
  have hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_offset (by omega) (by omega)⟩
  refine ⟨by rw [k _ (by decide) (by decide), di₂]; simp [cur],
    by rw [k _ (by decide) (by decide), si₂]; simp [oth], ?_, ?_,
    by rw [k _ (by decide) (by decide), sp₂], by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, rd₂],
    by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, wr₂], ?_, ⟨fun j hj => ?_, fun j hj => ?_⟩,
    by rw [m]; exact hf₂⟩
  · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.gpr, si₂, e200]
  · rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), si₂, e392]
  · intro i hi
    have hc : cur s₀ 0 = st s₀ := by simp [cur]
    rw [hc, m, hf.readW (lane_contains _ hi)
      (by simpa using hp.region_off (.inl rfl) (d := 200) (n := 240) (by omega) (by omega)) (by decide)]
    simp [Spec.Sha3.stateAt, laneAddr]
  · rw [m, f₂.readW (Region.contains_self _ _) ?_ (by decide)]
    · exact v₁ j hj
    · simpa using off_disjoint (scr s₀) (a := 392 + 8 * j) (n := 8) (b := 200) (k := 192)
        (by omega) (by omega) (by omega)
  · rw [m]; exact v₂ j hj

/-! ## The rounds -/

theorem off_add8 (s₀ : State) (d : Nat) : off s₀ d + 8 = off s₀ (d + 8) := by
  simp only [off]; rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

theorem off_beq (s₀ : State) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (off s₀ a - off s₀ b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    apply h
    simp only [off] at e
    bv_omega

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {s : State} (hL : LInv s₀ r s) :
    WP isa (.block round) s fun s' =>
      eval .ne s' = some (!decide (r + 1 = 24)) ∧ LInv s₀ (r + 1) s' := by
  have he := hp.env r hr
  have hc := cur_cases s₀ r
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine WP.mono (round_ok s _ _ _ _ (RC r) (by rw [hL.rd, hL.wr]; exact he) hL.rdi hL.rsi hL.rdx
    hL.state (by rw [hL.aux.2 r hr])) fun s' ⟨hl, hf, hrd, hwr, hdi, hsi, hdx, hcx, hsp, hzf⟩ => ?_
  have hL' : LInv s₀ (r + 1) s' := by
    refine ⟨by rw [hdi, cur_succ], by rw [hsi, oth_succ], by rw [hdx, off_add8]; congr 1,
      by rw [hcx, hL.rcx], by rw [hsp, hL.rsp], hrd.trans hL.rd, hwr.trans hL.wr, ?_, ?_, ?_⟩
    · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
    · exact hL.aux.frame (fun d hd hd' => (hp.region_off hoth hd (by omega)).symm) hf
    · refine hL.frame.trans (hf.sub fun R hR => ?_)
      simp only [List.mem_singleton] at hR; subst hR
      rcases hoth with e | e <;> rw [e]
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega)⟩
  refine ⟨?_, hL'⟩
  simp only [eval, hzf, hL.rcx, off_add8, Option.map_some]
  rw [off_beq s₀ (by omega) (by omega)]
  simp only [show (200 + 8 * r + 8 = 392) = (r + 1 = 24) by apply propext; omega]

/-- Two rounds, from an even round `r`. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r + 2 ≤ 24) {s : State} (hL : LInv s₀ r s) :
    WP isa (.block (round ++ round)) s fun s' =>
      eval .ne s' = some (!decide (r + 2 = 24)) ∧ LInv s₀ (r + 2) s' := by
  rw [WP.block_append_iff]
  exact WP.mono (round_step hp (by omega) hL) fun s₁ ⟨_, h₁⟩ => round_step hp (by omega) h₁

/-! ## The epilogue -/

theorem restore_eq : restore = (List.range 6).flatMap fun k =>
    [.mov ((saved.getD k (.rax, 0)).1) (.mem (at_ .rsi (392 + 8 * k)))] := by decide

theorem saved_ne : ∀ j < 6, ∀ k < 6, j ≠ k → (saved.getD j (.rax, 0)).1 ≠ (saved.getD k (.rax, 0)).1 := by
  decide

theorem saved_ne_rsi : ∀ k < 6, (saved.getD k (.rax, 0)).1 ≠ .rsi ∧ (saved.getD k (.rax, 0)).1 ≠ .rsp ∧
    (saved.getD k (.rax, 0)).1 ≠ .rdi := by
  decide

/-- During the restores. -/
def ResInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .rsi = scr s₀ ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rsp = s₀.gpr .rsp ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    ∀ j < k, s.gpr ((saved.getD j (.rax, 0)).1) = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  rw [restore_eq]
  have hsi : s.gpr .rsi = scr s₀ := by rw [hL.rsi]; simp [oth]
  have hdi : s.gpr .rdi = st s₀ := by rw [hL.rdi]; simp [cur]
  refine WP.mono (wp_range_flatMap (M := isa) (ResInv s₀ s) (fun k s' hk ⟨si, di, sp, m, rd, wr, v⟩ => ?_) 6
    (Nat.le_refl _) s ⟨hsi, hdi, hL.rsp, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩) fun s' ⟨si, di, sp, m, _, _, v⟩ => ?_
  · refine wp_movm (a := off s₀ (392 + 8 * k)) (by rw [ea_at, si])
      (by rw [rd, wr, hL.rd, hL.wr]; exact hp.in_all (hp.off_in (by omega))) fun s'' h => wp_nil ?_
    have ne := saved_ne_rsi k hk
    refine ⟨by rw [h.other _ (Ne.symm ne.1), si], by rw [h.other _ (Ne.symm ne.2.2), di],
      by rw [h.other _ (Ne.symm ne.2.1), sp],
      by rw [h.mem, m], by rw [h.rd, rd], by rw [h.wr, wr], fun j hj => ?_⟩
    by_cases e : j = k
    · subst e; rw [h.gpr, m]; exact hL.aux.1 j hk
    · rw [h.other _ (saved_ne j (by omega) k hk e), v j (by omega)]
  · refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact v 0 (by omega)
      · exact v 1 (by omega)
      · exact sp
      · exact v 2 (by omega)
      · exact v 3 (by omega)
      · exact v 4 (by omega)
      · exact v 5 (by omega)
    · rw [m]
      exact hL.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
    · refine ⟨?_, di, si⟩
      show stateAt s'.mem (st s₀) = keccakF (A₀ s₀)
      apply Vector.ext
      intro i hi
      have := hL.state i hi
      simp only [cur, show 24 % 2 = 0 from rfl, ite_true] at this
      simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, m]
      exact this

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 24) ?_ fun s₂ h₂ => restore_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ LInv s₀ (2 * j) s
  refine WP.loop (M := isa) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (body_ok hp (by omega) hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : 2 * j + 2 = 24
  · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
  · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 12 - (j + 1), by omega, j + 1, rfl, by omega,
      by rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact hl⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_verified :
    Verified X86_64.target Impl.Sha3.X86_64.permute Proof.Sha3.permuteX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Sha3.X86_64
