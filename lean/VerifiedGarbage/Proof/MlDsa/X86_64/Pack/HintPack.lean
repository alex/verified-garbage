import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Hint
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.MemTaint
import VerifiedGarbage.Proof.MlDsa.Pack.Hint
import VerifiedGarbage.Proof.MlKem.X86_64.Rel

/-!
# ML-DSA on x86-64: `vg_mldsa_hint_bit_pack`

The code follows the fold form of `HintBitPack` (`Pack/Hint.lean`) step by
step: the bytes of `y` are the array of the spec, and `rax` its index, which
stays below `ω` because it counts the 1s before the current coefficient
(`hpIdx_lt`).

Constant time but for the hint: once `y` is zeroed, the two runs agree on
all the memory the function may access (the hint, which the contract lets it
leak, and `y`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of ofNat64_pred ofNat64_beq_zero wp_countdown ifp ifn b8_eq64)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_pack(h = rdi, hlen = rsi, omega = edx, y = rcx, len = r8)`. -/
def hintBitPackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat * 4⟩] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 4⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 4⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    (dArg s .rdx, (s.gpr .r8).toNat - dArg s .rdx) ∈ hintParams ∧ dArg s .rdx ≤ (s.gpr .r8).toNat ∧
    (s.gpr .rsi).toNat = 256 * ((s.gpr .r8).toNat - dArg s .rdx) ∧
    hintOnes (hintAt s.mem (s.gpr .rdi) ((s.gpr .r8).toNat - dArg s .rdx)) ≤ dArg s .rdx
  post s s' := bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
    hintBitPack (dArg s .rdx) ((s.gpr .r8).toNat - dArg s .rdx)
      (hintAt s.mem (s.gpr .rdi) ((s.gpr .r8).toNat - dArg s .rdx))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    (List.range (s₁.gpr .rsi).toNat).map (fun i => (coeffAt s₁.mem (s₁.gpr .rdi) i).toNat) =
      (List.range (s₂.gpr .rsi).toNat).map (fun i => (coeffAt s₂.mem (s₂.gpr .rdi) i).toNat)

theorem ea_idx (s : State) (b i : Reg) : s.ea (atIdx b i) = s.gpr b + s.gpr i := by
  simp [State.ea, atIdx]

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

section
variable {s₀ : State} (hp : hintBitPackK.pre s₀)

/-- The arguments. -/
abbrev hω (s₀ : State) : Nat := dArg s₀ .rdx
abbrev hk (s₀ : State) : Nat := (s₀.gpr .r8).toNat - dArg s₀ .rdx
abbrev hLen (s₀ : State) : Nat := (s₀.gpr .r8).toNat
abbrev hH (s₀ : State) : List (Vector Bool n) := hintAt s₀.mem (s₀.gpr .rdi) (hk s₀)

include hp in
theorem hp_facts : 4 ≤ hk s₀ ∧ hk s₀ ≤ 8 ∧ hω s₀ ≤ 80 ∧ hω s₀ + hk s₀ = hLen s₀ ∧
    (s₀.gpr .rsi).toNat * 4 = 1024 * hk s₀ := by
  have := mem_hintParams hp.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.2.1
  simp only [hk, hω, hLen] at *
  omega

/-! ## Zeroing `y` -/

theorem hbpZeroPro_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov32 .rax (.imm 0), .mov .r9 (.reg .rcx), .mov .r10 (.reg .r8)]) s
      fun s' => (s'.gpr .rdx = BitVec.ofNat 64 (dArg s .rdx) ∧ s'.gpr .rax = 0 ∧ s'.gpr .r9 = s.gpr .rcx ∧
        s'.gpr .r10 = s.gpr .r8 ∧ s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]
  apply BitVec.eq_of_toNat_eq; simp

theorem zeroStep_ok (s : State) (hout : InRegions s.wr (s.gpr .r9) 1) :
    WP isa (.block [.store8 (at_ .r9 0) .rax, .alu .add .r9 (.imm 1), .alu .sub .r10 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r9) (BitVec.setWidth 8 (s.gpr .rax)) ∧ s'.gpr .r9 = s.gpr .r9 + 1 ∧
        s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0)) ∧ Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hout]

include hp in
theorem hbpZero_ok :
    WP isa hbpZero s₀ fun s =>
      bytesAt s.mem (s₀.gpr .rcx) (hLen s₀) = List.replicate (hLen s₀) 0 ∧
        Frame [⟨s₀.gpr .rcx, hLen s₀⟩] s₀.mem s.mem ∧ s.gpr .rax = 0 ∧
        s.gpr .rdx = BitVec.ofNat 64 (hω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s := by
  obtain ⟨hk4, -, -, hsum, -⟩ := hp_facts hp
  obtain ⟨-, hwr, -⟩ := hp
  have hl := (s₀.gpr .r8).isLt
  have e1 : hLen s₀ = (s₀.gpr .r8).toNat := rfl
  simp only [hk, hω, hLen] at hk4 hsum
  refine WP.seq (WP.mono (hbpZeroPro_ok s₀) fun s₁ ⟨⟨dx₁, ax₁, r9₁, r10₁, m₁⟩, k₁⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := hLen s₀) (by omega) (by omega)
    (fun t s => s.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 t ∧ s.gpr .rax = 0 ∧
      Frame [⟨s₀.gpr .rcx, hLen s₀⟩] s₀.mem s.mem ∧ (∀ u < t, s.mem (s₀.gpr .rcx + BitVec.ofNat 64 u) = 0) ∧
      s.gpr .rdx = BitVec.ofNat 64 (hω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s)
    (fun t ht s ⟨h9, hax, hf, hz, hdx, hk⟩ _ => ?_) (fun s ⟨_, hax, hf, hz, hdx, hk⟩ => ⟨?_, hf, hax, hdx, hk⟩)
    ⟨by rw [r9₁]; simp, ax₁, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), dx₁,
      k₁.mono (by decide)⟩ (by rw [r10₁]; simp)
  · refine WP.mono (zeroStep_ok s (by
      rw [hk.2.2, hwr, h9]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s' ⟨⟨hm, h9', h10, hz'⟩, k'⟩ => ⟨⟨?_, ?_, ?_, fun u hu => ?_, ?_, (hk.trans k').mono (by decide)⟩, h10, hz'⟩
    · rw [h9', h9, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
    · rw [k'.gpr (by decide), hax]
    · rw [hm, h9]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, h9, VG.WriteBytes.writeW8_apply]
      split
      · rw [hax]; rfl
      · rename_i hne
        refine hz u (by
          by_contra hu'
          exact hne (by rw [show u = t by omega]))
    · rw [k'.gpr (by decide), hdx]
  · exact bytesAt_eq (by simp) fun i hi => by rw [hz i hi]; simp

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (hω s₀) (hH s₀)) (Array.replicate (hω s₀ + hk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((hH s₀).getD i noHint)) (hpS s₀ i)

theorem hpT_zero (s₀ : State) (i : Nat) : hpT s₀ i 0 = hpS s₀ i := by
  simp only [hpT, List.range_zero, List.foldl_nil]


theorem hpS_idx (s₀ : State) (i : Nat) : (hpS s₀ i).2 = onesBefore (hH s₀) i 0 := by
  rw [hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (hpT s₀ i j).2 = onesBefore (hH s₀) i j := by
  rw [hpT, hpSteps_idx, hpS_idx]; unfold onesBefore; rfl

/-- Before coefficient `j` of polynomial `i`. -/
structure CInv (s₀ : State) (i j : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (4 * (256 * i + j))
  r11 : s.gpr .r11 = BitVec.ofNat 64 j
  rax : s.gpr .rax = BitVec.ofNat 64 (hpT s₀ i j).2
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rcx, hLen s₀⟩] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .rcx) (hLen s₀) = (hpT s₀ i j).1.toList

theorem hpT_succ (s₀ : State) (i j : Nat) :
    hpT s₀ i (j + 1) = hpStep ((hH s₀).getD i noHint) (hpT s₀ i j) j := by
  rw [hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    hpS s₀ (i + 1) = ((hpT s₀ i n).1.set! (hω s₀ + i) (BitVec.ofNat 8 (hpT s₀ i n).2), (hpT s₀ i n).2) := by
  rw [hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem hbpLoad_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4) :
    WP isa (.block [.mov32 .rsi (.mem (at_ .rdi 0)), .alu32 .cmp .rsi (.imm 0)]) s fun s' =>
      (s'.zf = some (s.mem.readW (s.gpr .rdi) 32 - 0 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rsi] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hin]

theorem hbpSet_ok (s : State) (hout : InRegions s.wr (s.gpr .rcx + s.gpr .rax) 1) :
    WP isa (.block [.store8 (atIdx .rcx .rax) .r11, .alu .add .rax (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rcx + s.gpr .rax) (BitVec.setWidth 8 (s.gpr .r11)) ∧
        s'.gpr .rax = s.gpr .rax + 1) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_idx, hout]

theorem hbpNext_ok (s : State) :
    WP isa (.block [.alu .add .rdi (.imm 4), .alu .add .r11 (.imm 1), .alu32 .cmp .r11 (.imm 256)]) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .r11 = s.gpr .r11 + 1 ∧
        s'.zf = some (BitVec.setWidth 32 (s.gpr .r11 + 1) - 256 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rdi, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem ofNat_succ64 (x : Nat) : BitVec.ofNat 64 x + 1 = BitVec.ofNat 64 (x + 1) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

theorem cmp256 {j : Nat} (hj : j < 256) : (BitVec.setWidth 32 (BitVec.ofNat 64 (j + 1)) - 256 == 0) = decide (j + 1 = 256) := by
  rw [VG.Proof.MlKem.X86_64.sub_beq_zero32]
  simp only [decide_eq_decide]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; rw [h]; rfl

include hp in
theorem coef_ok {i j : Nat} (hi : i < hk s₀) (hj : j < 256) {s : State} (hI : CInv s₀ i j s) :
    WP isa hbpCoef s fun s' => CInv s₀ i (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 256)) ∧
      Keep [.rax, .rsi, .rdi, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := hp_facts hp
  obtain ⟨hrd, hwr, hsep, -, -, -, -, -, hones⟩ := hp
  have e1 : hLen s₀ = (s₀.gpr .r8).toNat := rfl
  have e2 : hk s₀ = (s₀.gpr .r8).toNat - dArg s₀ .rdx := rfl
  have e3 : hω s₀ = dArg s₀ .rdx := rfl
  have hpos : 256 * i + j < 256 * hk s₀ := by omega
  -- The word, on entry.
  have hR : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat * 4⟩ : Region).Contains (coeffAddr (s₀.gpr .rdi) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  have hw : s.mem.readW (s.gpr .rdi) 32 = coeffAt s₀.mem (s₀.gpr .rdi) (256 * i + j) := by
    rw [hI.rdi]
    exact hI.frame.readW hR (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by decide)
  unfold hbpCoef
  refine WP.seq (WP.mono (hbpLoad_ok s (by rw [hI.rd, hI.wr, hrd, hI.rdi]; exact ⟨_, by simp, hR⟩))
    fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_)
  have hbit := hintAt_get (m := s₀.mem) (p := s₀.gpr .rdi) hi hj
  have hT := hpT_succ s₀ i j
  have hidx := hpT_idx s₀ i j
  refine WP.seq ?_
  -- The branch.
  have hc : isa.eval .ne s₁ = some (decide (coeffAt s₀.mem (s₀.gpr .rdi) (256 * i + j) ≠ 0)) := by
    show Option.map _ s₁.zf = _
    rw [z₁, hw, VG.Proof.MlKem.X86_64.sub_beq_zero32]; simp
  refine WP.ite (M := isa) _ hc (fun h1 => ?_) (fun h0 => ?_)
  · -- A 1: `y[index] ← j`.
    have hlt : (hpT s₀ i j).2 < hLen s₀ := by
      have : onesBefore (hH s₀) i j < hintOnes (hH s₀) :=
        hpIdx_lt (hintAt_length s₀.mem (s₀.gpr .rdi) _) hi hj (by rw [hbit]; exact h1)
      have hones' : hintOnes (hH s₀) ≤ hω s₀ := hones
      rw [hidx]; omega
    refine WP.mono (hbpSet_ok s₁ (by
      rw [k₁.2.2, hI.wr, hwr, k₁.gpr (by decide), k₁.gpr (by decide), hI.rcx, hI.rax]
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)) fun s₂ ⟨⟨m₂, ax₂⟩, k₂⟩ => ?_
    refine WP.mono (hbpNext_ok s₂) fun s₃ ⟨⟨di₃, r11₃, z₃, m₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [di₃, k₂.gpr (by decide), k₁.gpr (by decide), hI.rdi, BitVec.add_assoc,
        show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [r11₃, k₂.gpr (by decide), k₁.gpr (by decide), hI.r11, ofNat_succ64]
    · rw [k₃.gpr (by decide), ax₂, k₁.gpr (by decide), hI.rax, hT, hpStep, hbit]
      simp only [h1, ↓reduceIte, ofNat_succ64]
    · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hI.rcx]
    · rw [k₃.2.1, k₂.2.1, k₁.2.1, hI.rd]
    · rw [k₃.2.2, k₂.2.2, k₁.2.2, hI.wr]
    · rw [m₃, m₂, m₁, k₁.gpr (by decide), k₁.gpr (by decide), hI.rcx, hI.rax]
      exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m₃, m₂, m₁, k₁.gpr (by decide), k₁.gpr (by decide), hI.rcx, hI.rax, bytesAt_writeW8 _ _ hlt (by omega),
        hI.y, hT, hpStep, hbit, k₁.gpr (by decide), hI.r11, b8_eq64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [h1, ↓reduceIte, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide), hI.r11, ofNat_succ64, cmp256 hj]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)
  · -- A 0.
    refine WP.block_nil (WP.mono (hbpNext_ok s₁) fun s₃ ⟨⟨di₃, r11₃, z₃, m₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩)
    · rw [di₃, k₁.gpr (by decide), hI.rdi, BitVec.add_assoc,
        show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [r11₃, k₁.gpr (by decide), hI.r11, ofNat_succ64]
    · rw [k₃.gpr (by decide), k₁.gpr (by decide), hI.rax, hT, hpStep, hbit]
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
    · rw [k₃.gpr (by decide), k₁.gpr (by decide), hI.rcx]
    · rw [k₃.2.1, k₁.2.1, hI.rd]
    · rw [k₃.2.2, k₁.2.2, hI.wr]
    · rw [m₃, m₁]; exact hI.frame
    · rw [m₃, m₁, hI.y, hT, hpStep, hbit]
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
    · rw [z₃, k₁.gpr (by decide), hI.r11, ofNat_succ64, cmp256 hj]
    · exact (k₁.trans k₃).mono (by decide)

include hp in
theorem inner_ok {i : Nat} (hi : i < hk s₀) {s : State} (hI : CInv s₀ i 0 s) :
    WP isa (.loop hbpCoef .ne) s fun s' => CInv s₀ i 256 s' ∧ Keep [.rax, .rsi, .rdi, .r11] s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ j, j < 256 ∧ m = 256 - j ∧ CInv s₀ i j s' ∧
    Keep [.rax, .rsi, .rdi, .r11] s s') (fun m s' ⟨j, hj, hm, hI', hk'⟩ => ?_) 256 s
    ⟨0, by decide, rfl, hI, Keep.refl _ _⟩
  refine WP.mono (coef_ok hp hi hj hI') fun s'' ⟨hI'', hz, hk''⟩ => ?_
  have hc : isa.eval .ne s'' = some (!decide (j + 1 = 256)) := by
    show Option.map _ s''.zf = _; rw [hz]; rfl
  by_cases e : j + 1 = 256
  · refine .inl ⟨by rw [hc, e]; rfl, ?_, (hk'.trans hk'').mono (by decide)⟩
    rw [← e]; exact hI''
  · refine .inr ⟨by rw [hc, decide_eq_false e]; rfl, 256 - (j + 1), by omega, j + 1, by omega, rfl, hI'',
      (hk'.trans hk'').mono (by decide)⟩

/-- Before polynomial `i`. -/
structure HPInv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (4 * (256 * i))
  rax : s.gpr .rax = BitVec.ofNat 64 (hpS s₀ i).2
  rcx : s.gpr .rcx = s₀.gpr .rcx
  r9 : s.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 (hω s₀ + i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rcx, hLen s₀⟩] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .rcx) (hLen s₀) = (hpS s₀ i).1.toList

theorem zeroR11_ok (s : State) :
    WP isa (.block [.mov32 .r11 (.imm 0)]) s fun s' => (s'.gpr .r11 = 0 ∧ s'.mem = s.mem) ∧ Keep [.r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

include hp in
theorem poly_ok {i : Nat} (hi : i < hk s₀) {s : State} (hP : HPInv s₀ i s) :
    WP isa hbpPoly s fun s' => HPInv s₀ (i + 1) s' ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some (s.gpr .r10 - 1 == 0) ∧ Keep [.rax, .rsi, .rdi, .r9, .r10, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := hp_facts hp
  have hwr := hp.2.1
  have e1 : hLen s₀ = (s₀.gpr .r8).toNat := rfl
  unfold hbpPoly
  refine WP.seq (WP.mono (zeroR11_ok s) fun s₁ ⟨⟨r11₁, m₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (inner_ok hp hi (s := s₁) ⟨by rw [k₁.gpr (by decide), hP.rdi]; rfl, by rw [r11₁]; rfl,
    by rw [k₁.gpr (by decide), hP.rax, hpT_zero], by rw [k₁.gpr (by decide), hP.rcx], by rw [k₁.2.1, hP.rd],
    by rw [k₁.2.2, hP.wr], by rw [m₁]; exact hP.frame, by rw [m₁, hP.y, hpT_zero]⟩) fun s₂ ⟨hI, k₂⟩ => ?_)
  have r9₂ : s₂.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 (hω s₀ + i) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), hP.r9]
  have hidx : (hpT s₀ i 256).2 < 2 ^ 8 := by
    have := hpT_idx s₀ i 256
    have h1 : onesBefore (hH s₀) i 256 ≤ hintOnes (hH s₀) := onesBefore_n_le (hintAt_length _ _ _) hi
    have hones' : hintOnes (hH s₀) ≤ hω s₀ := hp.2.2.2.2.2.2.2.2
    rw [this]; omega
  refine WP.mono (zeroStep_ok s₂ (by
      rw [hI.wr, hwr, r9₂]
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩))
    fun s₃ ⟨⟨m₃, r9₃, r10₃, z₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [k₃.gpr (by decide), hI.rdi, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega]
  · rw [k₃.gpr (by decide), hI.rax, hpS_succ]
  · rw [k₃.gpr (by decide), hI.rcx]
  · rw [r9₃, r9₂, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [k₃.2.1, hI.rd]
  · rw [k₃.2.2, hI.wr]
  · rw [m₃, r9₂]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [m₃, r9₂, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, hI.rax, hpS_succ, b8_eq64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (hpT s₀ i 256).2 < 2 ^ 64 by omega), Array.set!_eq_setIfInBounds,
      Array.toList_setIfInBounds]
  · rw [r10₃, k₂.gpr (by decide), k₁.gpr (by decide)]
  · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
  · exact ((k₁.trans k₂).trans k₃).mono (by decide)

theorem hbpSetup_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rcx), .alu .add .r9 (.reg .rdx), .mov .r10 (.reg .r8), .alu .sub .r10 (.reg .rdx)])
      s fun s' => (s'.gpr .r9 = s.gpr .rcx + s.gpr .rdx ∧ s'.gpr .r10 = s.gpr .r8 - s.gpr .rdx ∧ s'.mem = s.mem) ∧
        Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

include hp in
theorem hbp_wp :
    WP isa Impl.MlDsa.X86_64.Pack.hintBitPack s₀ fun s' =>
      hintBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := hp_facts hp
  have e1 : hLen s₀ = (s₀.gpr .r8).toNat := rfl
  have e2 : hk s₀ = (s₀.gpr .r8).toNat - dArg s₀ .rdx := rfl
  have e3 : hω s₀ = dArg s₀ .rdx := rfl
  unfold Impl.MlDsa.X86_64.Pack.hintBitPack
  refine WP.seq (WP.mono (hbpZero_ok hp) fun s₁ ⟨hy₁, hf₁, ax₁, dx₁, k₁⟩ => ?_)
  unfold hbpMain
  refine WP.seq (WP.mono (hbpSetup_ok s₁) fun s₂ ⟨⟨r9₂, r10₂, m₂⟩, k₂⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := hk s₀) (by omega) (by omega) (fun i s => HPInv s₀ i s)
    (fun i hi s hP _ => WP.mono (poly_ok hp hi hP) fun s' ⟨h, h10, hz, _⟩ => ⟨h, h10, hz⟩)
    (fun s hP => ⟨hP.y.trans (hintBitPack_eq _ _ _).symm, hP.frame⟩) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [k₂.gpr (by decide), k₁.gpr (by decide)]; simp
  · rw [k₂.gpr (by decide), ax₁]; rfl
  · rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  · rw [r9₂, k₁.gpr (by decide), dx₁]; rfl
  · rw [k₂.2.1, k₁.2.1]
  · rw [k₂.2.2, k₁.2.2]
  · rw [m₂]; exact hf₁
  · rw [m₂, hy₁]; show _ = (Array.replicate (hω s₀ + hk s₀) (0 : Byte)).toList
    rw [Array.toList_replicate, hsum]
  · rw [r10₂, k₁.gpr (by decide), dx₁]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := (s₀.gpr .r8).isLt
    omega

end

theorem hintBitPack_correct (s : State) (hs : hintBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.hintBitPack s t s' ∧ abiPreserved s s' ∧ hintBitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.hintBitPack)
    [.rax, .rdx, .rsi, .rdi, .r9, .r10, .r11] (hbp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

/-! ## Constant time -/

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (coeffAddr p _) ht, Mem.readW_byte m₂ (coeffAddr p _) ht, ← coeffAt_eq, ← coeffAt_eq,
    hw _ hi]

/-- The taint of the loops: the pointers, the lengths, `ω` and the index. -/
abbrev hbpTaint : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rcx, .rdx, .r8, .rax]

theorem hintBitPack_ct :
    ConstantTime isa hintBitPackK.pre hintBitPackK.pub Impl.MlDsa.X86_64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := MAgree hbpTaint) ?_ (RelCT.taint (A := memTaint) hbpTaint (fun _ _ h => h) (by taint_decide))
  refine Proof.MlKem.X86_64.RelCT.postDep
    (RelCT.taint (A := taint) (regsLo [.rdi, .rsi, .rcx, .r8, .rsp] [.rdx])
      (fun _ _ ⟨_, _, hp⟩ => agree_regsLo (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1])
        fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2.2.1)
      (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨hbpZero_ok hx, hbpZero_ok hy⟩) fun x y x' y' ⟨hx, hy, hp⟩ fx fy => ?_
  obtain ⟨hy₁, hf₁, ax₁, dx₁, k₁⟩ := fx
  obtain ⟨hy₂, hf₂, ax₂, dx₂, k₂⟩ := fy
  obtain ⟨di, si, ci, r8, -, dx, hleak⟩ := hp
  have hdx : dArg x .rdx = dArg y .rdx := by unfold dArg; rw [dx]
  have hrd : x'.rd = y'.rd := by rw [k₁.2.1, k₂.2.1, hx.1, hy.1, di, si]
  have hwr : x'.wr = y'.wr := by rw [k₁.2.2, k₂.2.2, hx.2.1, hy.2.1, ci, r8]
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := hp_facts hx
  refine ⟨X86_64.Taint.agree_ofRegs fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), di]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), ci]
    · rw [dx₁, dx₂]; exact congrArg _ hdx
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), r8]
    · rw [ax₁, ax₂]
  · rw [k₁.2.1, k₁.2.2, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      have hdis : ∀ r ∈ [(⟨x.gpr .rcx, (x.gpr .r8).toNat⟩ : Region)], ¬ r.Contains a 1 := by
        intro r hr hc'; simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'
      rw [hf₁ a hdis, hf₂ a (fun r hr hc' => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [hLen, ← ci, ← r8] at hc'
        exact hx.2.2.1 a hc hc')]
      exact bytes_of_words (by rw [← di, ← si] at hleak; exact hleak) hc
    · -- `y`: zeros.
      have hlt : (a - x.gpr .rcx).toNat < (x.gpr .r8).toNat := by simp only [Region.Contains] at hc; omega
      have eL : hLen x = (x.gpr .r8).toNat := rfl
      have eLy : hLen y = (x.gpr .r8).toNat := by show (y.gpr .r8).toNat = _; rw [r8]
      have ea : a = x.gpr .rcx + BitVec.ofNat 64 (a - x.gpr .rcx).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := congrArg (·.getD (a - x.gpr .rcx).toNat 0) hy₁
      have h₂ := congrArg (·.getD (a - x.gpr .rcx).toNat 0) hy₂
      rw [eL, bytesAt_getD _ _ hlt, ← ea] at h₁
      rw [eLy, ← ci, bytesAt_getD _ _ hlt, ← ea] at h₂
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def hintBitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1024 | .rdx => 80 | .rcx => 0x3000 | .r8 => 84 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

theorem coeffAt_zero' (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := coeffAt_zero p i

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_zero l]

theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, coeffAt_zero', Function.comp_def, filter_false, sum_zero]

theorem hintBitPack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.hintBitPack (hintBitPackContract X86_64.abi) :=
  Verified.of_correct hintBitPack_correct hintBitPack_ct
    { pre := by sig_implies_pre [hintBitPackContract, hintBitPackSig, hintBitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [hintBitPackContract, hintBitPackSig, hintBitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [hintBitPackContract, hintBitPackSig, hintBitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨hintBitPackSat, ?_⟩
        sig_pre [hintBitPackContract, hintBitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | (rw [hintOnes_zero]; exact Nat.zero_le _)
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack
