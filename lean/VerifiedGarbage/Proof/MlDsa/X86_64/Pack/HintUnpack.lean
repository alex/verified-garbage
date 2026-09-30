import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack

/-!
# ML-DSA on x86-64: `vg_mldsa_hint_bit_unpack`

Untrusted: everything here is checked by Lean. The code follows the fold
form of `HintBitUnpack` (`hintBitUnpack_eq`, `Pack/Hint.lean`) step by step:
while no check has failed, the words of `h` are the hint of the spec
(`HArr`) and `rax` its index; once one has, `rax` is 256, which skips the
rest (`SRel`).

Constant time but for its input: once `h` is zeroed, the two runs agree on
all the memory the function may access (the input `y`, which the contract
lets it leak, and `h`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of wp_countdown ifp ifn b8_eq64 toNat_setWidth64_8)
open VG.Proof.MlKem (bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_unpack(y = rdi, len = rsi, omega = edx, h = rcx, hlen = r8)`. -/
def hintBitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat * 4⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 4⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat * 4⟩ ∧
    (dArg s .rdx, (s.gpr .rsi).toNat - dArg s .rdx) ∈ hintParams ∧ dArg s .rdx ≤ (s.gpr .rsi).toNat ∧
    (s.gpr .r8).toNat = 256 * ((s.gpr .rsi).toNat - dArg s .rdx)
  post s s' :=
    match hintBitUnpack (dArg s .rdx) ((s.gpr .rsi).toNat - dArg s .rdx)
      (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
    | some hint => (s'.gpr .rax).setWidth 32 = 1 ∧ HintIs s'.mem (s.gpr .rcx) ((s.gpr .rsi).toNat - dArg s .rdx) hint
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    leakBytes (bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat) =
      leakBytes (bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat)

section
variable {s₀ : State} (hp : hintBitUnpackK.pre s₀)

/-- The arguments. -/
abbrev uω (s₀ : State) : Nat := dArg s₀ .rdx
abbrev uk (s₀ : State) : Nat := (s₀.gpr .rsi).toNat - dArg s₀ .rdx
abbrev uLen (s₀ : State) : Nat := (s₀.gpr .rsi).toNat
abbrev uY (s₀ : State) : Array Byte := (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat).toArray
/-- The region of `h`. -/
abbrev uR (s₀ : State) : Region := ⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat * 4⟩

include hp in
theorem up_facts : 4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ uω s₀ ≤ 80 ∧ uω s₀ + uk s₀ = uLen s₀ ∧
    (s₀.gpr .r8).toNat = 256 * uk s₀ := by
  have := mem_hintParams hp.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.2
  simp only [uk, uω, uLen] at *
  omega

/-! ## Zeroing `h` -/

theorem hbuZeroPro_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov32 .rax (.imm 0), .mov .r9 (.reg .rcx), .mov .r10 (.reg .r8)]) s
      fun s' => (s'.gpr .rdx = BitVec.ofNat 64 (dArg s .rdx) ∧ s'.gpr .rax = 0 ∧ s'.gpr .r9 = s.gpr .rcx ∧
        s'.gpr .r10 = s.gpr .r8 ∧ s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]
  apply BitVec.eq_of_toNat_eq; simp

theorem zeroStep32_ok (s : State) (hout : InRegions s.wr (s.gpr .r9) 4) :
    WP isa (.block [.store32 (at_ .r9 0) .rax, .alu .add .r9 (.imm 4), .alu .sub .r10 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r9) (BitVec.setWidth 32 (s.gpr .rax)) ∧ s'.gpr .r9 = s.gpr .r9 + 4 ∧
        s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0)) ∧ Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hout]

include hp in
theorem hbuZero_ok :
    WP isa hbuZero s₀ fun s =>
      (∀ t < (s₀.gpr .r8).toNat, coeffAt s.mem (s₀.gpr .rcx) t = 0) ∧ Frame [uR s₀] s₀.mem s.mem ∧
        s.gpr .rax = 0 ∧ s.gpr .rdx = BitVec.ofNat 64 (uω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s := by
  obtain ⟨hk4, hk8, -, hsum, hr8⟩ := up_facts hp
  obtain ⟨-, hwr, -⟩ := hp
  have hl := (s₀.gpr .r8).isLt
  simp only [uk, uω, uLen] at hk4 hk8 hsum hr8
  refine WP.seq (WP.mono (hbuZeroPro_ok s₀) fun s₁ ⟨⟨dx₁, ax₁, r9₁, r10₁, m₁⟩, k₁⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := (s₀.gpr .r8).toNat) (by omega) (by omega)
    (fun t s => s.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 (4 * t) ∧ s.gpr .rax = 0 ∧
      Frame [uR s₀] s₀.mem s.mem ∧ (∀ u < t, coeffAt s.mem (s₀.gpr .rcx) u = 0) ∧
      s.gpr .rdx = BitVec.ofNat 64 (uω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s)
    (fun t ht s ⟨h9, hax, hf, hz, hdx, hk⟩ _ => ?_) (fun s ⟨_, hax, hf, hz, hdx, hk⟩ => ⟨hz, hf, hax, hdx, hk⟩)
    ⟨by rw [r9₁]; simp, ax₁, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), dx₁,
      k₁.mono (by decide)⟩ (by rw [r10₁]; simp)
  · refine WP.mono (zeroStep32_ok s (by
      rw [hk.2.2, hwr, h9]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s' ⟨⟨hm, h9', h10, hz'⟩, k'⟩ => ⟨⟨?_, ?_, ?_, fun u hu => ?_, ?_, (hk.trans k').mono (by decide)⟩, h10, hz'⟩
    · rw [h9', h9, BitVec.add_assoc, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show 4 * t + 4 = 4 * (t + 1) by omega]
    · rw [k'.gpr (by decide), hax]
    · rw [hm, h9]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, h9]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32, hax]; rfl
      · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          ← coeffAt_eq, hz u (by omega)]
    · rw [k'.gpr (by decide), hdx]

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = uk s₀ ∧ ∀ i < uk s₀, ∀ j < 256,
    coeffAt m (s₀.gpr .rcx) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `rax`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .rax = BitVec.ofNat 64 idx ∧ idx ≤ uω s₀ ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .rax = 256

/-- What stays the same from the loops on. -/
structure UCom (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi
  rdx : s.gpr .rdx = BitVec.ofNat 64 (uω s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [uR s₀] s₀.mem s.mem

theorem UCom.of_keep {s₀ s s' : State} (h : UCom s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (hrdi : Reg.rdi ∉ rs) (hrdx : Reg.rdx ∉ rs) (hm : Frame [uR s₀] s.mem s'.mem) : UCom s₀ s' :=
  ⟨(hk.gpr hrdi).trans h.rdi, (hk.gpr hrdx).trans h.rdx, hk.2.1.trans h.rd, hk.2.2.trans h.wr, h.frame.trans hm⟩

/-- Coefficient `256i + b`, the one `hbuSet` writes. -/
theorem setAddr (p : Addr) (i b : Nat) :
    p + BitVec.ofNat 64 (1024 * i) + BitVec.ofNat 64 b * 4 = coeffAddr p (256 * i + b) := by
  rw [show BitVec.ofNat 64 b * 4 = BitVec.ofNat 64 (4 * b) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : BitVec 64).toNat = 4 from rfl]
      omega,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat, coeffAddr]
  congr 2; omega

include hp in
theorem harr_set {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) {i b : Nat} (hi : i < uk s₀)
    (hb : b < 256) :
    HArr s₀ (m.writeW (coeffAddr (s₀.gpr .rcx) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -⟩ := up_facts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

include hp in
theorem harr_zero {m : Mem} (hz : ∀ t < (s₀.gpr .r8).toNat, coeffAt m (s₀.gpr .rcx) t = 0) :
    HArr s₀ m (Array.replicate (uk s₀) noHint) := by
  obtain ⟨-, -, -, -, hr8⟩ := up_facts hp
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

include hp in
/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s : State} (hc : UCom s₀ s) {t : Nat} (ht : t < uLen s₀) :
    s.mem (s₀.gpr .rdi + BitVec.ofNat 64 t) = (uY s₀).getD t 0 := by
  have e : uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.2.2.1 _ (Offset.contains_base _ (by omega) (by omega)) hc'

theorem hbuSet_ok (s : State) (hout : InRegions s.wr (s.gpr .rcx + s.gpr .rsi * 4) 4) :
    WP isa (.block hbuSet) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rcx + s.gpr .rsi * 4) (1 : BitVec 32) ∧ s'.gpr .rax = s.gpr .rax + 1) ∧
        Keep [.r8, .rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold hbuSet
  xrun [hout, show ∀ (t : State) (b i : Reg), t.ea (atIdx b i 4) = t.gpr b + t.gpr i * 4 from fun t b i => by
    simp [State.ea, atIdx]]

theorem ea_idx4 (t : State) (b i : Reg) : t.ea (atIdx b i 4) = t.gpr b + t.gpr i * 4 := by
  simp [State.ea, atIdx]

theorem ea_idxm1 (t : State) (b i : Reg) : t.ea (atIdx b i 1 (-1)) = t.gpr b + t.gpr i + BitVec.ofInt 64 (-1) := by
  simp [State.ea, atIdx]

theorem ofNat_pred64 (p : Addr) {x : Nat} (h : 1 ≤ x) (hx : x < 2 ^ 64) :
    p + BitVec.ofNat 64 x + BitVec.ofInt 64 (-1) = p + BitVec.ofNat 64 (x - 1) := by
  bv_omega

theorem cmpReg_ok (a b : Reg) (s : State) :
    WP isa (.block [.alu .cmp a (.reg b)]) s fun s' =>
      (s'.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat)) ∧ s'.mem = s.mem) ∧ Keep [] s s' := by
  refine WP.mono (Q := fun (s' : State) => s'.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat)) ∧ s'.mem = s.mem ∧
    s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr) (by xrun) fun s' ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨⟨h1, h2⟩, fun r _ => congrFun h3 r, h4, h5⟩

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ : State) (i bound : Nat) (s : State) : Prop where
  com : UCom s₀ s
  rcx : s.gpr .rcx = s₀.gpr .rcx + BitVec.ofNat 64 (1024 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 bound

theorem PCom.of_keep {s₀ s s' : State} {i bound : Nat} (h : PCom s₀ i bound s) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ rs, r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r11) (hm : Frame [uR s₀] s.mem s'.mem) :
    PCom s₀ i bound s' :=
  ⟨h.com.of_keep hk (fun h' => (hrs _ h').1 rfl) (fun h' => (hrs _ h').2.1 rfl) hm,
    (hk.gpr fun h' => (hrs _ h').2.2.1 rfl).trans h.rcx, (hk.gpr fun h' => (hrs _ h').2.2.2 rfl).trans h.r11⟩

include hp in
/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < uk s₀) {hA : Array (Vector Bool n)}
    {s : State} (hP : PCom s₀ i bound s) (hax : s.gpr .rax = BitVec.ofNat 64 idx)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 ((uY s₀).getD idx 0).toNat) (hh : HArr s₀ s.mem hA) :
    WP isa (.block hbuSet) s fun s' =>
      PCom s₀ i bound s' ∧ s'.gpr .rax = BitVec.ofNat 64 (idx + 1) ∧
        HArr s₀ s'.mem (huSet i ((uY s₀).getD idx 0).toNat hA) ∧ Keep [.r8, .rax] s s' := by
  obtain ⟨hk4, hk8, -, -, hr8⟩ := up_facts hp
  have hwr := hp.2.1
  have hb := ((uY s₀).getD idx 0).isLt
  have ha : s.gpr .rcx + s.gpr .rsi * 4 = coeffAddr (s₀.gpr .rcx) (256 * i + ((uY s₀).getD idx 0).toNat) := by
    rw [hP.rcx, hsi, setAddr]
  have hin : (uR s₀).Contains (coeffAddr (s₀.gpr .rcx) (256 * i + ((uY s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (hbuSet_ok s (by rw [hP.com.wr, hwr, ha]; exact ⟨_, List.mem_singleton_self _, hin⟩))
    fun s' ⟨⟨hm, hax'⟩, k'⟩ => ⟨hP.of_keep k' (by decide) ?_, by rw [hax', hax, ofNat_succ64], ?_, k'⟩
  · rw [hm, ha]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin
  · rw [hm, ha]; exact harr_set hp hh hi hb

include hp in
/-- The first coefficient of polynomial `i`, from the index `first`. -/
theorem first_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first < bound) (hbω : bound ≤ uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s) (hax : s.gpr .rax = BitVec.ofNat 64 first)
    (hh : HArr s₀ s.mem hA) :
    WP isa (.block (([.movzx8 .rsi (atIdx .rdi .rax)] : List Instr) ++ hbuSet ++
      ([.alu .cmp .rax (.reg .r11)] : List Instr))) s fun s' =>
      PCom s₀ i bound s' ∧ s'.gpr .rax = BitVec.ofNat 64 (first + 1) ∧
        HArr s₀ s'.mem (huSet i ((uY s₀).getD first 0).toNat hA) ∧
        s'.cf = some (decide (first + 1 < bound)) ∧ Keep [.r8, .rax, .rsi] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  have hrd := hp.1
  have e1 : uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun s' => s'.gpr .rsi = BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax)) ∧
    s'.mem = s.mem) (by
      xrun [ea_idx, show InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax) 1 by
        rw [hP.com.rd, hrd, hP.com.rdi, hax]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩])
    (by decide)) fun s₁ ⟨⟨si₁, m₁⟩, k₁⟩ => ?_
  have hb : s.mem (s.gpr .rdi + s.gpr .rax) = (uY s₀).getD first 0 := by
    rw [hP.com.rdi, hax]; exact yByte hp hP.com (by omega)
  have hP₁ : PCom s₀ i bound s₁ := hP.of_keep k₁ (by decide) (by rw [m₁]; exact Frame.refl _ _)
  refine WP.mono (set_ok hp hi (idx := first) (hA := hA) hP₁ (by rw [k₁.gpr (by decide), hax])
    (by rw [si₁, hb]; apply BitVec.eq_of_toNat_eq; simp) (by rw [m₁]; exact hh)) fun s₂ ⟨hP₂, ax₂, hh₂, k₂⟩ => ?_
  refine WP.mono (cmpReg_ok .rax .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ =>
    ⟨hP₂.of_keep k₃ (by decide) (by rw [m₃]; exact Frame.refl _ _), by rw [k₃.gpr (by decide), ax₂],
      by rw [m₃]; exact hh₂, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [cf₃, ax₂, hP₂.r11, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem hbuFail_ok (s : State) :
    WP isa hbuFail s fun s' => (s'.gpr .rax = 256 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

include hp in
/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ uω s₀) {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s)
    (hax : s.gpr .rax = BitVec.ofNat 64 idx) (hh : HArr s₀ s.mem hA) :
    WP isa hbuNext s fun s' => PCom s₀ i bound s' ∧
      (match huStep (uY s₀) i first (hA, idx) 0 with
        | some (hA', idx') => s'.gpr .rax = BitVec.ofNat 64 idx' ∧ HArr s₀ s'.mem hA' ∧
          s'.cf = some (decide (idx' < bound))
        | none => s'.gpr .rax = 256 ∧ s'.cf = some false) ∧ Keep [.r8, .rax, .rsi] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  have hrd := hp.1
  have e1 : uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  have hprev : s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1) = s₀.gpr .rdi + BitVec.ofNat 64 (idx - 1) := by
    rw [hP.com.rdi, hax, ofNat_pred64 _ (by omega) (by omega)]
  have hcur : s.gpr .rdi + s.gpr .rax = s₀.gpr .rdi + BitVec.ofNat 64 idx := by rw [hP.com.rdi, hax]
  unfold hbuNext
  refine WP.seq (WP.mono (WP.keep [.r8, .rsi] (Q := fun s' =>
    s'.gpr .r8 = BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1))) ∧
    s'.gpr .rsi = BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax)) ∧
    s'.cf = some (decide ((BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1)))).toNat <
      (BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax))).toNat)) ∧ s'.mem = s.mem) (by
      xrun [ea_idx, ea_idxm1, show InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1)) 1 by
          rw [hP.com.rd, hrd, hprev]
          exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩,
        show InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax) 1 by
          rw [hP.com.rd, hrd, hcur]
          exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩])
    (by decide)) fun s₁ ⟨⟨r8₁, si₁, cf₁, m₁⟩, k₁⟩ => ?_)
  have hbp : s.mem (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1)) = (uY s₀).getD (idx - 1) 0 := by
    rw [hprev]; exact yByte hp hP.com (by omega)
  have hbc : s.mem (s.gpr .rdi + s.gpr .rax) = (uY s₀).getD idx 0 := by
    rw [hcur]; exact yByte hp hP.com (by omega)
  have hP₁ : PCom s₀ i bound s₁ := hP.of_keep k₁ (by decide) (by rw [m₁]; exact Frame.refl _ _)
  rw [hbp, hbc, toNat_setWidth64_8, toNat_setWidth64_8] at cf₁
  refine WP.seq ?_
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from cf₁) (fun hlt => ?_) (fun hge => ?_)
  · -- `y[index - 1] < y[index]`: set it.
    have hs : huStep (uY s₀) i first (hA, idx) 0 = some (huSet i ((uY s₀).getD idx 0).toNat hA, idx + 1) := by
      simp only [huStep]
      rw [ite_neg' (by simp only [decide_eq_true_eq] at hlt; omega)]
    rw [hs]
    refine WP.mono (set_ok hp hi (idx := idx) (hA := hA) hP₁ (by rw [k₁.gpr (by decide), hax])
      (by rw [si₁, hbc]; apply BitVec.eq_of_toNat_eq; simp) (by rw [m₁]; exact hh)) fun s₂ ⟨hP₂, ax₂, hh₂, k₂⟩ => ?_
    refine WP.mono (cmpReg_ok .rax .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ =>
      ⟨hP₂.of_keep k₃ (by decide) (by rw [m₃]; exact Frame.refl _ _), ⟨by rw [k₃.gpr (by decide), ax₂],
        by rw [m₃]; exact hh₂, ?_⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    rw [cf₃, ax₂, hP₂.r11, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  · -- Not increasing: fail.
    have hs : huStep (uY s₀) i first (hA, idx) 0 = none := by
      simp only [huStep]
      rw [ite_pos' (by simp only [decide_eq_false_iff_not] at hge; omega)]
    rw [hs]
    refine WP.mono (hbuFail_ok s₁) fun s₂ ⟨⟨ax₂, m₂⟩, k₂⟩ => ?_
    refine WP.mono (cmpReg_ok .rax .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ =>
      ⟨hP₁.of_keep (k₂.trans k₃) (by decide) (by rw [m₃, m₂]; exact Frame.refl _ _),
        ⟨by rw [k₃.gpr (by decide), ax₂], ?_⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    rw [cf₃, ax₂, k₂.gpr (by decide), hP₁.r11, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    exact congrArg some (decide_eq_false (by omega))

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .rax = BitVec.ofNat 64 idx ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .rax = 256

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

include hp in
/-- The coefficients after the first. -/
theorem nexts_ok {i bound first : Nat} (hi : i < uk s₀) (hbω : bound ≤ uω s₀) {hA : Array (Vector Bool n)}
    {t : Nat} (ht1 : 1 ≤ t) {hA' : Array (Vector Bool n)} {idx' : Nat}
    (hF : optFold (huStep (uY s₀) i first) (List.range t) (hA, first) = some (hA', idx'))
    (hidx : idx' = first + t) (hlt : idx' < bound) {s : State} (hP : PCom s₀ i bound s)
    (hax : s.gpr .rax = BitVec.ofNat 64 idx') (hh : HArr s₀ s.mem hA') :
    WP isa (.loop hbuNext .b) s fun s' => PCom s₀ i bound s' ∧
      SIn s₀ bound (optFold (huStep (uY s₀) i first) (List.range (bound - first)) (hA, first)) s' ∧
      Keep [.r8, .rax, .rsi] s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧ 1 ≤ t ∧
      optFold (huStep (uY s₀) i first) (List.range t) (hA, first) = some (hA', idx') ∧ idx' = first + t ∧
      idx' < bound ∧ PCom s₀ i bound s' ∧ s'.gpr .rax = BitVec.ofNat 64 idx' ∧ HArr s₀ s'.mem hA' ∧
      Keep [.r8, .rax, .rsi] s s')
    (fun m s' ⟨t, hA', idx', hm, ht1, hF, hidx, hlt, hP', hax', hh', hk'⟩ => ?_) _ s
    ⟨t, hA', idx', rfl, ht1, hF, hidx, hlt, hP, hax, hh, Keep.refl _ _⟩
  refine WP.mono (next_ok hp hi (first := first) (by omega) hlt hbω hP' hax' hh') fun s'' ⟨hP'', hm'', hk''⟩ => ?_
  have hF1 : optFold (huStep (uY s₀) i first) (List.range (t + 1)) (hA, first) =
      huStep (uY s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
  cases hs : huStep (uY s₀) i first (hA', idx') 0 with
  | none =>
    rw [hs] at hm''
    obtain ⟨ax'', cf''⟩ := hm''
    refine .inl ⟨cf'', hP'', ?_, (hk'.trans hk'').mono (by decide)⟩
    have : optFold (huStep (uY s₀) i first) (List.range (t + 1)) (hA, first) = none := by
      rw [hF1]; exact hs
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega) this]
    exact ax''
  | some st =>
    rw [hs] at hm''
    obtain ⟨hA'', idx''⟩ := st
    obtain ⟨ax'', hh'', cf''⟩ := hm''
    have hi'' : idx'' = idx' + 1 := huStep_idx hs
    have hF2 : optFold (huStep (uY s₀) i first) (List.range (t + 1)) (hA, first) = some (hA'', idx'') := by
      rw [hF1]; exact hs
    by_cases e : idx'' < bound
    · refine .inr ⟨by show s''.cf = _; rw [cf'', decide_eq_true e], bound - idx'', by omega, t + 1, hA'', idx'', rfl,
        by omega, hF2, by omega, e, hP'', ax'', hh'', (hk'.trans hk'').mono (by decide)⟩
    · refine .inl ⟨by show s''.cf = _; rw [cf'', decide_eq_false e], hP'', ?_, (hk'.trans hk'').mono (by decide)⟩
      rw [show bound - first = t + 1 by omega, hF2]
      exact ⟨by omega, ax'', hh''⟩

theorem cmpRegs_ok (s : State) :
    WP isa (.block [.alu .cmp .rax (.reg .r11)]) s fun s' =>
      (s'.cf = some (decide ((s.gpr .rax).toNat < (s.gpr .r11).toNat)) ∧ s'.mem = s.mem) ∧ Keep [] s s' :=
  cmpReg_ok .rax .r11 s

include hp in
/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s) (hax : s.gpr .rax = BitVec.ofNat 64 first)
    (hh : HArr s₀ s.mem hA) :
    WP isa hbuCoefs s fun s' => PCom s₀ i bound s' ∧
      SIn s₀ bound (optFold (huStep (uY s₀) i first) (List.range (bound - first)) (hA, first)) s' ∧
      Keep [.r8, .rax, .rsi] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (cmpRegs_ok s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  have hP₁ : PCom s₀ i bound s₁ := hP.of_keep k₁ (by decide) (by rw [m₁]; exact Frame.refl _ _)
  rw [hax, hP.r11, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at cf₁
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from cf₁) (fun hlt => ?_) (fun hge => ?_)
  · -- The first coefficient, then the others.
    have hlt : first < bound := by simpa using hlt
    have hF1 : optFold (huStep (uY s₀) i first) (List.range 1) (hA, first) =
        some (huSet i ((uY s₀).getD first 0).toNat hA, first + 1) := by
      simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ite_false]; rfl
    refine WP.seq (WP.mono (first_ok hp hi hlt hbω (hA := hA) hP₁ (by rw [k₁.gpr (by decide), hax]) (by rw [m₁]; exact hh))
      fun s₂ ⟨hP₂, ax₂, hh₂, cf₂, k₂⟩ => ?_)
    refine WP.ite (M := isa) _ (show isa.eval .b s₂ = _ from cf₂) (fun hlt₂ => ?_) (fun hge₂ => ?_)
    · have hlt₂ : first + 1 < bound := by simpa using hlt₂
      exact WP.mono (nexts_ok hp hi hbω (Nat.le_refl 1) hF1 rfl hlt₂ hP₂ ax₂ hh₂) fun s₃ ⟨hP₃, hr₃, k₃⟩ =>
        ⟨hP₃, hr₃, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · have hge₂ : ¬ first + 1 < bound := by simpa using hge₂
      refine WP.block_nil ⟨hP₂, ?_, (k₁.trans k₂).mono (by decide)⟩
      rw [show bound - first = 1 by omega, hF1]
      exact ⟨by omega, ax₂, hh₂⟩
  · -- No coefficient.
    have hge : ¬ first < bound := by simpa using hge
    refine WP.block_nil ⟨hP₁, ?_, k₁.mono (by decide)⟩
    rw [show bound - first = 0 by omega]
    exact ⟨by omega, by rw [k₁.gpr (by decide), hax], by rw [m₁]; exact hh⟩

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uY s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ s
  r9 : s.gpr .r9 = s₀.gpr .rdi + BitVec.ofNat 64 (uω s₀ + i)
  rcx : s.gpr .rcx = s₀.gpr .rcx + BitVec.ofNat 64 (1024 * i)
  st : SRel s₀ (huS s₀ i) s

theorem bound_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r9) 1) :
    WP isa (.block [.movzx8 .r11 (at_ .r9 0), .alu .cmp .r11 (.reg .rax)]) s fun s' =>
      (s'.gpr .r11 = BitVec.setWidth 64 (s.mem (s.gpr .r9)) ∧
        s'.cf = some (decide ((s.mem (s.gpr .r9)).toNat < (s.gpr .rax).toNat)) ∧ s'.mem = s.mem) ∧
        Keep [.r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hin, toNat_setWidth64_8]

theorem polyTail_ok (s : State) :
    WP isa (.block [.alu .add .r9 (.imm 1), .alu .add .rcx (.imm 1024), .alu .sub .r10 (.imm 1)]) s fun s' =>
      (s'.gpr .r9 = s.gpr .r9 + 1 ∧ s'.gpr .rcx = s.gpr .rcx + 1024 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
        s'.zf = some (s.gpr .r10 - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.r9, .rcx, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 by decide]

include hp in
/-- Polynomial `i`: its checks and coefficients, unless a check failed. -/
theorem upoly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.alu .add .r9 (.imm 1), .alu .add .rcx (.imm 1024), .alu .sub .r10 (.imm 1)])) s
      fun s' => OInv s₀ (i + 1) s' ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0) ∧
        Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  have hrd := hp.1
  have e1 : uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  have hsucc : huS s₀ (i + 1) = (huS s₀ i).bind fun st => huPoly (uω s₀) (uY s₀) st i := optFold_range_succ _ _ _
  have hωeq : uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [uω, dArg]
  -- After the polynomial, whichever way it went.
  suffices h : WP isa hbuPoly s fun s' => UCom s₀ s' ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .r10 = s.gpr .r10 ∧ SRel s₀ (huS s₀ (i + 1)) s' ∧ Keep [.rax, .rsi, .r8, .r11] s s' by
    refine WP.seq (WP.mono h fun s₁ ⟨hc₁, r9₁, cx₁, r10₁, st₁, k₁⟩ => ?_)
    refine WP.mono (polyTail_ok s₁) fun s₂ ⟨⟨r9₂, cx₂, r10₂, z₂, m₂⟩, k₂⟩ => ⟨⟨hc₁.of_keep k₂ (by decide) (by decide)
      (by rw [m₂]; exact Frame.refl _ _), ?_, ?_, ?_⟩, by rw [r10₂, r10₁], by rw [z₂, r10₁],
      (k₁.trans k₂).mono (by decide)⟩
    · rw [r9₂, r9₁, hI.r9, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · rw [cx₂, cx₁, hI.rcx, BitVec.add_assoc, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
        BitVec.ofNat_add_ofNat, show 1024 * i + 1024 = 1024 * (i + 1) by omega]
    · -- `rax` and the memory of `h`: `SRel` does not look at the other registers.
      revert st₁
      cases huS s₀ (i + 1) with
      | none => exact fun h => by rw [SRel] at h ⊢; rw [k₂.gpr (by decide), h]
      | some st => obtain ⟨hA, idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [k₂.gpr (by decide), h1], h2, by rw [m₂]; exact h3⟩
  unfold hbuPoly
  refine WP.seq (WP.mono (cmpReg_ok .rdx .rax s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  have hc₁ : UCom s₀ s₁ := hI.com.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  cases hS : huS s₀ i with
  | none =>
    -- A check failed before: nothing.
    have hax : s.gpr .rax = 256 := by have := hI.st; rw [hS] at this; exact this
    rw [hI.com.rdx, hax, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl, Nat.mod_eq_of_lt (by omega)]
      at cf₁
    refine WP.ite (M := isa) false (by show Option.map _ s₁.cf = _; rw [cf₁]; simp; omega) (fun h => by cases h)
      fun _ => WP.block_nil ⟨hc₁, k₁.gpr (by decide), k₁.gpr (by decide), k₁.gpr (by decide), ?_, k₁.mono (by decide)⟩
    rw [hsucc, hS]
    exact (k₁.gpr (by decide)).trans hax
  | some st =>
    obtain ⟨hA, idx⟩ := st
    have hst := hI.st
    rw [hS] at hst
    obtain ⟨hax, hidx, hh⟩ := hst
    rw [hI.com.rdx, hax, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at cf₁
    refine WP.ite (M := isa) true (by show Option.map _ s₁.cf = _; rw [cf₁]; simp; omega) (fun _ => ?_)
      (fun h => by cases h)
    -- The bound.
    have hr9 : s₁.gpr .r9 = s₀.gpr .rdi + BitVec.ofNat 64 (uω s₀ + i) := (k₁.gpr (by decide)).trans hI.r9
    refine WP.seq (WP.mono (bound_ok s₁ (by
        rw [hc₁.rd, hc₁.wr, hrd, hr9]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨⟨r11₂, cf₂, m₂⟩, k₂⟩ => ?_)
    have hbd : s₁.mem (s₁.gpr .r9) = (uY s₀).getD (uω s₀ + i) 0 := by rw [hr9]; exact yByte hp hc₁ (by omega)
    have hc₂ : UCom s₀ s₂ := hc₁.of_keep k₂ (by decide) (by decide) (by rw [m₂]; exact Frame.refl _ _)
    have hbl := ((uY s₀).getD (uω s₀ + i) 0).isLt
    rw [hbd, k₁.gpr (by decide), hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at cf₂
    have hpoly := hsucc
    rw [hS] at hpoly
    simp only [Option.bind_some, huPoly] at hpoly
    refine WP.ite (M := isa) _ (show isa.eval .b s₂ = _ from cf₂) (fun hlt => ?_) (fun hge => ?_)
    · -- `bound < index`: fail.
      have hlt : ((uY s₀).getD (uω s₀ + i) 0).toNat < idx := by simpa using hlt
      refine WP.mono (hbuFail_ok s₂) fun s₃ ⟨⟨ax₃, m₃⟩, k₃⟩ => ⟨hc₂.of_keep k₃ (by decide) (by decide)
        (by rw [m₃]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
      · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
      · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
      · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
      · rw [hpoly, ite_pos' (.inl hlt)]; exact ax₃
    · have hge : ¬ ((uY s₀).getD (uω s₀ + i) 0).toNat < idx := by simpa using hge
      refine WP.seq (WP.mono (cmpReg_ok .rdx .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ => ?_)
      have hc₃ : UCom s₀ s₃ := hc₂.of_keep k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
      rw [hc₂.rdx, r11₂, hbd, toNat_setWidth64_8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at cf₃
      refine WP.ite (M := isa) _ (show isa.eval .b s₃ = _ from cf₃) (fun hgt => ?_) (fun hle => ?_)
      · -- `bound > ω`: fail.
        have hgt : uω s₀ < ((uY s₀).getD (uω s₀ + i) 0).toNat := by simpa using hgt
        refine WP.mono (hbuFail_ok s₃) fun s₄ ⟨⟨ax₄, m₄⟩, k₄⟩ => ⟨hc₃.of_keep k₄ (by decide) (by decide)
          (by rw [m₄]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [hpoly, ite_pos' (.inr hgt)]; exact ax₄
      · -- The coefficients.
        have hle : ¬ uω s₀ < ((uY s₀).getD (uω s₀ + i) 0).toNat := by simpa using hle
        have hP₃ : PCom s₀ i ((uY s₀).getD (uω s₀ + i) 0).toNat s₃ :=
          ⟨hc₃, by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hI.rcx],
            by rw [k₃.gpr (by decide), r11₂, hbd]; apply BitVec.eq_of_toNat_eq; simp⟩
        refine WP.mono (coefs_ok hp hi (first := idx) (hA := hA) (by omega) (by omega) hP₃
          (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hax])
          (by rw [m₃, m₂, m₁]; exact hh)) fun s₄ ⟨hP₄, hin₄, k₄⟩ => ⟨hP₄.com, ?_, ?_, ?_, ?_,
            (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [hP₄.rcx, hI.rcx]
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [hpoly, ite_neg' (by omega)]
          revert hin₄
          cases optFold (huStep (uY s₀) i idx) (List.range (((uY s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA, idx) with
          | none => exact id
          | some st => obtain ⟨hA', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega, h3⟩

/-! ## The bytes after the last index -/

theorem trailLoad_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax) 1) :
    WP isa (.block [.movzx8 .r8 (atIdx .rdi .rax), .alu32 .cmp .r8 (.imm 0)]) s fun s' =>
      (s'.zf = some (BitVec.setWidth 32 (BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax))) - 0 == 0) ∧
        s'.mem = s.mem) ∧ Keep [.r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_idx, hin]

theorem incRax_ok (s : State) :
    WP isa (.block [.alu .add .rax (.imm 1)]) s fun s' =>
      (s'.gpr .rax = s.gpr .rax + 1 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem byte_ne_zero (b : Byte) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 b) - 0 == 0) = decide (b = 0) := by
  rw [VG.Proof.MlKem.X86_64.sub_beq_zero32]
  simp only [decide_eq_decide]
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    have h2 := b.isLt
    simp only [BitVec.toNat_setWidth] at h1
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at h1
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Byte).toNat = 0 from rfl]
    omega
  · intro h; rw [h]; rfl

include hp in
/-- The bytes from the index `idx` up to `ω`. -/
theorem trail_ok {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ s)
    (hax : s.gpr .rax = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (uY s₀)) (List.range' idx (uω s₀ - idx)) () with
        | some _ => s'.gpr .rax = BitVec.ofNat 64 (uω s₀)
        | none => s'.gpr .rax = 256) ∧ Keep [.rax, .r8] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  have hrd := hp.1
  have e1 : uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  have hωeq : uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [uω, dArg]
  unfold hbuTrail
  refine WP.seq (WP.mono (cmpReg_ok .rax .rdx s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  have hc₁ : UCom s₀ s₁ := hc.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  rw [hax, hc.rdx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at cf₁
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from cf₁) (fun hlt => ?_) (fun hge => ?_)
  · have hlt : idx < uω s₀ := by simpa using hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
        optFold (huTrail (uY s₀)) (List.range' idx u) () = some () ∧ s'.gpr .rax = BitVec.ofNat 64 (idx + u) ∧
        UCom s₀ s' ∧ s'.mem = s.mem ∧ Keep [.rax, .r8] s s')
      (fun m s' ⟨u, hm, hu, hF, hax', hc', hm', hk'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega, rfl, by rw [k₁.gpr (by decide), hax]; rfl, hc₁, m₁, k₁.mono (by decide)⟩
    refine WP.seq (WP.mono (trailLoad_ok s' (by
        rw [hc'.rd, hc'.wr, hrd, hc'.rdi, hax']
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    have hbyte : s'.mem (s'.gpr .rdi + s'.gpr .rax) = (uY s₀).getD (idx + u) 0 := by
      rw [hc'.rdi, hax']; exact yByte hp hc' (by omega)
    rw [hbyte, byte_ne_zero] at z₂
    have hc₂ : UCom s₀ s₂ := hc'.of_keep k₂ (by decide) (by decide) (by rw [m₂]; exact Frame.refl _ _)
    have hF1 : optFold (huTrail (uY s₀)) (List.range' idx (u + 1)) () =
        huTrail (uY s₀) () (idx + u) := by rw [optFold_range'_succ, hF]; rfl
    refine WP.seq ?_
    refine WP.ite (M := isa) _ (show Option.map _ s₂.zf = _ by rw [z₂]; rfl) (fun hne => ?_) (fun heq => ?_)
    · -- A nonzero byte: fail.
      have hne : (uY s₀).getD (idx + u) 0 ≠ 0 := by simpa using hne
      have hn : optFold (huTrail (uY s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono (hbuFail_ok s₂) fun s₃ ⟨⟨ax₃, m₃⟩, k₃⟩ => ?_
      refine WP.mono (cmpReg_ok .rax .rdx s₃) fun s₄ ⟨⟨cf₄, m₄⟩, k₄⟩ => .inl ⟨?_, ⟨hc₂.of_keep (k₃.trans k₄) (by decide)
        (by decide) (by rw [m₄, m₃]; exact Frame.refl _ _), by rw [m₄, m₃, m₂, hm'], ?_,
        (((hk'.trans k₂).trans k₃).trans k₄).mono (by decide)⟩⟩
      · show s₄.cf = _
        rw [cf₄, ax₃, k₃.gpr (by decide), hc₂.rdx, show (256 : BitVec 64).toNat = 256 from rfl, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
        exact congrArg some (decide_eq_false (by omega))
      · rw [hn]; exact (k₄.gpr (by decide)).trans ax₃
    · -- A zero byte: next.
      have heq : (uY s₀).getD (idx + u) 0 = 0 := by simpa using heq
      have hF2 : optFold (huTrail (uY s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' (by simpa using heq)]
      refine WP.mono (incRax_ok s₂) fun s₃ ⟨⟨ax₃, m₃⟩, k₃⟩ => ?_
      have ax₃' : s₃.gpr .rax = BitVec.ofNat 64 (idx + (u + 1)) := by
        rw [ax₃, k₂.gpr (by decide), hax', ofNat_succ64, Nat.add_assoc]
      refine WP.mono (cmpReg_ok .rax .rdx s₃) fun s₄ ⟨⟨cf₄, m₄⟩, k₄⟩ => ?_
      have hc₄ : UCom s₀ s₄ := hc₂.of_keep (k₃.trans k₄) (by decide) (by decide) (by rw [m₄, m₃]; exact Frame.refl _ _)
      rw [ax₃', k₃.gpr (by decide), hc₂.rdx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at cf₄
      have ax₄ : s₄.gpr .rax = BitVec.ofNat 64 (idx + (u + 1)) := (k₄.gpr (by decide)).trans ax₃'
      by_cases e : idx + (u + 1) < uω s₀
      · exact .inr ⟨by show s₄.cf = _; rw [cf₄, decide_eq_true e], _, by omega, u + 1, rfl, e, hF2, ax₄, hc₄,
          by rw [m₄, m₃, m₂, hm'], (((hk'.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
      · refine .inl ⟨by show s₄.cf = _; rw [cf₄, decide_eq_false e], hc₄, by rw [m₄, m₃, m₂, hm'], ?_,
          (((hk'.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
        rw [show uω s₀ - idx = u + 1 by omega, hF2]
        rw [ax₄, show idx + (u + 1) = uω s₀ by omega]
  · -- `idx = ω`: nothing.
    have hge : ¬ idx < uω s₀ := by simpa using hge
    refine WP.block_nil ⟨hc₁, m₁, ?_, k₁.mono (by decide)⟩
    rw [show uω s₀ - idx = 0 by omega]
    simp only [List.range'_zero, optFold]
    rw [k₁.gpr (by decide), hax, show idx = uω s₀ by omega]

include hp in
theorem trail_fail {s : State} (hc : UCom s₀ s) (hax : s.gpr .rax = 256) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .rax = 256 ∧ Keep [.rax, .r8] s s' := by
  obtain ⟨-, -, hω80, -, -⟩ := up_facts hp
  have hωeq : uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [uω, dArg]
  unfold hbuTrail
  refine WP.seq (WP.mono (cmpReg_ok .rax .rdx s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  rw [hax, hc.rdx, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl, Nat.mod_eq_of_lt (by omega)] at cf₁
  refine WP.ite (M := isa) false (by show s₁.cf = _; rw [cf₁]; exact congrArg some (decide_eq_false (by omega)))
    (fun h => by cases h) fun _ => WP.block_nil ⟨hc.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _),
      m₁, (k₁.gpr (by decide)).trans hax, k₁.mono (by decide)⟩

/-! ## The function -/

theorem hbuSetup_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rdi), .alu .add .r9 (.reg .rdx), .mov .r10 (.reg .rsi), .alu .sub .r10 (.reg .rdx)])
      s fun s' => (s'.gpr .r9 = s.gpr .rdi + s.gpr .rdx ∧ s'.gpr .r10 = s.gpr .rsi - s.gpr .rdx ∧ s'.mem = s.mem) ∧
        Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem hbuRet_ok (s : State) :
    WP isa (.block hbuRet) s fun s' =>
      (BitVec.setWidth 32 (s'.gpr .rax) = if (s.gpr .rdx).toNat < (s.gpr .rax).toNat then 0 else 1) ∧ s'.mem = s.mem := by
  unfold hbuRet
  xrun
  split
  · rename_i h; rw [decide_eq_true h]; rfl
  · rename_i h; rw [decide_eq_false h]; rfl

include hp in
/-- The polynomials. -/
theorem hbuMain_ok {s : State} (hc : UCom s₀ s) (hax : s.gpr .rax = 0)
    (hz : ∀ t < (s₀.gpr .r8).toNat, coeffAt s.mem (s₀.gpr .rcx) t = 0) (hcx : s.gpr .rcx = s₀.gpr .rcx)
    (hsi : s.gpr .rsi = s₀.gpr .rsi) :
    WP isa hbuMain s fun s' => OInv s₀ (uk s₀) s' ∧ Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  have e1 : uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have e2 : uk s₀ = (s₀.gpr .rsi).toNat - uω s₀ := rfl
  have hωeq : uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [uω, dArg]
  unfold hbuMain
  refine WP.seq (WP.mono (hbuSetup_ok s) fun s₁ ⟨⟨r9₁, r10₁, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .r10) (N := uk s₀) (by omega) (by omega)
    (fun i s' => OInv s₀ i s' ∧ Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s s')
    (fun i hi s' ⟨hI, hk⟩ _ => WP.mono (upoly_ok hp hi hI) fun s'' ⟨hI', h10, hz', hk'⟩ =>
      ⟨⟨hI', (hk.trans hk').mono (by decide)⟩, h10, hz'⟩)
    (fun s' h => h) (s := s₁) ⟨⟨hc.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _), ?_, ?_, ?_⟩,
      k₁.mono (by decide)⟩ ?_) fun s' h => h
  · rw [r9₁, hc.rdi, hc.rdx]; rfl
  · rw [k₁.gpr (by decide), hcx]; simp
  · show SRel s₀ (some (Array.replicate (uk s₀) noHint, 0)) s₁
    exact ⟨by rw [k₁.gpr (by decide), hax]; rfl, Nat.zero_le _, by rw [m₁]; exact harr_zero hp hz⟩
  · rw [r10₁, hsi, hc.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := (s₀.gpr .rsi).isLt
    omega

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) :
    HintIs m (s₀.gpr .rcx) (uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

include hp in
theorem hbu_wp :
    WP isa Impl.MlDsa.X86_64.Pack.hintBitUnpack s₀ fun s' =>
      hintBitUnpackK.post s₀ s' ∧ Frame [uR s₀] s₀.mem s'.mem := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := up_facts hp
  have hωeq : uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [uω, dArg]
  unfold Impl.MlDsa.X86_64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (hbuZero_ok hp) fun s₁ ⟨hz₁, hf₁, ax₁, dx₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (hbuMain_ok hp (s := s₁) ⟨k₁.gpr (by decide), dx₁, k₁.2.1, k₁.2.2, hf₁⟩ ax₁ hz₁
    (k₁.gpr (by decide)) (k₁.gpr (by decide))) fun s₂ ⟨hI, k₂⟩ => ?_)
  -- The spec, as folds.
  show WP isa _ s₂ fun s' => (match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat) with
    | some hint => BitVec.setWidth 32 (s'.gpr .rax) = 1 ∧ HintIs s'.mem (s₀.gpr .rcx) (uk s₀) hint
    | none => BitVec.setWidth 32 (s'.gpr .rax) = 0) ∧ Frame [uR s₀] s₀.mem s'.mem
  rw [hintBitUnpack_eq]
  have hst := hI.st
  cases hS : huS s₀ (uk s₀) with
  | none =>
    rw [hS] at hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = none from hS]
    refine WP.seq (WP.mono (trail_fail hp hI.com hst) fun s₃ ⟨hc₃, m₃, ax₃, k₃⟩ => ?_)
    refine WP.mono (hbuRet_ok s₃) fun s₄ ⟨ax₄, m₄⟩ => ⟨?_, by rw [m₄, m₃]; exact hI.com.frame⟩
    rw [ax₄, ax₃, hc₃.rdx, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl, Nat.mod_eq_of_lt (by omega),
      ite_pos' (by omega)]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hS] at hst
    obtain ⟨hax, hidx, hh⟩ := hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = some (hA, idx) from hS]
    refine WP.seq (WP.mono (trail_ok hp hidx hI.com hax) fun s₃ ⟨hc₃, m₃, hr₃, k₃⟩ => ?_)
    refine WP.mono (hbuRet_ok s₃) fun s₄ ⟨ax₄, m₄⟩ => ⟨?_, by rw [m₄, m₃]; exact hI.com.frame⟩
    dsimp only
    revert hr₃
    cases optFold (huTrail (uY s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      intro hr₃
      rw [ax₄, hr₃, hc₃.rdx, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl,
        Nat.mod_eq_of_lt (by omega), ite_pos' (by omega)]
      rfl
    | some _ =>
      intro hr₃
      refine ⟨?_, by rw [m₄, m₃]; exact harr_hintIs hh⟩
      rw [ax₄, hr₃, hc₃.rdx, ite_neg' (Nat.lt_irrefl _)]

end

theorem hintBitUnpack_correct (s : State) (hs : hintBitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.hintBitUnpack s t s' ∧ abiPreserved s s' ∧ hintBitUnpackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.hintBitUnpack)
    [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11] (hbu_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

/-! ## Constant time -/

/-- A byte of the words of a region of zero words. -/
theorem byte_of_zero_words {m : Mem} {p : Addr} {N : Nat} (hz : ∀ t < N, coeffAt m p t = 0) {a : Addr}
    (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m a = 0 := by
  simp only [Region.Contains] at ha
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m (coeffAddr p _) ht, ← coeffAt_eq, hz _ (by omega)]
  simp

theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The taint of the loops: the pointers, the lengths, `ω` and the index. -/
abbrev hbuTaint : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rax]

theorem hintBitUnpack_ct :
    ConstantTime isa hintBitUnpackK.pre hintBitUnpackK.pub Impl.MlDsa.X86_64.Pack.hintBitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := MAgree hbuTaint) ?_ (RelCT.taint (A := memTaint) hbuTaint (fun _ _ h => h) (by taint_decide))
  refine Proof.MlKem.X86_64.RelCT.postDep
    (RelCT.taint (A := taint) (regsLo [.rdi, .rsi, .rcx, .r8, .rsp] [.rdx])
      (fun _ _ ⟨_, _, hp⟩ => agree_regsLo (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1])
        fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2.2.1)
      (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨hbuZero_ok hx, hbuZero_ok hy⟩) fun x y x' y' ⟨hx, hy, hp⟩ fx fy => ?_
  obtain ⟨hz₁, hf₁, ax₁, dx₁, k₁⟩ := fx
  obtain ⟨hz₂, hf₂, ax₂, dx₂, k₂⟩ := fy
  obtain ⟨di, si, ci, r8, -, dx, hleak⟩ := hp
  have hdx : dArg x .rdx = dArg y .rdx := by unfold dArg; rw [dx]
  have hrd : x'.rd = y'.rd := by rw [k₁.2.1, k₂.2.1, hx.1, hy.1, di, si]
  have hwr : x'.wr = y'.wr := by rw [k₁.2.2, k₂.2.2, hx.2.1, hy.2.1, ci, r8]
  refine ⟨X86_64.Taint.agree_ofRegs fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), di]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), si]
    · rw [dx₁, dx₂]; exact congrArg _ hdx
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), ci]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), r8]
    · rw [ax₁, ax₂]
  · rw [k₁.2.1, k₁.2.2, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `y`: as on entry, where the runs agree.
      have hdis : ∀ r ∈ [uR x], ¬ r.Contains a 1 := by
        intro r hr hc'; simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'
      rw [hf₁ a hdis, hf₂ a (fun r hr hc' => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [uR, ← ci, ← r8] at hc'
        exact hx.2.2.1 a hc hc')]
      have hlt : (a - x.gpr .rdi).toNat < (x.gpr .rsi).toNat := by simp only [Region.Contains] at hc; omega
      have ea : a = x.gpr .rdi + BitVec.ofNat 64 (a - x.gpr .rdi).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hb : bytesAt x.mem (x.gpr .rdi) (x.gpr .rsi).toNat = bytesAt y.mem (x.gpr .rdi) (x.gpr .rsi).toNat := by
        have hl2 := hleak
        rw [← di, ← si] at hl2
        exact map_toNat_inj hl2
      have h₁ := congrArg (·.getD (a - x.gpr .rdi).toNat 0) hb
      rw [bytesAt_getD _ _ hlt, bytesAt_getD _ _ hlt, ← ea] at h₁
      exact h₁
    · -- `h`: zeros.
      rw [byte_of_zero_words hz₁ hc, byte_of_zero_words hz₂ (by rw [← ci, ← r8]; exact hc)]

/-- A state satisfying the precondition. -/
def hintBitUnpackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 84 | .rdx => 80 | .rcx => 0x3000 | .r8 => 1024 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 84⟩]
  wr := [⟨0x3000, 4096⟩]

theorem hintBitUnpack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.hintBitUnpack (hintBitUnpackContract X86_64.abi) :=
  Verified.of_correct hintBitUnpack_correct hintBitUnpack_ct
    { pre := by sig_implies_pre [hintBitUnpackContract, hintBitUnpackSig, hintBitUnpackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [hintBitUnpackContract, hintBitUnpackSig, hintBitUnpackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [hintBitUnpackContract, hintBitUnpackSig, hintBitUnpackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨hintBitUnpackSat, ?_⟩
        sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack
