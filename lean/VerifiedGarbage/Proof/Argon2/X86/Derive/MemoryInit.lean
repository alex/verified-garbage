import VerifiedGarbage.Proof.Argon2.X86.Derive.Clear
import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.Matrix

/-!
# Argon2 on x86 (32-bit): the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared, then each
lane's first two blocks are H′ of the 72 bytes at the start of the locals
(`initBlock_ok`), H₀ followed by the column and the lane, written there just
before the call. `LI s₀ h0 l` is the state after `l` lanes (`initCell`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block blockAt zeroBlock parseBlock)

/-! ## Blocks in memory -/

/-- A block outside a frame's regions is kept. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 1024⟩ r) : blockAt m' p = blockAt m p := by
  unfold blockAt
  exact congrArg Vector.ofFn (funext fun j => f.read (r := ⟨p, 1024⟩)
    (Offset.contains_base p (by have := j.isLt; omega) (by have := j.isLt; omega)) hd (by decide))

theorem read_zero {m : Mem} {a : Addr} {n : Nat} (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = 0) :
    m.read a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 : m a = 0 := by simpa using h 0 (by omega)
    have h1 : m.read (a + 1) n = 0 := ih fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact h (1 + i) (by omega)
    simp only [Mem.read, h0, h1]
    exact BitVec.zero_append_zero

/-- A block of zero bytes. -/
theorem blockAt_zero {m : Mem} {p : Addr} (h : ∀ i < 1024, m (p + BitVec.ofNat 64 i) = 0) :
    blockAt m p = zeroBlock := by
  unfold blockAt zeroBlock
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  exact read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) : initCell p h0 0 k = zeroBlock := by
  unfold initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen) (hc : c < 2) :
    initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold initCell
  rw [cell_div (by omega), cell_mod (by omega)]
  exact ite_eq_left ⟨by omega, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    initCell p h0 (l + 1) k = initCell p h0 l k := by
  unfold initCell
  have hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega), ite_eq_left hc]
    · rw [ite_eq_right (by omega), ite_eq_right hc]

/-! ## A lane's first blocks -/

/-- A store to the locals at `d` keeps their first `n ≤ d` bytes. -/
theorem loc_bytes_store {s₀ : State} (hp : DPre s₀) {m : Mem} {d n : Nat} (hn : n ≤ d) (hd : d + 4 ≤ 144)
    (v : BitVec 32) :
    bytesAt (m.writeW (addr (E s₀) d) v) ((E s₀).setWidth 64) n = bytesAt m ((E s₀).setWidth 64) n := by
  have := E_hi hp
  refine bytes_keep
    ((Frame.refl [⟨addr (E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  exact disj32 (.inl (by rw [add_nat (by omega)]; omega)) (by omega) (by rw [add_nat (by omega)]; omega)

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, bytes_word, bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- The call's frame lies in the body's regions. -/
theorem call_sub {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first 64 bytes of the locals are outside a call's frame. -/
theorem h0_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], Region.Disjoint ⟨(E s₀).setWidth 64, 64⟩ r := by
  have sub : Region.Sub ⟨(E s₀).setWidth 64, 64⟩ (locR s₀) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((loc_disj' hp (R := memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((loc_disj' hp (R := outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sub
  · exact (loc_call hp).sub_left sub

/-- A cell of the memory matrix is outside `scratch`, `out`'s and the stack below the locals. -/
theorem cell_disj {k : Nat} (hk : k < blocksN s₀) :
    ∀ r ∈ [scrR s₀, callR s₀], Region.Disjoint ⟨matrixCell (memB s₀) k, 1024⟩ r := by
  have sub : Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub

theorem cell_addr {k : Nat} (hk : k < blocksN s₀) :
    (memP s₀ + BitVec.ofNat 32 (k * 1024)).setWidth 64 = matrixCell (memB s₀) k := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  exact HPrime.setWidth_add (by omega)

omit hp in
theorem cell_in_mem {k : Nat} (hk : k < blocksN s₀) :
    Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < blocksN s₀) (hk : k < blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (memB s₀) j, 1024⟩ ⟨matrixCell (memB s₀) k, 1024⟩ :=
  matrixCell_disjoint _ _ _ _ (by have := hp.blocks_lt; omega) hj hk ne

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0) {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2)
    (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.X86.Derive.initBlock c) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 = h0 ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧
      blockAt t.mem (matrixCell (memB s₀) (l * (prm s₀).laneLen + c)) = parseBlock (initialBytes h0 l c) ∧
      ∀ k < blocksN s₀, k ≠ l * (prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k) := by
  have hE := E_hi hp
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine WP.seq (wp_movi fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ v₂ o₂ g₂ m₂ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := ((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide)
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₆.gpr r = s.gpr r := fun r a b d => by
    rw [u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  have ebp₆ : s₆.gpr .ebp = E s₀ := i₆.ebp
  have eax₆ : (s₆.gpr .eax).toNat = 72 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
  have ecx₆ : (s₆.gpr .ecx).toNat = 1024 := by rw [u₆.other _ (by decide), u₅.gpr]; rfl
  have edi₆ : s₆.gpr .edi = s.gpr .edi := g₆ _ (by decide) (by decide) (by decide)
  have O : (s₆.gpr .edi).setWidth 64 = matrixCell (memB s₀) (l * (prm s₀).laneLen + c) := by
    rw [edi₆, edi, cell_addr hp hcell]
  have sO : Region.Sub ⟨(s₆.gpr .edi).setWidth 64, (s₆.gpr .ecx).toNat⟩ (memR s₀) := by
    rw [O, ecx₆]; exact cell_in_mem hcell
  have hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  refine hcall_ok hp i₆ (r := .ebp) (by decide) u₆.gpr
    ⟨locR s₀, by simp, 0, by rw [ebp₆]; simp, by rw [eax₆]; show 0 + 72 ≤ 144; omega⟩ (by rw [ebp₆, eax₆]; omega)
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [O]; rfl, by rw [ecx₆]; exact hcell'⟩
    (by rw [edi₆, edi, ecx₆, add_nat (by omega)]; omega) (by rw [ecx₆]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parameters.
    exact Prm.of_lw pr fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      have hd' : 72 ≤ d ∧ d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
      rw [lw_keep hp fr (call_sub (.inl sO)) hd'.2, lw_mem m₆, o₃ d (by omega) (by omega),
        o₂ d (by omega) (by omega), lw_mem u₁.mem]
  · rw [bytes_keep fr (h0_call hp (.inl sO)) (by omega), m₆, m₃,
      loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide), u₁.mem, b0]
  · rw [cs .esi (by decide), g₆ _ (by decide) (by decide) (by decide)]
  · rw [cs .edi (by decide), edi₆]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← O, ← ecx₆, post, ecx₆, ebp₆, eax₆, bytes72, m₆]
    have w64 : s₃.mem.readW ((E s₀).setWidth 64 + BitVec.ofNat 64 64) 32 = BitVec.ofNat 32 c := by
      rw [← addr_eq (by omega)]
      show lw s₀ s₃ 64 = _
      rw [o₃ 64 (by decide) (by decide), v₂, u₁.gpr]
    have w68 : s₃.mem.readW ((E s₀).setWidth 64 + BitVec.ofNat 64 68) 32 = BitVec.ofNat 32 l := by
      rw [← addr_eq (by omega)]
      show lw s₀ s₃ 68 = _
      rw [v₃, g₂, u₁.other _ (by decide), esi]
    rw [w64, w68, m₃, loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    have fs : Frame [⟨addr (E s₀) 64, 4⟩, ⟨addr (E s₀) 68, 4⟩] s.mem s₃.mem := by
      rw [m₃, m₂, u₁.mem]
      exact ((Frame.refl _ _).writeW (w := 32) List.mem_cons_self _ (Region.contains_self _ _)).writeW (w := 32)
        (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
    rw [blockAt_keep fr (fun r hr => ?_), m₆]
    · -- The stores to the locals.
      refine blockAt_keep fs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((loc_disj hp (d := 64) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
      · exact ((loc_disj hp (d := 68) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [O, ecx₆]; exact cell_other hp hk hcell ne
      · exact cell_disj hp hk _ (by simp)
      · exact cell_disj hp hk _ (by simp)

end

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0
  esi : s.gpr .esi = BitVec.ofNat 32 l
  edi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (l * (prm s₀).laneLen * 1024)
  cells : ∀ k < blocksN s₀, blockAt s.mem (matrixCell (memB s₀) k) = initCell (prm s₀) h0 l k

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  Prm.of_lw pr fun d _ => lw_mem h d

theorem edi_next (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + 1024 + BitVec.ofNat 32 b - 1024 = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc (x + _) 1024, BitVec.add_comm 1024 (BitVec.ofNat 32 b), ← BitVec.add_assoc,
    BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < lanesN s₀) (h : LI s₀ h0 l s) :
    WP isa Impl.Argon2.X86.Derive.initLane s fun t =>
      LI s₀ h0 (l + 1) t ∧ t.cf = some (decide (l + 1 < lanesN s₀)) := by
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hlt := hp.lanes_lt
  unfold Impl.Argon2.X86.Derive.initLane
  refine WP.seq ((initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.esi
    (by rw [h.edi, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_addi fun s₂ u₂ => WP.block_nil ?_)
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine WP.seq ((initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1) (by decide)
    (by rw [u₂.other _ (by decide), e₁, h.esi]) (by rw [u₂.gpr, d₁, h.edi, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, Nat.succ_mul])).mono fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.X86.Derive.nextLane, Impl.Argon2.X86.Derive.fr]
  refine wp_ldloc hp i₃ (d := Impl.Argon2.X86.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add fun s₅ u₅ _ => wp_subi fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
    (by decide)).upd u₇ (by decide) (by decide)
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (l + 1) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      u₂.other _ (by decide), e₁, h.esi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmpm i₇.ebp (i₇.arg_in hp (i := 7) (by decide)) fun t f c _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact i₇.step (by rw [f.gpr]) (by rw [f.gpr]) f.rd f.wr (by rw [f.mem]; exact Frame.refl _ _)
  · exact p₃.of_mem (by rw [f.mem, m₇])
  · rw [f.mem, m₇, b₃]
  · rw [f.gpr, esi₇]
  · rw [f.gpr, u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), d₃, u₂.gpr, d₁, h.edi,
      p₃.stride, edi_next, Nat.succ_mul, Nat.add_mul]
  · intro k hk
    rw [f.mem, m₇]
    by_cases k1 : k = l * (prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (prm s₀).laneLen = l * (prm s₀).laneLen + 0 from rfl, w₁]
      exact (initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega), h.cells k hk, initCell_old _ _ k0 k1]
  · rw [c, esi₇, i₇.arg hp (by decide), Wp.toNat_ofNat_lt (by omega)]; rfl

/-- `clear`, from the body with H₀ in the locals. -/
theorem clearW_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0) :
    WP isa Impl.Argon2.X86.Derive.clear s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        t.mem ((memP s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  refine (clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [memR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact lw_keep hp f₁ fsub (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
  · rw [bytes_keep f₁ (fun r hr => ?_) (by omega), b0]
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj' hp (R := memR s₀) (by simp)).sub_left (Region.sub_prefix (by decide))

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧
      bytesAt s.mem ((E s₀).setWidth 64) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        s.mem ((memP s₀).setWidth 64 + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [.mov .edi (Impl.Argon2.X86.Derive.fr (Impl.Argon2.X86.Derive.argOff 13)), .mov .esi (.imm 0)]) s (LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine wp_ldarg hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_movi fun s₃ u₃ => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [initCell_zero, m₃]
    refine blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega)

theorem memoryInit_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0) :
    WP isa Impl.Argon2.X86.Derive.memoryInit s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Represents t.mem (memB s₀) (prm s₀).blocks (Spec.Argon2.initMemory (prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have hb := hp.blocks_lt
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine WP.seq ((clearW_ok hp h pr b0).mono fun s₁ h₁ => WP.seq ((laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ LI s₀ h0 l t) ?_
    (lanesN s₀) s₃ ⟨0, by omega, by omega, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 < lanesN s₀
  · refine .inr ⟨by simp only [eval, cu, done, decide_true], lanesN s₀ - (l + 1), by omega, l + 1, rfl, done, hu⟩
  · refine .inl ⟨by simp only [eval, cu, done, decide_false], hu.inv, hu.pr, ?_⟩
    have hl' : l + 1 = lanesN s₀ := by omega
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, initCell, hl']
    have : k / (prm s₀).laneLen < lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]

end

end VG.Proof.Argon2.X86.Derive
