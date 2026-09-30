import VerifiedGarbage.Proof.MlKem.X86_64.S4Absorb

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, squeezing

Untrusted: everything here is checked by Lean. The padded seeds are the
states that `Keccak-f` turns into the absorbed ones (`padded_A0`), and the
four states hold them after `absorb4` (`lanes_A0`). Each `squeeze4 n`
permutes the four states (`permute4_ok`) and copies the first 168 bytes of
each to its output, which then holds the first `168 (n + 1)` bytes of the
seed's XOF output (`sq_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (padded xofByte)
open VG.Proof.Sha3.X86_64.X4 (la ba Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok)

/-! ## The padded seeds -/

/-- The state whose permutation is the absorbed padded seed. -/
def A0 (Bs : List Byte) : Spec.Sha3.State := xorByte (xorByte (Rep 168 Bs) 34 0x1f) 167 0x80

theorem padded_A0 {Bs : List Byte} (h : Bs.length = 34) :
    padded 168 Spec.Sha3.shakeSuffix Bs = keccakF (A0 Bs) := by
  rw [padded, absorb_pad (by decide) (by decide), h]; rfl

theorem byteOf_A0 {Bs : List Byte} (h : Bs.length = 34) {q : Nat} (hq : q < 200) :
    byteOf (A0 Bs) q = if q < 34 then Bs.getD q 0 else if q = 34 then 0x1f else if q = 167 then 0x80 else 0 := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have ha : Spec.Sha3.absorb 168 Bs = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, h]
  have hr : byteOf (Rep 168 Bs) q = Bs.getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, h, show 168 * (34 / 168) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hd : ∀ q, 34 ≤ q → Bs.getD q 0 = 0 := fun q hq' => by
    rw [List.getD, List.getElem?_eq_none (by omega)]; rfl
  rw [A0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr]
  by_cases e1 : q < 34
  · rw [ifn (show ¬ q = 167 by omega), ifn (show ¬ q = 34 by omega), ifp e1]
  · rw [ifn e1, hd q (by omega)]
    by_cases e2 : q = 34
    · rw [ifn (show ¬ q = 167 by omega), ifp e2, ifp e2]; exact BitVec.zero_xor
    · rw [ifn e2, ifn e2]
      by_cases e3 : q = 167
      · rw [ifp e3, ifp e3]; exact BitVec.zero_xor
      · rw [ifn e3, ifn e3]

theorem B_length (σ : State) (k : Nat) : (B σ k).length = 34 := VG.Proof.Sha3.bytesAt_length _ _ _

/-- Byte `p` of the XOF output of `Bs`, from the states. -/
theorem xofByte_A0 {Bs : List Byte} (h : Bs.length = 34) {n p : Nat} (hp : p < 168) :
    xofByte Bs (168 * n + p) = byteOf (iterF (n + 1) (A0 Bs)) p := by
  rw [xofByte, show (168 * n + p) / 168 = n by omega, show (168 * n + p) % 168 = p by omega, padded_A0 h,
    iterF_keccakF]

/-! ## `Env` after writes -/

/-- `Env` after writes below the saved registers. -/
theorem Env.low {σ s s' : State} (he : Env σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨scr σ, oSave⟩)
    (hf : Frame rs s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Offset.base_disjoint (scr σ) (k := oSave)
        (e := oSave + 8 * i) (n := 8) (by omega) (by simp only [oSave]; omega)).symm).sub_right (hrs r hr))
      (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ⟨scrR σ, by simp, fun x hx => Offset.sub_base (scr σ) (d := 0)
      (n := oSave) (k := 8192) (by simp only [oSave]; omega) x (by rw [BitVec.add_zero]; exact hrs r hr x hx)⟩)

/-- `Env` after code that writes no memory and keeps its registers. -/
theorem Env.keep {σ s s' : State} (he : Env σ s) (hm : s'.mem = s.mem) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], r ∉ rs) : Env σ s' :=
  Env.low he (rs := []) (by simp) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2 fun r hr => hk.gpr (hrs r hr)

/-! ## The squeezes -/

/-- After `n` squeezes. -/
structure SqInv (σ : State) (n : Nat) (s : State) : Prop where
  env : Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) fun k => iterF n (A0 (B σ k))
  buf : ∀ k < 4, ∀ p < 168 * n, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p

theorem lanes_A0 {σ : State} {m : Mem} (h : SB σ m (PF σ)) : Lanes4 m (scr σ) fun k => iterF 0 (A0 (B σ k)) :=
  lanes4_of_bytes fun k hk q hq => by
    rw [h k hk q hq, show iterF 0 (A0 (B σ k)) = A0 (B σ k) from rfl, byteOf_A0 (B_length σ k) hq, PF]



theorem la_tbl (σ : State) (r k : Nat) : la (at' σ 1600) r k = la (scr σ) (50 + r) k := by
  rw [la, la, at', Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega]

theorem sx800 : BitVec.signExtend 64 (BitVec.ofNat 32 oTmp) = BitVec.ofNat 64 800 := by decide
theorem sx1600 : BitVec.signExtend 64 (BitVec.ofNat 32 oRc) = BitVec.ofNat 64 1600 := by decide
theorem sx2368 : BitVec.signExtend 64 (BitVec.ofNat 32 oBuf) = BitVec.ofNat 64 2368 := by decide

theorem args_ok {σ s : State} (he : Env σ s) :
    WP isa (.block permArgs) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = scr σ ∧ s'.gpr .rsi = at' σ 800 ∧
      s'.gpr .rdx = at' σ 1600 ∧ s'.gpr .rcx = at' σ 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold permArgs
  xrun [he.rbx, sx800, sx1600, sx2368]

/-- The permutation's precondition, in the scratch space. -/
theorem pre4 {σ : State} (hp : Pre σ) {s : State} (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    (hrc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) :
    Pre4 s (scr σ) (at' σ 800) (at' σ 1600) :=
  ⟨fun i _ => in_scr hp hwr (a := 32 * i) (by omega),
    fun i _ => by rw [at', Offset.add_add]; exact in_scr hp hwr (by omega),
    fun r _ => by rw [at', Offset.add_add]; exact in_scr' hp hrd hwr (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    fun r hr k hk => by rw [la_tbl]; exact hrc r hr k hk⟩

/-- A buffer byte, read through a frame of the states. -/
theorem buf_frame {σ : State} {m m' : Mem} {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' σ oBuf, 2016⟩ r) (hf : Frame rs m m') {k p : Nat} (hk : k < 4)
    (hp' : p < 504) : m' (at' σ (oBuf + 504 * k + p)) = m (at' σ (oBuf + 504 * k + p)) := by
  have := hf.bytes (R := ⟨at' σ oBuf, 2016⟩) hd (by simp only; omega) (i := 504 * k + p) (by simp only; omega)
  simpa only [at', Offset.add_add, Nat.add_assoc] using this

/-- The permutation, after `n` squeezes. -/
theorem perm_ok {σ : State} (hp : Pre σ) {n : Nat} (hn : n < 3) {s : State} (h : SqInv σ n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', Env σ s' ∧ s'.gpr .r14 = 1 ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (scr σ) (fun k => iterF (n + 1) (A0 (B σ k))) ∧
      (∀ k < 4, ∀ p < 168 * n, s'.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p) → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq Impl.Sha3.X86_64.X4.permute4 rest)) s Q := by
  refine WP.seq (WP.mono (args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (A := fun k => iterF n (A0 (B σ k))) (pre4 hp hrd hwr (by rw [hm]; exact h.rc))
    hdi hsi hdx (by rw [hcx, at', at', Offset.add_add]) (by rw [hm]; exact h.lanes))
    fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2016) (by simp only [oBuf]; omega)
        (by simp only [oBuf]; omega), Offset.disjoint (scr σ) (d := oBuf) (n := 2016) (e := 800) (k := 800)
          (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf hk (by omega), hm]
    exact h.buf k hk p hp'


/-! ## Copying the output -/

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXI (σ : State) (n K I : Nat) (s : State) : Prop where
  env : Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (fun k => iterF (n + 1) (A0 (B σ k)))
  buf : ∀ k < 4, ∀ p < 504, (p < 168 * n ∨ (168 * n ≤ p ∧ p < 168 * n + 168 ∧ (k < K ∨ (k = K ∧ p < 168 * n + 8 * I)))) →
    s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem ext_step {σ : State} (hp : Pre σ) {n K I : Nat} (hn : n < 3) (hK : K < 4) (hI : I < 21) {s : State}
    (h : EXI σ n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbx (oBuf + 504 * K + 168 * n + 8 * I)) .rax]) s (EXI σ n K (I + 1)) := by
  refine wp_movm (a := at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hf : Frame [⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨Env.low h.env (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by simp only [oBuf, oSave]; omega)) hf (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_⟩
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hk (by omega), ← xofByte_A0 (B_length σ k) (by omega),
        show 168 * n + (8 * I + (p - 168 * n - 8 * I)) = p by omega]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

theorem extract_eq (n : Nat) : extract n = (List.range 4).flatMap fun K => (List.range 21).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))), .store (at_ .rbx (oBuf + 504 * K + 168 * n + 8 * I)) .rax] := rfl

/-- Block `n` of each state's output. -/
theorem extract_ok {σ : State} (hp : Pre σ) {n : Nat} (hn : n < 3) {s : State} (h : EXI σ n 0 0 s) :
    WP isa (.block (extract n)) s (SqInv σ (n + 1)) := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXI σ n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => EXI σ n K I s) (fun I s hI h => ext_step hp hn hK hI h)
    21 (Nat.le_refl _) s h) fun s' h' => ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega)⟩

/-- `squeeze4 n`: after `n + 1` squeezes. -/
theorem sq_ok {σ : State} (hp : Pre σ) {n : Nat} (hn : n < 3) {s : State} (h : SqInv σ n s) :
    WP isa (squeeze4 n) s (SqInv σ (n + 1)) := by
  unfold squeeze4
  exact perm_ok hp hn h fun s' ⟨he, h14, hrc, hl, hb⟩ =>
    extract_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega)⟩

end VG.Proof.MlKem.X86_64.S4
