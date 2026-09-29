import VerifiedGarbage.Proof.MlKem.Arm.Prf

/-!
# ML-KEM-768 on 32-bit ARM: a row of `Â ∘ v̂`

Untrusted: everything here is checked by Lean. `rowSum transpose` sums, in
polynomial 11, the products of the entries `j < 3` of row `i` (in `r9`) of
`Â` (or of `Â^⊺`, `transpose`) with polynomials `3 + j`, sampling each
entry into polynomial 13 from the seed `ρ ‖ j ‖ i` (`ρ ‖ i ‖ j`) at 1216. If a
`SampleNTT` does not finish, the product uses polynomial `3 + j` in its
place (`effA`), and the flag in `r11` becomes 0 (`rowSum_ok`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The algorithm -/

/-- The seed of entry `j` of row `i`: that of `Â[i, j]`, or of `Â[j, i]`. -/
def rowSeed (transpose : Bool) (ρ : List Byte) (i j : Nat) : List Byte :=
  if transpose then VG.Proof.MlKem.matSeed ρ j i else VG.Proof.MlKem.matSeed ρ i j

/-- The entry the product uses: the sampled one, or `v` if `SampleNTT` does not finish. -/
def effA (transpose : Bool) (ρ : List Byte) (i j : Nat) (v : Poly) : Poly :=
  (sampleNTT 280 (rowSeed transpose ρ i j)).getD v

/-- The sum of the first `j` products. -/
def rowAcc (a v : Nat → Poly) : Nat → Poly
  | 0 => zero
  | j + 1 => add (rowAcc a v j) (multiplyNTTs (a j) (v j))

/-- Whether the first `j` entries' `SampleNTT`s finished. -/
def okRow (transpose : Bool) (ρ : List Byte) (i j : Nat) : Bool :=
  (List.range j).all fun j' => (sampleNTT 280 (rowSeed transpose ρ i j')).isSome

theorem okRow_succ (transpose : Bool) (ρ : List Byte) (i j : Nat) :
    okRow transpose ρ i (j + 1) = (okRow transpose ρ i j && (sampleNTT 280 (rowSeed transpose ρ i j)).isSome) := by
  simp only [okRow, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem rowAcc_three (a v : Nat → Poly) : rowAcc a v 3 = VG.Proof.MlKem.dot3 a v := by
  simp only [rowAcc, VG.Proof.MlKem.zero_add_poly, VG.Proof.MlKem.dot3]

/-! ## The blocks -/

section
variable {s : State} {P : BitVec 32} {i j : Nat}

theorem seedArgs_ok (transpose : Bool) (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 i)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 j)
    (w912 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (oSeed + 32))) 1)
    (w913 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (oSeed + 33))) 1) :
    WP isa (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 oAhat, ptrTo .r2 .r7 oSample])) s
      fun s' => (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.mem = (s.mem.writeW (State.addr (P + BitVec.ofNat 32 (oSeed + 32)))
            ((BitVec.ofNat 32 (if transpose then i else j)).setWidth 8)).writeW
          (State.addr (P + BitVec.ofNat 32 (oSeed + 33))) ((BitVec.ofNat 32 (if transpose then j else i)).setWidth 8) ∧
        s'.gpr .r0 = P + BitVec.ofNat 32 oSeed ∧ s'.gpr .r1 = P + BitVec.ofNat 32 oAhat ∧
        s'.gpr .r2 = P + BitVec.ofNat 32 oSample := by
  have e1 : encodable (BitVec.ofNat 32 oSeed) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 oAhat) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oSample) = true := by decide
  have o1 : oSeed + 32 < 4096 := by decide
  have o2 : oSeed + 33 < 4096 := by decide
  cases transpose <;>
  · run_block [seedBytes, ptrTo, e1, e2, e3, o1, o2, h7, h9, h10, w912, w913]
    refine ⟨fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, m2, -, -⟩ := pres_ne hr hl
    simp only [m0, m1, m2, ite_false]

theorem flag_ok {b c : Bool} (h0 : s.gpr .r0 = if c then 1 else 0) (h11 : s.gpr .r11 = if b then 1 else 0) :
    WP isa (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) s fun s' =>
      KeptX [.r11] [] s s' ∧ s'.gpr .r11 = (if b && c then 1 else 0) ∧ s'.z = !c ∧ s'.mem = s.mem := by
  have e0 : encodable (0 : BitVec 32) = true := by decide
  run_block [e0, h0, h11]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, ?_, ?_⟩
  · show (if r = .r11 then _ else s.gpr r) = s.gpr r
    exact ite_eq_right (fun e : r = .r11 => hx (by rw [e]; exact List.mem_singleton_self _))
  · cases b <;> cases c <;> rfl
  · cases c <;> exact ⟨rfl, trivial⟩

theorem selT_ok (h7 : s.gpr .r7 = P) (h10 : s.gpr .r10 = BitVec.ofNat 32 j) :
    WP isa (.block (slotAt .r1 .r10 (oPoly 3))) s fun s' =>
      Only s s' ∧ s'.gpr .r1 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly 3) := by
  have e1 : encodable (BitVec.ofNat 32 (oPoly 3)) = true := by decide
  run_block [slotAt, ptrTo, e1, h7, h10]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨-, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m1, ite_false]

theorem selF_ok (h7 : s.gpr .r7 = P) :
    WP isa (.block [ptrTo .r1 .r7 oAhat]) s fun s' => Only s s' ∧ s'.gpr .r1 = P + BitVec.ofNat 32 oAhat := by
  have e1 : encodable (BitVec.ofNat 32 oAhat) = true := by decide
  run_block [ptrTo, e1, h7]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨-, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m1, ite_false]

theorem mulArgs_ok (h7 : s.gpr .r7 = P) (h10 : s.gpr .r10 = BitVec.ofNat 32 j) :
    WP isa (.block (ptrTo .r0 .r7 oTmp :: slotAt .r2 .r10 (oPoly 3) ++ [ptrTo .r3 .r7 oNtt])) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 oTmp ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .r2 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly 3) ∧
      s'.gpr .r3 = P + BitVec.ofNat 32 oNtt := by
  have e1 : encodable (BitVec.ofNat 32 oTmp) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 (oPoly 3)) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oNtt) = true := by decide
  run_block [slotAt, ptrTo, e1, e2, e3, h7, h10]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, -, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m2, m3, ite_false]

theorem accArgs_ok {o o' : Nat} (h7 : s.gpr .r7 = P) (he : encodable (BitVec.ofNat 32 o) = true)
    (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block [ptrTo .r0 .r7 o, ptrTo .r1 .r7 o']) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 o ∧ s'.gpr .r1 = P + BitVec.ofNat 32 o' := by
  run_block [ptrTo, he, he', h7]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

end

/-! ## The loop -/

/-- What a row needs of the state it starts from. -/
structure RowPre (L : Lay) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool) (s : State) : Prop where
  ctx : Ctx L s
  i3 : i < 3
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if fl then 1 else 0
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρ
  vec : ∀ j < 3, PolyIs s.mem (L.A 0 (oPoly (3 + j))) (v j)

/-- What a row changes: the indices of the seed, polynomials 11 to 13, the
working space of the callees and the stack. -/
abbrev rowW : List (Nat × Nat × Nat) := [(0, 1248, 2), (0, oAcc, 3072), (0, oSample, 3072), (1, 0, 8)]

/-- After the first `j` entries of the row. -/
structure RowInv (L : Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool) (s₀ : State)
    (j : Nat) (s : State) : Prop where
  kx : KeptX [.r10, .r11] (L.RL rowW) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i j then 1 else 0
  acc : PolyIs s.mem (L.A 0 oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v j)

theorem rowW_vec : ∀ j < 3, rowW.all (sep0 (oPoly (3 + j)) 1024) = true := by decide

theorem bytes_two (m : Mem) (p : Addr) : bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := by
  simp only [bytesAt, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, add_ofNat_zero]

theorem rowSeed_eq (transpose : Bool) (ρ : List Byte) (i j : Nat) :
    rowSeed transpose ρ i j = ρ ++ [BitVec.ofNat 8 (if transpose then i else j), BitVec.ofNat 8 (if transpose then j else i)] := by
  cases transpose <;> rfl

/-! ### The steps of an iteration -/

/-- Whether entry `j`'s `SampleNTT` finishes. -/
abbrev cOk (transpose : Bool) (ρ : List Byte) (i j : Nat) : Bool := (sampleNTT 280 (rowSeed transpose ρ i j)).isSome

/-- Where the product takes the entry from. -/
abbrev oSel (c : Bool) (j : Nat) : Nat := if c then oAhat else oPoly (3 + j)

section
variable (L : Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool) (s₀ : State) (j : Nat)

/-- What holds through an iteration: what it changed, the counter, the sum so far. -/
structure RS (s : State) : Prop where
  kx : KeptX [.r10, .r11] (L.RL rowW) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  acc : PolyIs s.mem (L.A 0 oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v j)

/-- After the seed and the arguments of `SampleNTT`. -/
structure RA (s : State) : Prop where
  rs : RS L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i j then 1 else 0
  r0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oSeed
  r1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oAhat
  r2 : s.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 oSample
  seed : bytesAt s.mem (L.A 0 oSeed) 34 = rowSeed transpose ρ i j

/-- After `SampleNTT`. -/
structure RB (s : State) : Prop where
  rs : RS L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i j then 1 else 0
  r0 : s.gpr .r0 = if cOk transpose ρ i j then 1 else 0
  ahat : ∀ a, sampleNTT 280 (rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 oAhat) a

/-- After the flag. -/
structure RC (s : State) : Prop where
  rs : RS L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  z : s.z = !cOk transpose ρ i j
  ahat : ∀ a, sampleNTT 280 (rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 oAhat) a

/-- After the selection of the entry. -/
structure RD (s : State) : Prop where
  rs : RS L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  r1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oSel (cOk transpose ρ i j) j)
  sel : PolyIs s.mem (L.A 0 (oSel (cOk transpose ρ i j) j)) (effA transpose ρ i j (v j))

/-- After the arguments of the product. -/
structure RE (s : State) : Prop where
  rd : RD L transpose ρ v i fl s₀ j s
  r0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oTmp
  r2 : s.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 + j))
  r3 : s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 oNtt

/-- After the product. -/
structure RF (s : State) : Prop where
  rs : RS L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  tmp : PolyIs s.mem (L.A 0 oTmp) (multiplyNTTs (effA transpose ρ i j (v j)) (v j))

/-- After the arguments of the sum. -/
structure RG (s : State) : Prop where
  rf : RF L transpose ρ v i fl s₀ j s
  r0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc
  r1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oTmp

/-- After the sum. -/
structure RH (s : State) : Prop where
  kx : KeptX [.r10, .r11] (L.RL rowW) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  acc : PolyIs s.mem (L.A 0 oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v (j + 1))

end

section
variable {L : Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → Poly} {i : Nat} {fl : Bool} {s₀ : State}
  {j : Nat}

theorem RS.ctx (hp : RowPre L ρ v i fl s₀) {s : State} (h : RS L transpose ρ v i s₀ j s) : Ctx L s :=
  h.kx.ctx (by decide) hp.ctx

theorem RS.r9 (hp : RowPre L ρ v i fl s₀) {s : State} (h : RS L transpose ρ v i s₀ j s) :
    s.gpr .r9 = BitVec.ofNat 32 i := by
  rw [h.kx.cs .r9 (by decide) (by decide) (by decide), hp.r9]

theorem RS.vec (hp : RowPre L ρ v i fl s₀) (hj : j < 3) {s : State} (h : RS L transpose ρ v i s₀ j s) :
    PolyIs s.mem (L.A 0 (oPoly (3 + j))) (v j) :=
  Lay.polyIs_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by offs) (rowW_vec j hj)) (hp.vec j hj)

/-- A step that keeps `RS`: it changes only the regions of `rowW` and not `r10`, nor the sum. -/
theorem RS.step (hp : RowPre L ρ v i fl s₀) {s s' : State} (h : RS L transpose ρ v i s₀ j s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.r10, .r11])
    (h10 : Reg.r10 ∉ xs) (hW : W.all (fun w => rowW.any (subB0 w)) = true)
    (hA : sepAll L.sizes (0, oAcc, 1024) W = true) : RS L transpose ρ v i s₀ j s' :=
  ⟨h.kx.trans ((hk.weaken hx).subL hp.ctx hW), by rw [hk.cs .r10 (by decide) (by decide) h10, h.r10],
    Lay.polyIs_keep hp.ctx.ok hk.frame hA h.acc⟩

theorem rowA_ok (hp : RowPre L ρ v i fl s₀) (hj : j < 3) {s : State} (h : RowInv L transpose ρ v i fl s₀ j s) :
    WP isa (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 oAhat, ptrTo .r2 .r7 oSample])) s
      (RA L transpose ρ v i fl s₀ j) := by
  have hL := hp.ctx.ok
  have hi := hp.i3
  have hc := h.kx.ctx (by decide) hp.ctx
  have g9 : s.gpr .r9 = BitVec.ofNat 32 i := by rw [h.kx.cs .r9 (by decide) (by decide) (by decide), hp.r9]
  have ρs : bytesAt s.mem (L.A 0 oSeed) 32 = ρ := by
    rw [← hp.rho]; exact Lay.bytes_keep hL h.kx.frame (hp.ctx.sepAll0 (by decide) (by decide)) (by decide)
  have e912 := hc.addr (o := oSeed + 32) (by decide)
  have e913 := hc.addr (o := oSeed + 33) (by decide)
  have w912 : InRegions s.wr (State.addr (L.ptr 0 + BitVec.ofNat 32 (oSeed + 32))) 1 := by
    rw [e912]; exact hc.cs (o := 1248) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have w913 : InRegions s.wr (State.addr (L.ptr 0 + BitVec.ofNat 32 (oSeed + 33))) 1 := by
    rw [e913]; exact hc.cs (o := 1249) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (seedArgs_ok transpose hc.r7 g9 h.r10 w912 w913)
    fun s₁ ⟨cs₁, rd₁, wr₁, sp₁, m₁, g0, g1, g2⟩ => ?_
  have m₁' : s₁.mem = (s.mem.writeW (L.A 0 1248) (BitVec.ofNat 8 (if transpose then i else j))).writeW (L.A 0 1249)
      (BitVec.ofNat 8 (if transpose then j else i)) := by
    rw [m₁, e912, e913, setWidth8_ofNat (by split <;> omega), setWidth8_ofNat (by split <;> omega)]
  have k₁ : KeptX [] (L.RL [(0, 1248, 2)]) s s₁ := by
    refine ⟨fun r hr hl _ => cs₁ r hr hl, sp₁, rd₁, wr₁, ?_⟩
    rw [m₁']
    have c1 : (L.R 0 1248 2).Contains (L.A 0 1248) 1 := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have c2 : (L.R 0 1248 2).Contains (L.A 0 1249) 1 := by
      have := contains_off (base := State.addr (L.ptr 0) + BitVec.ofNat 64 1248) (len := 2) (off := 1) (n := 1)
        (by omega) (by omega)
      rwa [add_ofNat_add] at this
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2
  have ne : (L.A 0 1248 : Addr) ≠ L.A 0 1249 := by
    intro e; have := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp e); simp at this
  have b912 : s₁.mem (L.A 0 1248) = BitVec.ofNat 8 (if transpose then i else j) := by
    rw [m₁', writeW8_apply, writeW8_apply, ite_eq_right ne, ite_eq_left rfl]
  have b913 : s₁.mem (L.A 0 1249) = BitVec.ofNat 8 (if transpose then j else i) := by
    rw [m₁', writeW8_apply, ite_eq_left rfl]
  refine ⟨⟨h.kx.trans ((k₁.weaken (by simp)).subL hp.ctx (by decide)),
    by rw [k₁.cs .r10 (by decide) (by decide) (by decide), h.r10],
    Lay.polyIs_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) h.acc⟩,
    by rw [k₁.cs .r11 (by decide) (by decide) (by decide), h.r11], g0, g1, g2, ?_⟩
  rw [rowSeed_eq]
  show bytesAt s₁.mem (State.addr (L.ptr 0) + BitVec.ofNat 64 1216) (32 + 2) = _
  rw [bytesAt_add, bytes_two, add_ofNat_add, add_ofNat_add]
  congr 1
  · rw [← ρs]
    exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) (by decide)
  · exact congrArg₂ (fun a b => [a, b]) b912 b913

theorem rowB_ok (hp : RowPre L ρ v i fl s₀) {s : State} (h : RA L transpose ρ v i fl s₀ j s) :
    WP isa callSample s (RB L transpose ρ v i fl s₀ j) := by
  have hc := h.rs.ctx hp
  refine sampleL hc h.r0 h.r1 h.r2 (hc.sep00 (by decide) (by decide) (by decide))
    (hc.sep00 (by decide) (by decide) (by decide)) (hc.sep00 (by decide) (by decide) (by decide))
    (hc.sep01 (by decide) (by decide)) (hc.sep01 (by decide) (by decide)) (hc.sep01 (by decide) (by decide))
    (mem_rd_wr hc.buf0) hc.buf0 hc.buf0 fun s' k' r0' a' => ?_
  rw [h.seed] at r0' a'
  exact ⟨h.rs.step hp (k'.x []) (by simp) (by simp) (by decide) (hc.sepAll0 (by decide) (by decide)),
    by rw [k'.cs .r11 (by decide) (by decide), h.r11], r0', a'⟩

theorem rowC_ok {s : State} (h : RB L transpose ρ v i fl s₀ j s) :
    WP isa (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) s (RC L transpose ρ v i fl s₀ j) :=
  WP.mono (flag_ok h.r0 h.r11) fun s' ⟨k', f', z', m'⟩ =>
    ⟨⟨h.rs.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)),
      by rw [k'.cs .r10 (by decide) (by decide) (by decide), h.rs.r10], by rw [m']; exact h.rs.acc⟩,
      by rw [f', Bool.and_assoc, ← okRow_succ], z', by rw [m']; exact h.ahat⟩

theorem rowD_ok (hp : RowPre L ρ v i fl s₀) (hj : j < 3) {s : State} (h : RC L transpose ρ v i fl s₀ j s) :
    WP isa (.ite .eq (.block (slotAt .r1 .r10 (oPoly 3))) (.block [ptrTo .r1 .r7 oAhat])) s
      (RD L transpose ρ v i fl s₀ j) := by
  have hc := h.rs.ctx hp
  have eo : oPoly (3 + j) = oPoly 3 + 1024 * j := by simp only [oPoly]; omega
  refine WP.ite s.z rfl (fun hz => WP.mono (selT_ok hc.r7 h.rs.r10) fun s₄ ⟨o₄, g1₄⟩ => ?_)
    (fun hz => WP.mono (selF_ok hc.r7) fun s₄ ⟨o₄, g1₄⟩ => ?_)
  · rw [h.z] at hz
    have hc' : cOk transpose ρ i j = false := by simpa using hz
    rw [slot_eq _ (by offs), ← eo] at g1₄
    have e : effA transpose ρ i j (v j) = v j := by
      simp only [effA]
      simp only [cOk] at hc'
      cases e' : sampleNTT 280 (rowSeed transpose ρ i j)
      · rfl
      · rw [e'] at hc'; cases hc'
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .r11 (by decide) (by decide), h.r11], by rw [g1₄, hc']; rfl, ?_⟩
    rw [hc', e, o₄.mem]; exact h.rs.vec hp hj
  · rw [h.z] at hz
    have hc' : cOk transpose ρ i j = true := by simpa using hz
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .r11 (by decide) (by decide), h.r11], by rw [g1₄, hc']; rfl, ?_⟩
    simp only [cOk] at hc'
    cases e' : sampleNTT 280 (rowSeed transpose ρ i j) with
    | none => rw [e'] at hc'; cases hc'
    | some a =>
      have e : effA transpose ρ i j (v j) = a := by simp only [effA, e', Option.getD_some]
      rw [e, o₄.mem, show oSel (cOk transpose ρ i j) j = oAhat by simp [cOk, e']]
      exact h.ahat a e'

theorem rowE_ok (hp : RowPre L ρ v i fl s₀) (hj : j < 3) {s : State} (h : RD L transpose ρ v i fl s₀ j s) :
    WP isa (.block (ptrTo .r0 .r7 oTmp :: slotAt .r2 .r10 (oPoly 3) ++ [ptrTo .r3 .r7 oNtt])) s
      (RE L transpose ρ v i fl s₀ j) := by
  have hc := h.rs.ctx hp
  have eo : oPoly (3 + j) = oPoly 3 + 1024 * j := by simp only [oPoly]; omega
  refine WP.mono (mulArgs_ok (j := j) hc.r7 h.rs.r10) fun s' ⟨o', m0, m1, m2, m3⟩ => ?_
  rw [slot_eq _ (by offs), ← eo] at m2
  exact ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
    by rw [o'.cs .r11 (by decide) (by decide), h.r11], by rw [m1, h.r1], by rw [o'.mem]; exact h.sel⟩, m0, m2, m3⟩

theorem sel_sep (c : Bool) {j : Nat} (hj : j < 3) :
    oSel c j + 1024 ≤ 32768 ∧ (oTmp + 1024 ≤ oSel c j ∨ oSel c j + 1024 ≤ oTmp) ∧
      (oSel c j + 1024 ≤ oNtt ∨ oNtt + 1024 ≤ oSel c j) := by
  cases c <;> simp only [oSel, Bool.false_eq_true, ite_false, ite_true] <;> offs

theorem rowF_ok (hp : RowPre L ρ v i fl s₀) (hj : j < 3) {s : State} (h : RE L transpose ρ v i fl s₀ j s) :
    WP isa callMul s (RF L transpose ρ v i fl s₀ j) := by
  have hc := h.rd.rs.ctx hp
  obtain ⟨s1, s2, s3⟩ := sel_sep (cOk transpose ρ i j) hj
  refine mulL hc.ok h.r0 h.rd.r1 h.r2 h.r3 (hc.sep00 (by offs) s1 s2) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 s1 (by offs) s3) (hc.sep00 (by offs) (by offs) (by offs))
    hc.buf0 (mem_rd_wr hc.buf0) (mem_rd_wr hc.buf0) hc.buf0 h.rd.sel (h.rd.rs.vec hp hj) fun s' k' p' => ?_
  exact ⟨h.rd.rs.step hp (k'.x []) (by simp) (by simp) (by decide) (hc.sepAll0 (by decide) (by decide)),
    by rw [k'.cs .r11 (by decide) (by decide), h.rd.r11], p'⟩

theorem rowG_ok (hp : RowPre L ρ v i fl s₀) {s : State} (h : RF L transpose ρ v i fl s₀ j s) :
    WP isa (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 oTmp]) s (RG L transpose ρ v i fl s₀ j) := by
  have hc := h.rs.ctx hp
  exact WP.mono (accArgs_ok hc.r7 (by decide) (by decide)) fun s' ⟨o', a0, a1⟩ =>
    ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o'.cs .r11 (by decide) (by decide), h.r11], by rw [o'.mem]; exact h.tmp⟩, a0, a1⟩

theorem rowH_ok (hp : RowPre L ρ v i fl s₀) {s : State} (h : RG L transpose ρ v i fl s₀ j s) :
    WP isa callAdd s (RH L transpose ρ v i fl s₀ j) := by
  have hc := h.rf.rs.ctx hp
  refine addL hc.ok h.r0 h.r1 (hc.sep00 (by decide) (by decide) (by decide)) hc.buf0 (mem_rd_wr hc.buf0)
    h.rf.rs.acc h.rf.tmp fun s' k' p' => ?_
  exact ⟨h.rf.rs.kx.trans ((k'.x _).subL hp.ctx (by decide)),
    by rw [k'.cs .r10 (by decide) (by decide), h.rf.rs.r10], by rw [k'.cs .r11 (by decide) (by decide), h.rf.r11],
    p'⟩

theorem rowI_ok {s : State} (hj : j < 3) (h : RH L transpose ρ v i fl s₀ j s) :
    WP isa (.block (count .r10 3)) s fun s' =>
      RowInv L transpose ρ v i fl s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = 3) :=
  WP.mono (count_ok (by omega) (by decide) (by decide) h.r10) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨h.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)), g',
      by rw [k'.cs .r11 (by decide) (by decide) (by decide), h.r11],
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) h.acc⟩, z'⟩

theorem rowBody_ok (hp : RowPre L ρ v i fl s₀) (hj : j < 3) {s : State} (h : RowInv L transpose ρ v i fl s₀ j s) :
    WP isa (rowBody transpose) s fun s' => RowInv L transpose ρ v i fl s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = 3) :=
  WP.seq (WP.mono (rowA_ok hp hj h) fun _ h₁ => WP.seq (WP.mono (rowB_ok hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (rowC_ok h₂) fun _ h₃ => WP.seq (WP.mono (rowD_ok hp hj h₃) fun _ h₄ =>
    WP.seq (WP.mono (rowE_ok hp hj h₄) fun _ h₅ => WP.seq (WP.mono (rowF_ok hp hj h₅) fun _ h₆ =>
    WP.seq (WP.mono (rowG_ok hp h₆) fun _ h₇ => WP.seq (WP.mono (rowH_ok hp h₇) fun _ h₈ =>
      rowI_ok hj h₈))))))))

end

theorem movc_ok {s : State} (c : Reg) {N : Nat} (he : encodable (BitVec.ofNat 32 N) = true) :
    WP isa (.block [.mov c (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 32 N ∧ s'.mem = s.mem := by
  run_block [he]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = c then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = c => hx (by rw [e]; exact List.mem_singleton_self _))

theorem rowSum_ok {L : Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → Poly} {i : Nat} {fl : Bool}
    {s₀ : State} (hp : RowPre L ρ v i fl s₀) :
    WP isa (rowSum transpose) s₀ (RowInv L transpose ρ v i fl s₀ 3) := by
  refine WP.seq (WP.mono (zeroPoly_ok hp.ctx (by decide) (by decide)) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_ne (RowInv L transpose ρ v i fl s₀) (N := 3) (by decide) (fun j hj s h => rowBody_ok hp hj h)
    (fun _ h => h) ⟨?_, g₂, ?_, by rw [m₂]; exact z₁⟩
  · exact ((k₁.x _).subL hp.ctx (by decide)).trans ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · rw [k₂.cs .r11 (by decide) (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), hp.r11]
    simp [okRow]

/-! ## `dot` -/

theorem dotArgs_ok {s : State} {P : BitVec 32} {j : Nat} (h7 : s.gpr .r7 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 j) :
    WP isa (.block (ptrTo .r0 .r7 oTmp :: slotAt .r1 .r10 (oPoly 0) ++ slotAt .r2 .r10 (oPoly 3) ++
      [ptrTo .r3 .r7 oNtt])) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 oTmp ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly 0) ∧
      s'.gpr .r2 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly 3) ∧
      s'.gpr .r3 = P + BitVec.ofNat 32 oNtt := by
  have e1 : encodable (BitVec.ofNat 32 oTmp) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 (oPoly 3)) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oNtt) = true := by decide
  have e4 : encodable (BitVec.ofNat 32 (oPoly 0)) = true := by decide
  run_block [slotAt, ptrTo, e1, e2, e3, e4, h7, h10]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

/-- What `dot` changes: polynomials 11 and 12, and the working space of the callees. -/
abbrev dotW : List (Nat × Nat × Nat) := [(0, oAcc, 2048), (0, oNtt, 1024)]

/-- After the first `j` products. -/
structure DotInv (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r10] (L.RL dotW) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  acc : PolyIs s.mem (L.A 0 oAcc) (rowAcc a v j)

theorem dotW_vec : ∀ j < 6, dotW.all (sep0 (oPoly j) 1024) = true := by decide

theorem dotBody_ok {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < 3, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j)) (hv : ∀ j < 3, PolyIs s₀.mem (L.A 0 (oPoly (3 + j))) (v j))
    {j : Nat} (hj : j < 3) {s : State} (h : DotInv L a v s₀ j s) :
    WP isa dotBody s fun s' => DotInv L a v s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = 3) := by
  have hL := hc₀.ok
  have hc := h.kx.ctx (by decide) hc₀
  have as : PolyIs s.mem (L.A 0 (oPoly j)) (a j) :=
    Lay.polyIs_keep hL h.kx.frame (hc₀.sepAll0 (by offs) (dotW_vec j (by omega))) (ha j hj)
  have vs : PolyIs s.mem (L.A 0 (oPoly (3 + j))) (v j) :=
    Lay.polyIs_keep hL h.kx.frame (hc₀.sepAll0 (by offs) (dotW_vec (3 + j) (by omega))) (hv j hj)
  have eo : oPoly (3 + j) = oPoly 3 + 1024 * j := by simp only [oPoly]; omega
  have eo' : oPoly j = oPoly 0 + 1024 * j := by simp only [oPoly]; try omega
  refine WP.seq (WP.mono (dotArgs_ok hc.r7 h.r10) fun s₁ ⟨o₁, m0, m1, m2, m3⟩ => ?_)
  rw [slot_eq _ (by offs), ← eo'] at m1
  rw [slot_eq _ (by offs), ← eo] at m2
  have hc₁ := hc.only o₁
  refine WP.seq (mulL hL m0 m1 m2 m3 (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) hc₁.buf0 (mem_rd_wr hc₁.buf0) (mem_rd_wr hc₁.buf0) hc₁.buf0
    (by rw [o₁.mem]; exact as) (by rw [o₁.mem]; exact vs) fun s₂ k₂ p₂ => ?_)
  have hc₂ := hc₁.kept k₂
  refine WP.seq (WP.mono (accArgs_ok hc₂.r7 (by decide) (by decide)) fun s₃ ⟨o₃, a0, a1⟩ => ?_)
  have hc₃ := hc₂.only o₃
  have acc₃ : PolyIs s₃.mem (L.A 0 oAcc) (rowAcc a v j) := by
    rw [o₃.mem]
    refine Lay.polyIs_keep hL k₂.frame (hc.sepAll0 (by decide) (by decide)) ?_
    rw [o₁.mem]; exact h.acc
  refine WP.seq (addL hL a0 a1 (hc.sep00 (by decide) (by decide) (by decide)) hc₃.buf0 (mem_rd_wr hc₃.buf0)
    acc₃ (by rw [o₃.mem]; exact p₂) fun s₄ k₄ p₄ => ?_)
  have g10 : s₄.gpr .r10 = BitVec.ofNat 32 j := by
    rw [k₄.cs .r10 (by decide) (by decide), o₃.cs .r10 (by decide) (by decide), k₂.cs .r10 (by decide) (by decide),
      o₁.cs .r10 (by decide) (by decide), h.r10]
  refine WP.mono (count_ok (by omega) (by decide) (by decide) g10) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_⟩, z'⟩
  · exact h.kx.trans ((o₁.x _ _).trans (((k₂.x _).subL hc₀ (by decide)).trans ((o₃.x _ _).trans
      (((k₄.x _).subL hc₀ (by decide)).trans (k'.mono (fun _ h => absurd h List.not_mem_nil))))))
  · exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₄

theorem dot_ok {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < 3, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j)) (hv : ∀ j < 3, PolyIs s₀.mem (L.A 0 (oPoly (3 + j))) (v j)) :
    WP isa dot s₀ fun s => KeptX [.r10] (L.RL dotW) s₀ s ∧ PolyIs s.mem (L.A 0 oAcc) (VG.Proof.MlKem.dot3 a v) := by
  refine WP.seq (WP.mono (zeroPoly_ok hc₀ (by decide) (by decide)) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_ne (DotInv L a v s₀) (N := 3) (by decide) (fun j hj s h => dotBody_ok hc₀ ha hv hj h)
    (fun _ h => ⟨h.kx, by rw [← rowAcc_three]; exact h.acc⟩)
    ⟨((k₁.x _).subL hc₀ (by decide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
      by rw [m₂]; exact z₁⟩

/-! ## Blocks of the top-level functions -/

theorem at384_eq (p : BitVec 32) {i : Nat} (_h : 384 * i < 2 ^ 32) :
    p + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 = p + BitVec.ofNat 32 (384 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem at320_eq (p : BitVec 32) {i : Nat} (_h : 320 * i < 2 ^ 32) :
    p + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 6 = p + BitVec.ofNat 32 (320 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

section
variable {s : State} {P : BitVec 32} {i : Nat}

/-- `r0` at `o` in `scratch`, `r1` at polynomial `i` of the array at `o'`. -/
theorem ptrSlot_ok {o o' : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 i)
    (he : encodable (BitVec.ofNat 32 o) = true) (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block (ptrTo .r0 .r7 o :: slotAt .r1 .r9 o')) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 o ∧ s'.gpr .r1 = P + BitVec.ofNat 32 i <<< 10 + BitVec.ofNat 32 o' := by
  run_block [slotAt, ptrTo, he, he', h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

/-- `r0` at `o` in `scratch`, `r1` at `b + 384 i`. -/
theorem ptr384_ok {o : Nat} {b : Reg} {B : BitVec 32} (hb : b = .r5 ∨ b = .r6) (h7 : s.gpr .r7 = P)
    (hB : s.gpr b = B) (h9 : s.gpr .r9 = BitVec.ofNat 32 i) (he : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block (ptrTo .r0 .r7 o :: at384 .r1 b .r9)) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 o ∧ s'.gpr .r1 = B + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 := by
  rcases hb with rfl | rfl <;>
  · run_block [at384, ptrTo, he, h7, hB, h9]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
    simp only [m0, m1, ite_false]

/-- `r0` at polynomial `i` of the array at `o'`, `r1` at `b + 384 i`. -/
theorem slot384_ok {o' : Nat} {b : Reg} {B : BitVec 32} (hb : b = .r5 ∨ b = .r6) (h7 : s.gpr .r7 = P)
    (hB : s.gpr b = B) (h9 : s.gpr .r9 = BitVec.ofNat 32 i) (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block (slotAt .r0 .r9 o' ++ at384 .r1 b .r9)) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 i <<< 10 + BitVec.ofNat 32 o' ∧
      s'.gpr .r1 = B + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 := by
  rcases hb with rfl | rfl <;>
  · run_block [at384, slotAt, ptrTo, he', h7, hB, h9]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
    simp only [m0, m1, ite_false]

end

/-! ## The end of the top-level functions -/

theorem mem_rd_wr' {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem topEnd_ok {L : Lay} {s₀ s : State} (hc : Ctx L s) (hsav : Saved s.mem (L.A 0 840) s₀.gpr)
    (hlr : s.mem.readW (L.A 0 872) 32 = s₀.gpr .lr) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .r0 = s.gpr .r11 ∧
      s'.mem = s.mem ∧ s'.sp = s.sp := by
  have fs := hc.fit
  rw [topEnd, List.append_assoc, WP.block_append_iff]
  have e7 := hc.r7
  have hk : WP isa (.block [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r11 ∧ s'.gpr .r3 = L.ptr 0 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    run_block [e7]
  refine WP.mono hk fun s₁ ⟨r0, r3, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have e3 : State.addr (s₁.gpr .r3) + BitVec.ofNat 64 840 = L.A 0 840 := by rw [r3]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 840) (by decide)
    (by rw [r3]; exact fit_le (by decide) fs) (g := s₀.gpr) (by rw [e3, m₁]; exact hsav)
    fun i hi => by
      rw [e3, rd₁, wr₁, add_ofNat_add]
      exact mem_rd_wr' (hc.cs (o := 840 + 4 * i) (l := 4) (by omega) _ _ ⟨_, List.mem_singleton_self _,
        Region.contains_self _ _⟩))
    fun s₂ h₂ => ?_
  have g3 : s₂.gpr .r3 = L.ptr 0 := by rw [h₂.other .r3 (by decide), r3]
  have e872 : State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = L.A 0 872 := by
    rw [g3]; exact hc.addr (by decide)
  have i12 : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₂.rd, h₂.wr, rd₁, wr₁]
    exact mem_rd_wr' (hc.cs (o := 872) (l := 4) (by decide) _ _ ⟨_, List.mem_singleton_self _,
      Region.contains_self _ _⟩)
  have ho : oSave + 32 < 4096 := by decide
  have hl : WP isa (.block [.ldr .lr .r3 (oSave + 32)]) s₂ fun s' =>
      s'.gpr .lr = s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 32 ∧
      (∀ r, r ≠ .lr → s'.gpr r = s₂.gpr r) ∧ s'.mem = s₂.mem ∧ s'.sp = s₂.sp := by
    run_block [i12, ho, and_self, and_true]
    exact ⟨trivial, fun r hr => by simp [hr]⟩
  refine WP.mono hl fun s' ⟨lr, rr, m, sp⟩ => ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · by_cases e : r = .lr
    · subst e
      rw [lr, e872, h₂.mem, m₁]; exact hlr
    · have hs : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, savedRegs.getD i .r4 = r := by decide
      obtain ⟨i, hi, rfl⟩ := hs r hr e
      rw [rr _ e]; exact h₂.loaded i hi
  · rw [rr .r0 (by decide), h₂.other .r0 (by decide), r0]
  · rw [m, h₂.mem, m₁]
  · rw [sp, h₂.sp, sp₁]

end VG.Proof.MlKem.Arm
