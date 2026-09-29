import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM-768 on x86-64: byte stores, copies, and the calls of `SampleNTT`

Untrusted: everything here is checked by Lean. In a layout: a byte store
(`setB_okL`), a copy (`copy_okL`), and the entry `Â[i, j]` of the matrix,
`SampleNTT(ρ ‖ j ‖ i)` with `ρ` at `SB` (`sampleIJ_ok`, `sampleIJ_tr`),
which changes `r15` (so what it leaves is `PostB`, not `Post`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem rbx_cs : Reg.rbx ∈ calleeSaved := by decide
theorem rbx_na : Reg.rbx ∉ argRegs := by decide
theorem rbx_bases : Reg.rbx ∈ bases := by decide

/-! ## Composing what pieces leave -/

theorem PostB.refl (s : State) (W : List Region) : PostB s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PPostB.app {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPostB s s₁ ws₁) (h₂ : PPostB s₁ s₂ ws₂)
    (hb : ∀ w ∈ ws₂, w.1.1 ∈ bases) : PPostB s s₂ (ws₁ ++ ws₂) := by
  have e : ws₂.map (toR s₁) = ws₂.map (toR s) := List.map_congr_left fun w hw => by simp only [toR, h₁.pa (hb w hw)]
  have f₂ := h₂.frame
  rw [e, h₁.rsp] at f₂
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr), h₂.rsp.trans h₁.rsp,
    (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (by rw [List.map_append]; exact List.mem_append_left _ hr)
    · exact List.mem_append_right _ hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (by rw [List.map_append]; exact List.mem_append_right _ hr)
    · exact List.mem_append_right _ hr

theorem PPost.app {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPost s s₁ ws₁) (h₂ : PPost s₁ s₂ ws₂)
    (hcs : ∀ w ∈ ws₂, w.1.1 ∈ calleeSaved) : PPost s s₂ (ws₁ ++ ws₂) :=
  PPost.trans h₁ h₂ hcs (fun _ hw => List.mem_append_left _ hw) (fun _ hw => List.mem_append_right _ hw)

/-! ## A byte -/

section
variable {rbs wbs : List (Reg × Nat)}

theorem bytesAt_one (m : Mem) (a : Addr) : bytesAt m a 1 = [m a] := by
  simp [bytesAt]

theorem setB_okL {s : State} (L : Lay rbs wbs s) {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 256)
    (hc : inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => PPost s s' [(p, 1)] ∧ bytesAt s'.mem (pa s p) 1 = [BitVec.ofNat 8 v] := by
  have hw : InRegions s.wr (pa s p) 1 := L.cW hc _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (setB_ok p v hr hv s hw) fun s' ⟨hm, k⟩ => ⟨post_of_keep k (by decide) ?_, ?_⟩
  · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [hm, bytesAt_one, writeW8_apply, ifp rfl]

/-! ## A copy -/

def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  wrOk bs wbs dst n && rdOk bs src n && sepB bs src n dst n && decide (0 < n) && decide (n < 2 ^ 31)

theorem copy_okL {s : State} (L : Lay rbs wbs s) {dst src : Ptr} {n : Nat} (hsr : src.1 ≠ .rdi)
    (hc : copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => PPost s s' [(dst, n)] ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  simp only [copyChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hod, hid⟩, hwd⟩, hos, his⟩, hs⟩, hn0⟩, hn⟩ := hc
  have hrd : InRegions (s.rd ++ s.wr) (pa s src) n := L.cR his _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hwr : InRegions s.wr (pa s dst) n := L.cW hwd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  exact WP.mono (copy_ok dst src n hn0 hn hod hos hsr s hrd hwr (L.disj hs))
    fun s' ⟨hb, hf, k⟩ => ⟨post_of_keep k (by decide) hf, hb⟩

end

/-! ## The seed of `SampleNTT` -/

theorem seed_eq {m : Mem} {p : Addr} {ρ : List Byte} (hρ : bytesAt m p 32 = ρ) {j i : Byte}
    (hj : bytesAt m (p + BitVec.ofNat 64 32) 1 = [j]) (hi : bytesAt m (p + BitVec.ofNat 64 33) 1 = [i]) :
    bytesAt m p 34 = ρ ++ [j, i] := by
  rw [show (34 : Nat) = 32 + (1 + 1) from rfl, bytesAt_add, bytesAt_add, off_add, hρ, hj, hi]
  rfl

/-- What `SampleNTT` leaves, as `PostB`. -/
theorem SampPost.b {a : Ptr} {s s' : State} (h : SampPost a s s') :
    PPostB s s' [(a, 1024), (sc oSS, 2048)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The checks of `Â[i, j]`: its call, and the two bytes of the seed. -/
def ijChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  sampChk bs wbs a && inB wbs (sc (oSB + 32)) 1 && inB wbs (sc (oSB + 33)) 1 &&
    keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 && keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 &&
    keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1

theorem ijChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : ijChk bs wbs a = true) :
    sampChk bs wbs a = true ∧ inB wbs (sc (oSB + 32)) 1 = true ∧ inB wbs (sc (oSB + 33)) 1 = true ∧
      keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 = true ∧ keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 = true ∧
      keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1 = true := by
  simp only [ijChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The two indices of the seed `ρ ‖ j ‖ i`. -/
theorem setIJ_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat} (hi : i < 256) (hj : j < 256) {a : Ptr}
    (hc : ijChk (rbs ++ wbs) wbs a = true) :
    WP isa (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) s fun s' =>
      PPost s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt s'.mem (pa s' (sc oSB)) 34 = matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j := by
  obtain ⟨_, h32, h33, k1, k2, k3⟩ := ijChk_spec hc
  rw [WP.block_append_iff]
  refine WP.mono (setB_okL L (by decide) hj h32) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (setB_okL L₁ (by decide) hi h33) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have e1 : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun o => hP₁.pa rbx_cs
  have e2 : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have hρ : bytesAt s₂.mem (pa s₂ (sc oSB)) 32 = bytesAt s.mem (pa s (sc oSB)) 32 := by
    rw [L₁.keepBytes hP₂.b k2, L.keepBytes hP₁.b k1]
  have hjb : bytesAt s₂.mem (pa s₂ (sc (oSB + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₁.keepBytes hP₂.b k3, e1]; exact hb₁
  have hib : bytesAt s₂.mem (pa s₂ (sc (oSB + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e2]; exact hb₂
  refine ⟨PPost.app hP₁ hP₂ (by decide), seed_eq hρ ?_ ?_⟩
  · rw [← hjb, pa, pa, off_add]
  · rw [← hib, pa, pa, off_add]

theorem sampleIJ_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat} (hi : i < 256) (hj : j < 256)
    (hc : ijChk (rbs ++ wbs) wbs (aS i j) = true) :
    WP isa (sampleIJ i j) s fun s' =>
      PPostB s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(aS i j, 1024), (sc oSS, 2048)]) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j)).isSome then 1 else 0)) ∧
      ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j) = some f →
        PolyIs s'.mem (pa s (aS i j)) f := by
  unfold sampleIJ
  rw [WP.seq_iff]
  refine WP.mono (setIJ_ok L hcs hi hj hc) fun s₂ ⟨hP₂, hseed⟩ => ?_
  have L₂ := L.post hP₂.b hcs
  refine WP.mono (sampleAt_ok rbx_na (SampH.of L₂ (ijChk_spec hc).1)) fun s₃ h => ?_
  have e3 : pa s₂ (aS i j) = pa s (aS i j) := hP₂.pa rbx_cs
  refine ⟨PPostB.app hP₂.b h.b (by simp [bases]), ?_, fun f hf => ?_⟩
  · rw [h.r15, hseed, hP₂.cs .r15 (by decide)]
  · rw [← e3]; exact h.res f (by rw [hseed]; exact hf)

theorem sampleIJ_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat}
    (hi : i < 256) (hj : j < 256) (hc : ijChk (rbs ++ wbs) wbs (aS i j) = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i))
      (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 32 = bytesAt y.mem (pa y (sc oSB)) 32)
      (sampleIJ i j) fun _ _ => True := by
  have hin : inB (rbs ++ wbs) (sc oSB) 34 = true := (sampChk_in (ijChk_spec hc).1).1
  unfold sampleIJ
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.eq hin) ht)
    (F := fun x x' => PPost x x' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt x'.mem (pa x' (sc oSB)) 34 = matSeed (bytesAt x.mem (pa x (sc oSB)) 32) i j)
    (fun x y h => ⟨setIJ_ok h.1.1 hcs hi hj hc, setIJ_ok h.1.2.1 hcs hi hj hc⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, by rw [hx.2, hy.2, h.2]⟩)
    (sampleAt_trL rbx_na (ijChk_spec hc).1)

end VG.Proof.MlKem.X86_64
