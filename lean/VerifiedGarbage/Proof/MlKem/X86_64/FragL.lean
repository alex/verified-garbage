import VerifiedGarbage.Proof.MlKem.X86_64.FragHash

/-!
# ML-KEM-768 on x86-64: the calls of the polynomial primitives, in a layout

Untrusted: everything here is checked by Lean. Each call of a primitive
from a state in a layout whose pointers pass its check: what it leaves
(`PPost`) and computes (`nttAt_ok`, …), and that two runs in the layout
leak the same (`nttAt_tr`, …); and the same for the byte stores and copies
between them.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt rates)

section
variable {rbs wbs : List (Reg × Nat)}

theorem rdOk_in {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : rdOk bs p l = true) : inB bs p l = true := by
  simp only [rdOk, Bool.and_eq_true] at h; exact h.2

theorem wrOk_in {bs wbs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : wrOk bs wbs p l = true) : inB bs p l = true := by
  simp only [wrOk, Bool.and_eq_true] at h; exact rdOk_in h.1

/-! ## `NTT` and `NTT⁻¹` -/

theorem ipChk_in {bs wbs : List (Reg × Nat)} {f : Ptr} (hc : ipChk bs wbs f = true) :
    inB bs f 1024 = true ∧ inB bs (sc oSS) 1024 = true := by
  simp only [ipChk, Bool.and_eq_true] at hc; exact ⟨wrOk_in hc.1.1, wrOk_in hc.1.2⟩

theorem nttAt_ok {s : State} (L : Lay rbs wbs s) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    (red : Reduced s.mem (pa s f)) :
    WP isa (nttAt f) s fun s' => PPost s s' [(f, 1024), (sc oSS, 1024)] ∧
      PolyIs s'.mem (pa s f) (ntt (polyAt s.mem (pa s f))) :=
  ipAt_ok ntt_correct ntt_nosp (by rw [ntt_depth]; decide) (IpH.of L hc red)

theorem nttInvAt_ok {s : State} (L : Lay rbs wbs s) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    (red : Reduced s.mem (pa s f)) :
    WP isa (nttInvAt f) s fun s' => PPost s s' [(f, 1024), (sc oSS, 1024)] ∧
      PolyIs s'.mem (pa s f) (nttInv (polyAt s.mem (pa s f))) :=
  ipAt_ok nttInv_correct nttInv_nosp (by rw [nttInv_depth]; decide) (IpH.of L hc red)

theorem nttAt_tr {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (nttAt f)
      fun _ _ => True :=
  RelCT.mono (ipAt_tr ntt_correct ntt_ct) (fun _ _ ⟨h, rx, ry⟩ => ⟨IpH.of h.1 hc rx, IpH.of h.2.1 hc ry,
    h.eq (ipChk_in hc).1, h.eq (ipChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

theorem nttInvAt_tr {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (nttInvAt f)
      fun _ _ => True :=
  RelCT.mono (ipAt_tr nttInv_correct nttInv_ct) (fun _ _ ⟨h, rx, ry⟩ => ⟨IpH.of h.1 hc rx, IpH.of h.2.1 hc ry,
    h.eq (ipChk_in hc).1, h.eq (ipChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

/-! ## Addition and subtraction -/

theorem accChk_in {bs wbs : List (Reg × Nat)} {f g : Ptr} (hc : accChk bs wbs f g = true) :
    inB bs f 1024 = true ∧ inB bs g 1024 = true := by
  simp only [accChk, Bool.and_eq_true] at hc; exact ⟨wrOk_in hc.1.1, rdOk_in hc.1.2⟩

theorem addAt_ok {s : State} (L : Lay rbs wbs s) {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (addAt f g) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (add (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok add_correct add_nosp (by rw [add_depth]; decide) (fun e => hg (by rw [e]; decide)) (AccH.of L hc rf rg)

theorem subAt_ok {s : State} (L : Lay rbs wbs s) {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (subAt f g) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (sub (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok sub_correct sub_nosp (by rw [sub_depth]; decide) (fun e => hg (by rw [e]; decide)) (AccH.of L hc rf rg)

theorem addAt_tr {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (addAt f g) fun _ _ => True :=
  RelCT.mono (accAt_tr add_correct add_ct (fun e => hg (by rw [e]; decide)))
    (fun _ _ ⟨h, ⟨r1, r2⟩, r3, r4⟩ => ⟨AccH.of h.1 hc r1 r2, AccH.of h.2.1 hc r3 r4, h.eq (accChk_in hc).1,
      h.eq (accChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

theorem subAt_tr {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (subAt f g) fun _ _ => True :=
  RelCT.mono (accAt_tr sub_correct sub_ct (fun e => hg (by rw [e]; decide)))
    (fun _ _ ⟨h, ⟨r1, r2⟩, r3, r4⟩ => ⟨AccH.of h.1 hc r1 r2, AccH.of h.2.1 hc r3 r4, h.eq (accChk_in hc).1,
      h.eq (accChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

/-! ## `MultiplyNTTs` -/

theorem mulChk_in {bs wbs : List (Reg × Nat)} {h f g : Ptr} (hc : mulChk bs wbs h f g = true) :
    inB bs h 1024 = true ∧ inB bs f 1024 = true ∧ inB bs g 1024 = true ∧ inB bs (sc oSS) 1024 = true := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4⟩

theorem mulAt_okL {s : State} (L : Lay rbs wbs s) {h f g : Ptr} (hf : NA f) (hg : NA g)
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAt h f g) s fun s' => PPost s s' [(h, 1024), (sc oSS, 1024)] ∧
      PolyIs s'.mem (pa s h) (multiplyNTTs (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  mulAt_ok hf hg (MulH.of L hc rf rg)

theorem mulAt_trL {h f g : Ptr} (hf : NA f) (hg : NA g) (hc : mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAt h f g) fun _ _ => True :=
  RelCT.mono (mulAt_tr hf hg) (fun _ _ ⟨e, ⟨r1, r2⟩, r3, r4⟩ => ⟨MulH.of e.1 hc r1 r2, MulH.of e.2.1 hc r3 r4,
    e.eq (mulChk_in hc).1, e.eq (mulChk_in hc).2.1, e.eq (mulChk_in hc).2.2.1, e.eq (mulChk_in hc).2.2.2,
    e.2.2.2⟩) fun _ _ _ => trivial

/-! ## Two pointers: `SamplePolyCBD₂`, `ByteEncode₁₂`, `ByteDecode₁₂` and the compressions -/

theorem twoChk_in {bs wbs : List (Reg × Nat)} {p q : Ptr} {n m : Nat} (hc : twoChk bs wbs p n q m = true) :
    inB bs p n = true ∧ inB bs q m = true := by
  simp only [twoChk, Bool.and_eq_true] at hc; exact ⟨rdOk_in hc.1.1, wrOk_in hc.1.2⟩

theorem cbd2At_okL {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 128 q 1024 = true) :
    WP isa (cbd2At p q) s fun s' => PPost s s' [(q, 1024)] ∧
      PolyIs s'.mem (pa s q) (samplePolyCBD 2 (bytesAt s.mem (pa s p) 128)) :=
  cbd2At_ok hq (TwoH.of L hc)

theorem cbd2At_trL {p q : Ptr} (hq : NA q) (hc : twoChk (rbs ++ wbs) wbs p 128 q 1024 = true) :
    RelCT isa (LRel rbs wbs) (cbd2At p q) fun _ _ => True :=
  RelCT.mono (cbd2At_tr hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem enc12At_okL {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 1024 q 384 = true) (red : Reduced s.mem (pa s p)) :
    WP isa (enc12At p q) s fun s' => PPost s s' [(q, 384)] ∧
      bytesAt s'.mem (pa s q) 384 = encode12 (polyAt s.mem (pa s p)) :=
  enc12At_ok hq (TwoH.of L hc) red

theorem enc12At_trL {p q : Ptr} (hq : NA q) (hc : twoChk (rbs ++ wbs) wbs p 1024 q 384 = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x p) ∧ Reduced y.mem (pa y p)) (enc12At p q)
      fun _ _ => True :=
  RelCT.mono (enc12At_tr hq) (fun _ _ ⟨e, r1, r2⟩ => ⟨⟨TwoH.of e.1 hc, r1⟩, ⟨TwoH.of e.2.1 hc, r2⟩,
    e.eq (twoChk_in hc).1, e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem dec12At_okL {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 384 q 1024 = true) :
    WP isa (dec12At p q) s fun s' => PPost s s' [(q, 1024)] ∧
      PolyIs s'.mem (pa s q) (decode12 (bytesAt s.mem (pa s p) 384)) :=
  dec12At_ok hq (TwoH.of L hc)

theorem dec12At_trL {p q : Ptr} (hq : NA q) (hc : twoChk (rbs ++ wbs) wbs p 384 q 1024 = true) :
    RelCT isa (LRel rbs wbs) (dec12At p q) fun _ _ => True :=
  RelCT.mono (dec12At_tr hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem ceAt_okL {s : State} (L : Lay rbs wbs s) {f out : Ptr} {d : Nat} (hout : NA out)
    (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ compressWidths)
    (red : Reduced s.mem (pa s f)) :
    WP isa (ceAt f d out) s fun s' => PPost s s' [(out, 32 * d)] ∧
      bytesAt s'.mem (pa s out) (32 * d) = compressEncode d (polyAt s.mem (pa s f)) :=
  ceAt_ok hout (CEH.of L hc hd red)

theorem ceAt_trL {f out : Ptr} {d : Nat} (hout : NA out) (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true)
    (hd : d ∈ compressWidths) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (ceAt f d out)
      fun _ _ => True :=
  RelCT.mono (ceAt_tr hout) (fun _ _ ⟨e, r1, r2⟩ => ⟨CEH.of e.1 hc hd r1, CEH.of e.2.1 hc hd r2,
    e.eq (twoChk_in hc).1, e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem ddAt_okL {s : State} (L : Lay rbs wbs s) {b f : Ptr} {d : Nat} (hf : NA f)
    (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ compressWidths) :
    WP isa (ddAt b d f) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (decodeDecompress d (bytesAt s.mem (pa s b) (32 * d))) :=
  ddAt_ok hf (DDH.of L hc hd)

theorem ddAt_trL {b f : Ptr} {d : Nat} (hf : NA f) (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true)
    (hd : d ∈ compressWidths) :
    RelCT isa (LRel rbs wbs) (ddAt b d f) fun _ _ => True :=
  RelCT.mono (ddAt_tr hf) (fun _ _ e => ⟨DDH.of e.1 hc hd, DDH.of e.2.1 hc hd, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

/-! ## `SampleNTT` -/

theorem sampChk_in {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : sampChk bs wbs a = true) :
    inB bs (sc oSB) 34 = true ∧ inB bs a 1024 = true := by
  simp only [sampChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨rdOk_in h1, wrOk_in h2⟩

theorem sampleAt_trL {a : Ptr} (hna : NA a) (hc : sampChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34)
      (sampleAt a) fun _ _ => True :=
  RelCT.mono (sampleAt_tr hna) (fun _ _ ⟨e, hb⟩ => ⟨SampH.of e.1 hc, SampH.of e.2.1 hc,
    e.eq (sampChk_in hc).1, e.eq (sampChk_in hc).2, e.2.2.2, hb⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64
